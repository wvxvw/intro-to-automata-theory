:- module('automata/convert',
          [regex_to_nfa/2,
           table_to_diagram/2,
           nfa_inputs/2,
           nfa_states/2,
           nfa_table/2,
           nfa_to_dfa/2,
           reacheable_states/4,
           has/3,
           trn_from/2,
           trn_to/2,
           trn_input/2,
           trn_acc/2
           ]).

:- meta_predicate
       regex_to_nfa(+, -),
       table_to_diagram(+, -),
       nfa_inputs(+, -),
       nfa_states(+, -),
       nfa_table(+, -),
       nfa_to_dfa(+, -),
       reacheable_states(+, +, +, -),
       has(+, ?, ?),
       trn_from(+, -),
       trn_to(+, -),
       trn_input(+, -),
       trn_acc(+, -).

:- dynamic trn_from/2, trn_to/2, trn_input/2, trn_acc/2.

/** <module> Convert between different automata represenations

This module defines defines conversions between regular expression
AST, DFA represented as a list of transitions or as a table, and NFA
represented similarly to DFA.

This module also defines data types:
    * Transition record
      ==
      trn(from:integer, to:integer, input:input, acc:boolean)
      ==
      To describe a single transition between states on some input.
      =acc= is =true= whenever the target state is an accepting one.
    * State record
      ==
      state(label, acc:boolean)
      ==
      To describe states.
    * Transition table row record
      ==
      row(state:state, trns:trns)
      ==
      To describe all inputs for a given state.
    * Transition table record
      ==
      table(inputs:list(input), tab:list(row))
      ==
      To describe a complete table of transitions between all states
      of some automata.

@see    https://github.com/wvxvw/intro-to-automata-theory
*/

:- use_module('automata/parser').
:- use_module(library(record)).
:- use_module(library(error)).
:- use_module(library(pairs)).
:- use_module(library(clpfd)).
:- use_module(library(assoc)).

error:has_type(state, X) :- default_state(X).
error:has_type(trn, X) :- default_trn(X).
error:has_type(input, X) :- X = [] ; atom(X).
error:has_type(trns, X) :-
    foreach(member(E, X), error:must_be(list(integer), E)).
error:has_type(row, X) :- default_row(X).

:- record trn(from:integer, to:integer, input:input, acc:boolean).
:- record state(label, acc:boolean).
:- record row(state:state, trns:trns).
:- record table(inputs:list(input), tab:list(row)).

%%  has(+Accessor, ?Value, ?Record) is det.
%
%   Flips arguments for Accessr (the predicate generated to access
%   fields of the record).

has(Accessor, Value, Record) :- call(Accessor, Record, Value).

vre_to_nfa_helper(rterminal(X), From, To, [trn(From, To, X, Final)], P, P) :-
    ( To = 1 -> Final = true ; Final = false ).
vre_to_nfa_helper(rconcat(L, R), From, To, Diagram, Prev, Next) :-
    Next1 is Prev + 1,
    vre_to_nfa_helper(L, From, Prev, Left, Next1, Next2),
    vre_to_nfa_helper(R, Prev, To, Right, Next2, Next),
    append(Left, Right, Diagram).
vre_to_nfa_helper(runion(L, R), From, To, Diagram, Prev, Next) :-
    vre_to_nfa_helper(L, From, To, Left, Prev, Next1),
    vre_to_nfa_helper(R, From, To, Right, Next1, Next),
    append(Left, Right, Diagram).
vre_to_nfa_helper(rstar(X), From, To, Diagram, Prev, Next) :-
    MidRight is Prev + 1,
    Next0 is MidRight + 1,
    vre_to_nfa_helper(rterminal([]), From, Prev, Left, Next0, Next1),
    vre_to_nfa_helper(rterminal([]), From, To, Long, Next0, Next1),
    vre_to_nfa_helper(rterminal([]), MidRight, To, Right, Next1, Next2),
    vre_to_nfa_helper(rterminal([]), MidRight, Prev, Back, Next2, Next3),
    vre_to_nfa_helper(X, Prev, MidRight, Forward, Next3, Next),
    append([Left, Long, Right, Back, Forward], Diagram).
vregex_to_nfa(Regex, Diagram) :-
    vre_to_nfa_helper(Regex, 0, 1, Diagram, 2, _).

%%  regex_to_nfa(+Regex, -Nfa) is det.
%
%   Evaluates to true when given regular expression Regex can be
%   decomposed into a list of transitions Nfa.
%
%   @see    gexps/3

regex_to_nfa(Regex, Diagram) :-
    phrase(gexps(Parsed), Regex),
    %% format('Parsed = ~w~n', [Parsed]),
    vregex_to_nfa(Parsed, Diagram).

nfa_inputs_helper([], X, X).
nfa_inputs_helper([trn(_, _, X, _) | Diagram], Acc, Inputs) :-
    (
        member(X, Acc) ->
            nfa_inputs_helper(Diagram, Acc, Inputs) ;
        nfa_inputs_helper(Diagram, [X | Acc], Inputs)
    ).

%%  nfa_inputs(+Nfa, -Inputs) is det.
%
%   Evaluates to true when Inputs is the alphabet of the Nfa automata.

nfa_inputs(Diagram, Inputs) :-
    nfa_inputs_helper(Diagram, [], Inputs).

accepting(N, Diagram, true) :-
    include(has(trn_to, N), Diagram, [trn(_, _, _, true) | _]), !.
accepting(_, _, false).

nfa_states_helper([], _, X, X).
nfa_states_helper([trn(From, To, _, _) | Diagram], Transitions, Acc, States) :-
    accepting(From, Transitions, FromAcc),
    accepting(To, Transitions, ToAcc),
    (
        member(state(From, FromAcc), Acc) ->
            (
                member(state(To, ToAcc), Acc) ->
                    nfa_states_helper(Diagram, Transitions, Acc, States)
             ;
             nfa_states_helper(
                     Diagram, Transitions, [state(To, ToAcc) | Acc], States)
            )
     ;
     (
         member(state(To, ToAcc), Acc) ->
             nfa_states_helper(
                     Diagram, Transitions, [state(From, FromAcc) | Acc], States)
      ;
      nfa_states_helper(
              Diagram,
              Transitions,
              [state(From, FromAcc), state(To, ToAcc) | Acc],
              States)
     )
    ).

%%  nfa_states(+Nfa, -States) is det.
%
%   Evaluates to true when States is the states of the Nfa automata.

nfa_states(Diagram, States) :-
    nfa_states_helper(Diagram, Diagram, [], States).

nfa_state(table(_, Table), N, State) :-
    findall(S, (member(Row, Table),
                row_state(Row, S),
                state_label(S, N)),
            [State | _]).
nfa_state(Diagram, state(N, _), State) :-
    include(has(trn_from, N), Diagram, State).

nfa_nth_state(N, [state(N, _), _]).

reacheable_states_helper([], All, _, All).
reacheable_states_helper(NextGen, Cache, Table, All) :-
    NextGen \== [],
    append(NextGen, Cache, NewCache),
    reacheable_states_rec(NextGen, Table, NewCache, All).

reacheable_states_rec(Previous, Table, Cached, All) :-
    findall(Trans,
            (member(T, Previous),
             member([state(T, _), Ts], Table),
             nfa_nth_state(T, [_, Ts]),
             include(has(trn_input, []), Ts, AllTrans),
             findall(X, (member(M, AllTrans), trn_to(M, X)), AllStates),
             ord_subtract(AllStates, Cached, Trans)),
            ResultTree),
    flatten(ResultTree, Result),
    reacheable_states_helper(Result, Cached, Table, All).

%%  reacheable_states(+Input, +Transitions, +Table, -States) is det.
%
%   Evaluates to true when States can be reached from all Transitions
%   on given Input.  This also accounts for epsilon transitions.

reacheable_states([], [Tr | Trans], Table, Result) :-
    include(has(trn_input, []), [Tr | Trans], Dest),
    trn_from(Tr, Self),
    findall(X, (member(T, Dest), trn_to(T, X)), Dests),
    union(Dests, [Self], Cache),
    reacheable_states_rec(Dests, Table, Cache, Result).
reacheable_states(Input, Trans, _, Result) :-
    Input \== [],
    include(has(trn_input, Input), Trans, Dest),
    findall(X, (member(T, Dest), trn_to(T, X)), Result).

ensure_state(state(N, _), [], [], _, [N]).
ensure_state(_, Input, State, All, Cell) :-
     reacheable_states(Input, State, All, Cell).

nfa_table_helper([], _, _, X, X).
nfa_table_helper([[N, State] | States], All, Inputs, Acc, Table) :-
    findall(X, (member(Y, Inputs), ensure_state(N, Y, State, All, X)), Row),
    nfa_table_helper(States, All, Inputs, [row(N, Row) | Acc], Table).

%%  nfa_table(+Transitions, -Table:table) is det.
%
%   Evaluates to true when Table is the transitions table containing
%   all transitions given by Transitions.

nfa_table(Diagram, table(Inputs, Table)) :-
    nfa_inputs(Diagram, Inputs),
    nfa_states(Diagram, States),
    findall([X, Y], (member(X, States), nfa_state(Diagram, X, Y)), StatesL),
    nfa_table_helper(StatesL, StatesL, Inputs, [], UnsortedTable),
    sort(1, @<, UnsortedTable, Table).

states_for_input(Input, Inputs, Row, States) :-
    nth0(Index, Inputs, Input),
    nth0(Index, Row, States).

nth_row_accepts(Table, N) :-
    member(row(state(N, true), _), Table).

reacheable_epsilon(From, Input, table(Inputs, Table),
                   state(States, Accepting)) :-
    findall(X, (member(row(state(From, _), Row), Table),
                states_for_input(Input, Inputs, Row, X)),
            StatesTree),
    flatten(StatesTree, Prefix),
    findall(Y, (member(P, Prefix),
                member(row(state(P, _), Row1), Table),
                states_for_input([], Inputs, Row1, Y)),
            StatesRawTree),
    flatten(StatesRawTree, StatesUnsorted),
    sort(StatesUnsorted, States),
    include(nth_row_accepts(Table), States, Final),
    ( Final = [] -> Accepting = false ; Accepting = true ).

merge_states(state(Y, _), X, Z) :- append(X, Y, Z).

nfa_to_dfa_helper(_, _, [], Dfa-Dfa).
nfa_to_dfa_helper(table(Inputs, Table), Cache,
                  [state(T, A) | Todo], Dfa-Afd) :-
    exclude('='([]), Inputs, In),
    findall(X,
            (member(I, In),
             findall(Y,
                     (member(From, T),
                      reacheable_epsilon(From, I, table(Inputs, Table), Y)),
                     Xs),
             flatten(Xs, X)),
            Dest),
    findall(Z, (member(D, Dest),
                foldl(merge_states, D, [], Z)),
            Row),
    flatten(Dest, FlatDest),
    ord_subtract(FlatDest, Cache, CleanDest),
    append(CleanDest, Cache, NewCache),
    append(CleanDest, Todo, NewTodo),
    make_state([label(T), acc(A)], S),
    make_row([state(S), trns(Row)], R),
    nfa_to_dfa_helper(table(Inputs, Table), NewCache, NewTodo, Dfa-[R | Afd]).

enum(States, Assoc) :-
    length(States, Len),
    L is Len - 1,
    findall(N, between(0, L, N), NList),
    pairs_keys_values(Paired, States, NList),
    ord_list_to_assoc(Paired, Assoc).

replace_trns([], _, []).
replace_trns([[] | Trns], Numerated, [[] | NewTrns]) :-
    replace_trns(Trns, Numerated, NewTrns).
replace_trns([T | Trns], Numerated, [[Nt] | NewTrns]) :-
    get_assoc(T, Numerated, Nt),
    replace_trns(Trns, Numerated, NewTrns).

normalized_table(table(I, Denorm), table(I, Norm)) :-
    findall(Row, (member(Row, Denorm),
                  row_state(Row, St),
                  state_label(St, L),
                  L \== []),
            Rows),
    findall(L, (member(R, Rows),
                row_state(R, St),
                state_label(St, L)), States),
    enum(States, Numerated),
    findall(Row, (member(R, Rows),
                  row_state(R, St),
                  row_trns(R, Trns),
                  state_label(St, L),
                  state_acc(St, Acc),
                  get_assoc(L, Numerated, NewL),
                  replace_trns(Trns, Numerated, NewTrns),
                  make_state([label(NewL), acc(Acc)], NewSt),
                  make_row([state(NewSt), trns(NewTrns)], Row)),
            Norm).

%%  nfa_to_dfa(+Nfa, -Dfa) is det.
%
%   Evaluates to true when Dfa accepts the same language as Nfa.

nfa_to_dfa(Nfa, table(In, DfaTable)) :-
    nfa_table(Nfa, table(Inputs, Table)),
    nfa_to_dfa_helper(table(Inputs, Table), [], [state([0], false)], UnsortedDfa-[]),
    sort([1, 1], @<, UnsortedDfa, SortedDfa),
    normalized_table(table(Inputs, SortedDfa), table(Inputs, DfaTable)),
    exclude('='([]), Inputs, In).

%%  table_to_diagram(+Table, -Diagram) is det.
%
%   Evaluates to true when Diagram contains all the transitions
%   described in Table.

table_to_diagram(table(Input, Table), Diagram) :-
    findall(Trn, (member(Row, Table),
                  row_state(Row, St),
                  row_trns(Row, Trns),
                  state_label(St, Label),
                  pairs_keys_values(Paired, Trns, Input),
                  member(Ts-I, Paired),
                  member(T, Ts),
                  nfa_state(table(Input, Table), T, To),
                  state_acc(To, A),
                  make_trn([from(Label), to(T), input(I), acc(A)], Trn)),
            Diagram).
