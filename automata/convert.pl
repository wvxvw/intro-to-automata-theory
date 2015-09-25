:- module('automata/convert',
          [regex_to_nfa/2,
           dfa_to_regex/2,
           dfa_minimize/2,
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
           trn_acc/2,
           make_row/2,
           make_state/2,
           make_table/2,
           row_state/2,
           row_trns/2,
           state_acc/2,
           state_label/2
           ]).

:- meta_predicate
       regex_to_nfa(+, -),
       dfa_to_regex(+, -),
       dfa_minimize(+, -),
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
       trn_acc(+, -),
       make_row(+, -),
       make_state(+, -),
       make_table(+, -),
       row_state(+, -),
       row_trns(+, -),
       state_acc(+, -),
       state_label(+, -).

:- dynamic trn_from/2, trn_to/2, trn_input/2, trn_acc/2, make_row/2,
           make_state/2, make_table/2, row_state/2, row_trns/2,
           state_acc/2, state_label/2.

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
:- use_module('automata/ast').
:- use_module('automata/printing').
:- use_module('automata/utils').
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
    numlist(0, L, NList),
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

nfa_to_dfa(Nfa, MinDfaTable) :-
    nfa_table(Nfa, table(Inputs, Table)),
    nfa_to_dfa_helper(table(Inputs, Table), [], [state([0], false)], UnsortedDfa-[]),
    sort([1, 1], @<, UnsortedDfa, SortedDfa),
    normalized_table(table(Inputs, SortedDfa), table(Inputs, DfaTable)),
    exclude('='([]), Inputs, In),
    dfa_minimize(table(In, DfaTable), MinDfaTable).

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

maybe_union(Re, [], [Re]).
maybe_union(Re, [Re | Rest], [Re | Rest]).
maybe_union(Re1-[N], [Re2-[N] | Rest], [runion(Re1, Re2)-[N] | Rest]).
maybe_union(Re1, [Re2 | Rest], [runion(Re1, Re2) | Rest]) :-
    regex(Re1), regex(Re2).
maybe_union(Re1, [Re2 | Rest], [Re1, Re2 | Rest]).

normalize_rule(Rule, Normalized) :-
    sort(0, @<, Rule, Sorted),
    foldl(maybe_union, Sorted, [], Normalized).

find_rule(N, Rules, Rule) :-
    member(state(N, _)-Tail, Rules),
    member(Rule, Tail).

reduce_rule(State-Rule, RulesIn, RulesOut) :-
    state_label(State, N),
    normalize_rule(Rule, NormRule),
    findall(Rex, (member(Rl, NormRule),
                  (
                      Rl = R-[M] ->
                          (
                              N = M -> Rex = rstar(R)
                           ;
                           find_rule(M, RulesIn, Expansion),
                           (
                               regex(Expansion) ->
                                   (
                                       Expansion = rterminal([]) -> Rex = R
                                    ;
                                    Rex = rconcat(R, Expansion)
                                   )
                            ;
                            Head-Tail = Expansion,
                            Rex = rconcat(R, Head)-Tail
                           )
                          )
                   ;
                   Rex = Rl
                  )),
            NewRule),
    select(State-Rule, RulesIn, State-NewRule, RulesOut).

dead(_-[]).

reduce_rules_helper([], X, X).
reduce_rules_helper([R | Rest], Rules, Interim) :-
    reduce_rule(R, Rules, NewRules),
    reduce_rules_helper(Rest, NewRules, Interim).

reduce_rules(Rules, Reduced) :-
    [_-R | _] = Rules,
    (
        (length(R, 1), [Rex] = R, regex(Rex)) ->
            Reduced = Rules
     ;
     reduce_rules_helper(Rules, Rules, Interim),
     reduce_rules(Interim, Reduced)
    ).

%%  dfa_to_regex(+Dfa, -Regex) is det.
%
%   Evaluates to true when Regex accepts the same language as the
%   given Dfa.  Dfa could be either a transitions table or a list of
%   all transitions.

dfa_to_regex(table(Input, Table), Regex) :-
    findall(I, (member(In, Input), I = rterminal(In)), Terminals),
    findall(R, (member(Row, Table),
                row_state(Row, S),
                row_trns(Row, Trns),
                pairs_keys_values(Paired, Terminals, Trns),
                exclude(dead, Paired, Filtered),
                (
                    state_acc(S, true) -> Tail = [rterminal([]) | Filtered]
                 ;
                 Tail = Filtered
                ),
                R = S-Tail),
            Rules),
    reduce_rules(Rules, Reduced), !,
    Reduced = [_-[Re | _] | _],
    regex_to_string(Re, Regex).
    
dfa_to_regex(Dfa, Regex) :-
    is_list(Dfa),
    nfa_table(Dfa, Table),
    dfa_to_regex(Table, Regex).

row_accepts(Row) :-
    row_state(Row, State),
    state_acc(State, true).

cmp_trns([X | Xs], [Y | Ys], Result) :-
    cmp_lists(X, Y, Res),
    (
        Res = '=' -> cmp_trns(Xs, Ys, Result)
     ;
     Result = Res
    ).

cmp_rows(Row1, Row2, '=') :-
    row_trns(Row1, Trns),
    row_trns(Row2, Trns).

cmp_rows(Row1, Row2, Result) :-
    row_trns(Row1, Trns1),
    row_trns(Row2, Trns2),
    cmp_trns(Trns1, Trns2, Result).

classify_rows_helper([], Classes, [], [Classes]).
classify_rows_helper(Less, Equal, [], Classes) :-
    Less \== [],
    classify_rows(Less, Classes1),
    classify_rows(Equal, Classes2),
    append(Classes1, Classes2, Classes).
classify_rows_helper([], Equal, Greater, Classes) :-
    Greater \== [],
    classify_rows(Greater, Classes1),
    classify_rows(Equal, Classes2),
    append(Classes1, Classes2, Classes).
classify_rows_helper(Less, Equal, Greater, Classes) :-
    Less \== [], Greater \== [], 
    classify_rows(Less, Classes1),
    classify_rows(Equal, Classes2),
    classify_rows(Greater, Classes3),
    append([Classes1, Classes2, Classes3], Classes).

classify_rows([T | Trns], Classes) :-
    partition(cmp_rows(T), Trns, Less, Equal, Greater),
    classify_rows_helper(Less, [T | Equal], Greater, Classes).

replace_trns(L, Labels, OldRow, NewRow) :-
    row_state(OldRow, S),
    row_trns(OldRow, Ts),
    findall(X, (member(T, Ts),
                replace_all_tree_lift(L, Labels, T, X)),
            NewTrns),
    make_row([state(S), trns(NewTrns)], NewRow).

relabel([], Out, Out).
relabel([[_] | States], AccStates, Out) :-
    relabel(States, AccStates, Out).
relabel([[Row1, Row2 | Rows] | States], AccStates, Out) :-
    row_state(Row1, S),
    state_label(S, L),
    findall(X, (member(R, [Row2, Rows]),
                row_state(R, St),
                state_label(St, X)),
            Labels),
    findall(NewA, (member([A | _], AccStates),
                   replace_trns(L, Labels, A, NewA)),
            NewAccStates),
    relabel(States, NewAccStates, Out).

%%  dfa_minimize(+Dfa, -Minimized) is det.
%
%   Evaluates to true when Minimized is the minimal DFA of Dfa.

dfa_minimize(table(Inputs, Dfa), Minimized) :-
    partition(row_accepts, Dfa, Accepting, Rejecting),
    classify_rows(Accepting, AClasses),
    classify_rows(Rejecting, RClasses),
    append(AClasses, RClasses, Classes),
    relabel(Classes, Classes, Relabeled),
    sort([1, 1], @<, Relabeled, Sorted),
    make_table([inputs(Inputs), tab(Sorted)], Minimized).
