:- module('automata/convert',
          [vregex_to_nfa/2,
           regex_to_nfa/2,
           nfa_inputs/2,
           nfa_states/2,
           nfa_state/3,
           reacheable_states/4,
           nfa_table/2,
           nfa_to_dfa/2
           ]).

:- meta_predicate
       vregex_to_nfa(+, -),
       regex_to_nfa(+, -),
       nfa_inputs(+, -),
       nfa_states(+, -),
       nfa_state(+, +, -),
       reacheable_states(+, +, +, -),
       nfa_table(+, -),
       nfa_to_dfa(+, -).

:- use_module('automata/parser').

%%
%% regular expression to NFA conversion
%% 

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
nfa_inputs(Diagram, Inputs) :-
    nfa_inputs_helper(Diagram, [], Inputs).

transition_from(From, trn(From, _, _, _)).
transition_to(To, trn(_, To, _, _)).
transition_input(Input, trn(_, _, Input, _)).
transition_accept(Accept, trn(_, _, _, Accept)).

accepting(N, Diagram, true) :-
    include(transition_to(N), Diagram, [trn(_, _, _, true) | _]), !.
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
nfa_states(Diagram, States) :-
    nfa_states_helper(Diagram, Diagram, [], States).

nfa_state(Diagram, state(N, _), State) :-
    include(transition_from(N), Diagram, State).

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
             include(transition_input([]), Ts, AllTrans),
             findall(X,
                     (member(M, AllTrans), transition_to(X, M)),
                     AllStates),
             ord_subtract(AllStates, Cached, Trans)),
            ResultTree),
    flatten(ResultTree, Result),
    reacheable_states_helper(Result, Cached, Table, All).

reacheable_states([], [Tr | Trans], Table, Result) :-
    include(transition_input([]), [Tr | Trans], Dest),
    transition_from(Self, Tr),
    findall(X, (member(T, Dest), transition_to(X, T)), Dests),
    union(Dests, [Self], Cache),
    reacheable_states_rec(Dests, Table, Cache, Result).
reacheable_states(Input, Trans, _, Result) :-
    Input \== [],
    include(transition_input(Input), Trans, Dest),
    findall(X, (member(T, Dest), transition_to(X, T)), Result).

ensure_state(state(N, _), [], [], _, [N]).
ensure_state(_, Input, State, All, Cell) :-
     reacheable_states(Input, State, All, Cell).

nfa_table_helper([], _, _, X, X).
nfa_table_helper([[N, State] | States], All, Inputs, Acc, Table) :-
    findall(X, (member(Y, Inputs), ensure_state(N, Y, State, All, X)), Row),
    nfa_table_helper(States, All, Inputs, [row(N, Row) | Acc], Table).
nfa_table(Diagram, table(Inputs, Table)) :-
    nfa_inputs(Diagram, Inputs),
    nfa_states(Diagram, States),
    findall([X, Y], (member(X, States), nfa_state(Diagram, X, Y)), StatesL),
    nfa_table_helper(StatesL, StatesL, Inputs, [], UnsortedTable),
    sort(1, @<, UnsortedTable, Table).

%%
%% NFA -> DFA
%% 

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
    nfa_to_dfa_helper(table(Inputs, Table),
                      NewCache, NewTodo, Dfa-[row(state(T, A), Row) | Afd]).

nfa_to_dfa(Nfa, table(In, DfaTable)) :-
    nfa_table(Nfa, table(Inputs, Table)),
    nfa_to_dfa_helper(table(Inputs, Table), [], [state([0], false)], UnsortedDfa-[]),
    sort([1, 1], @<, UnsortedDfa, DfaTable),
    exclude('='([]), Inputs, In).
    
