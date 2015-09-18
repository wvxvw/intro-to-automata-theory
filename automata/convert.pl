:- module('automata/convert',
          [vregex_to_nfa/2,
           regex_to_nfa/2,
           nfa_inputs/2,
           nfa_states/2,
           nfa_state/3,
           nfa_state_input/4,
           nfa_table/2
           ]).

:- meta_predicate
       vregex_to_nfa(+, -),
       regex_to_nfa(+, -),
       nfa_inputs(+, -),
       nfa_states(+, -),
       nfa_state(+, +, -),
       nfa_state_input(+, +, +, -),
       nfa_table(+, -).

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
    vre_to_nfa_helper(rterminal([]), To, Prev, Back, Next2, Next3),
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
    ( member(X, Acc) ->
          nfa_inputs_helper(Diagram, Acc, Inputs) ;
      nfa_inputs_helper(Diagram, [X | Acc], Inputs) ).
nfa_inputs(Diagram, Inputs) :-
    nfa_inputs_helper(Diagram, [], Inputs).

nfa_states_helper([], X, X).
nfa_states_helper([trn(From, To, _, _) | Diagram], Acc, States) :-
    ( member(From, Acc) ->
          ( member(To, Acc) ->
                nfa_states_helper(Diagram, Acc, States) ;
            nfa_states_helper(Diagram, [To | Acc], States) ) ;
      ( member(To, Acc) ->
            nfa_states_helper(Diagram, [From | Acc], States) ;
        nfa_states_helper(Diagram, [From, To | Acc], States) ) ).
nfa_states(Diagram, States) :-
    nfa_states_helper(Diagram, [], States).

nfa_state_n(N, trn(N, _, _, _)).

nfa_state(Diagram, N, State) :-
    include(nfa_state_n(N), Diagram, State).

nfa_nth_state(N, [N, _]).

nfa_state_input_cached(State, States, Result, Cache) :-
    findall(To, (member(S, State), nfa_state_to([], To, S, States)), Interim),
    ord_subtract(Interim, Cache, Res),
    ( Res = [] -> Result = Cache ;
      flatten(Res, Res1),
      append(Interim, Res1, Cache1),
      findall(X, (member(R, Res1), member([R, X], States)), Filtered),
      findall(Y, (member(F, Filtered), 
                  nfa_state_input_cached(F, States, Y, Cache1)), Res2),
      append(Cache, Res2, Result) ).

nfa_state_to([], To, trn(From, To1, [], _), States) :-
    include(nfa_nth_state(To1), States, State),
    [[_, Row]] = State,
    nfa_state_input_cached(Row, States, To, [From, To1]).
nfa_state_to(Input, To, trn(_, To, Input, _), _) :- atom(Input).

nfa_state_input(Input, State, States, Result) :-
    findall(To, (member(S, State), nfa_state_to(Input, To, S, States)), Interim),
    flatten(Interim, Inter1),
    list_to_set(Inter1, Inter2),
    ( Inter2 = [] ->
          ( Input = [] ->
                [trn(N, _, _, _), _] = State, Result = [N] ;
            Result = [e] ) ;
      Result = Inter2 ).

nfa_table_helper([], _, _, X, X).
nfa_table_helper([[N, State] | States], All, Inputs, Acc, Table) :-
    findall(X, (member(Y, Inputs), nfa_state_input(Y, State, All, X)), Row),
    nfa_table_helper(States, All, Inputs, [row(N, Row) | Acc], Table).
nfa_table(Diagram, table(Inputs, Table)) :-
    nfa_inputs(Diagram, Inputs),
    nfa_states(Diagram, States),
    findall([X, Y], (member(X, States), nfa_state(Diagram, X, Y)), StatesL),
    nfa_table_helper(StatesL, StatesL, Inputs, [], Table).

nfa_to_dfa_row(Row, Inputs, Result). % TODO

nfa_to_dfa_helper(_, _, [], Dfa, Dfa).
nfa_to_dfa_helper(Inputs, Table, [state(N, Accepting) | Todo], Acc, Dfa) :-
    include(nfa_nth_state(N), Table, Filtered),
    [_, [Row]] = Filtered,
    nfa_to_dfa_row(Row, Inputs, Result),
    ord_subtract(Acc, Result, New),
    ( New = [] -> nfa_to_dfa_helper(Inputs, Table, Todo, Acc, Dfa) ;
      append(New, Todo, Next),
      nfa_to_dfa_helper(Inputs, Table, Next, Acc, Dfa) ).

nfa_to_dfa(Nfa, Dfa) :-
    nfa_table(Nfa, table(Inputs, Table)),
    nfa_to_dfa_helper(Inputs, Table, [state(1, false)], [], Dfa).
