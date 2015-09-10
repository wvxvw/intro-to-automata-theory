:- use_module(library(lists)).

concatentated_member(L1, L2, L3) :-
    member(M1, L1), member(M2, L2),
    string_concat(M1, M2, L3).

concatentated(L1, L2, L3) :-
    findall(X, concatentated_member(L1, L2, X), X),
    list_to_set(X, L3).

rterminal([]).                  % this is epsilon
rterminal(X)  :- atom(X).
runion(X, Y)  :- regex(X), regex(Y).
rstar(X)      :- regex(X).
rconcat(X, Y) :- regex(X), regex(Y).
regex(X)      :- rterminal(X) ;
                 X = runion(Y, Z), regex(Y), regex(Z) ;
                 X = rstar(Y), regex(Y) ;
                 X = rconcat(Y, Z), regex(Y), regex(Z).

gstar_helper(rstar(S), [Y, 42 | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    phrase(gstarred(S), Test),
    Xs = Ys.
gstar_helper(Exp, [Y, Z | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    gstar_helper(Exp, [Z | Ys], Test, Xs).
gstar(rstar(S), [X, 42 | Xs], Xs) :- phrase(gchar(S), [X]).
gstar(Exp, [X, Y | Ys], Xs) :-
    gstar_helper(Exp, [Y | Ys], [X], Xs).

gunion_helper(runion(R, L), [Y, 43 | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    phrase(gexps(R), Test),
    phrase(gexps(L), Ys, Xs).
gunion_helper(Exp, [Y, Z | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    gunion_helper(Exp, [Z | Ys], Test, Xs).
    
gunion(runion(R, L), [X, 43 | Xs], Ys) :-
    phrase(gchar(R), [X]), phrase(gexp(L), Xs, Ys).
gunion(Exp, [X, Y | Ys], Xs) :-
    gunion_helper(Exp, [Y | Ys], [X], Xs).

gchar(rterminal(C), [X | Xs], Xs) :-
    %% Our regex character class is somewhat limited...
    member(X, `abcdefghjklmnopqrstuvwxyzABCDEFGHJKLMNOPQRSTUVWXYZ012345678`),
    char_code(C, X).

gstarred(Node) -->
    gstar(Node) ;
    "(", gexps(Node), ")" ;
    gchar(Node).

gexp(Node) --> gstarred(Node) ; gunion(Node).

gexps(Tree) -->
    gexp(Tree) ;
    gexp(Node), gexps(Rest), { Tree = rconcat(Node, Rest) }.

vexp(rterminal(C))  --> { char_code(C, R) }, [R].
vexp(runion(L, R))  --> "(", vexp(L), "+", vexp(R), ")".
vexp(rstar(E))      --> "(", vexp(E), ")*".
vexp(rconcat(L, R)) --> vexp(L), vexp(R).

regex_to_string(Exp, Result) :-
    phrase(Exp, Codes), text_to_string(Codes, Result).

vre_to_nfa_helper(rterminal(X), From, To, [trn(From, To, X)], P, P).
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
nfa_inputs_helper([trn(_, _, X) | Diagram], Acc, Inputs) :-
    ( member(X, Acc) ->
          nfa_inputs_helper(Diagram, Acc, Inputs) ;
      nfa_inputs_helper(Diagram, [X | Acc], Inputs) ).
nfa_inputs(Diagram, Inputs) :-
    nfa_inputs_helper(Diagram, [], Inputs).

nfa_states_helper([], X, X).
nfa_states_helper([trn(From, To, _) | Diagram], Acc, States) :-
    ( member(From, Acc) ->
          ( member(To, Acc) ->
                nfa_states_helper(Diagram, Acc, States) ;
            nfa_states_helper(Diagram, [To | Acc], States) ) ;
      ( member(To, Acc) ->
            nfa_states_helper(Diagram, [From | Acc], States) ;
        nfa_states_helper(Diagram, [From, To | Acc], States) ) ).
nfa_states(Diagram, States) :-
    nfa_states_helper(Diagram, [], States).

nfa_state_n(N, trn(N, _, _)).

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

nfa_state_to([], To, trn(From, To1, []), States) :-
    include(nfa_nth_state(To1), States, State),
    [[_, Row]] = State,
    nfa_state_input_cached(Row, States, To, [From, To1]).
nfa_state_to(Input, To, trn(_, To, Input), _) :- atom(Input).

nfa_state_input(Input, State, States, Result) :-
    findall(To, (member(S, State), nfa_state_to(Input, To, S, States)), Interim),
    flatten(Interim, Inter1),
    list_to_set(Inter1, Inter2),
    ( Inter2 = [] ->
          ( Input = [] ->
                [trn(N, _, _), _] = State, Result = [N] ;
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

format_table_helper([]).
format_table_helper([row(N, Row) | Table]) :-
    format('~d | ~w |~n', [N, Row]),
    format_table_helper(Table).
format_table(table(Inputs, Table)) :-
    format('~w~n', [Inputs]),
    format_table_helper(Table).
