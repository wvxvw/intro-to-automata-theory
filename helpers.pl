:- use_module(library(lists)).
:- use_module(automata).

concatentated_member(L1, L2, L3) :-
    member(M1, L1), member(M2, L2),
    string_concat(M1, M2, L3).

concatentated(L1, L2, L3) :-
    findall(X, concatentated_member(L1, L2, X), X),
    list_to_set(X, L3).

test_automata :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_table(X, Y),
    format_table(Y).
