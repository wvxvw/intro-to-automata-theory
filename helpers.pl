:- doc_server(4000).    % Start PlDoc at port 4000
:- portray_text(true).  % Enable portray of strings
%% :- use_module(library(pldoc/doc_library)).

:- use_module(library(lists)).
:- use_module(automata).
:- use_module(automata(convert)).
:- use_module(automata(printing)).

%% :- doc_load_library.
:- doc_collect(true).

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

test_match :-
    match_regex(`x(y+x)*+z`, `xyyxxxyxxy`).
