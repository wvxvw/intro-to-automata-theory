:- doc_server(4000).    % Start PlDoc at port 4000
:- portray_text(true).  % Enable portray of strings

:- use_module(library(lists)).
:- use_module(library(doc_latex)).
:- use_module(automata).
:- use_module(automata(convert)).
:- use_module(automata(printing)).

:- doc_collect(true).

concatentated_member(L1, L2, L3) :-
    member(M1, L1), member(M2, L2),
    string_concat(M1, M2, L3).

concatentated(L1, L2, L3) :-
    findall(X, concatentated_member(L1, L2, X), X),
    list_to_set(X, L3).

test_automata(X) :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_table(X, Y),
    format_table(Y).

test_nfa_to_dfa(Dfa) :-
    regex_to_nfa(`x(y+x)*+z`, Nfa),
    nfa_to_dfa(Nfa, Dfa),
    format_table(Dfa).

test_match :-
    match_regex(`x(y+x)*+z`, `xyyxxxyxxy`).

test_mismatch :-
    match_regex(`x(y+x)*+z`, `xyyxxxyxxyz`).

test_smatch_suffix(Suffix) :-
    match_suffix_regex(`x(y+x)*+z`, `xyyxxxyxxyzab`, Suffix).

test_reacheable_epsilon(States) :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_table(X, Y),
    'automata/convert':reacheable_epsilon(3, x, Y, States).

gen_doc :-
    doc_latex(['automata',
               'automata/ast',
               'automata/convert',
               'automata/parser',
               'automata/printing'],
              'automata-doc.tex',
              [stand_alone(flase),
               section_level(subsection)])
