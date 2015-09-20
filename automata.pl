:- module('automata',
          [match_regex/2        % :Pred, +Regex, +String
           ]).

user:file_search_path(automata, './automata').

/** <module> High-level predicates for dealing with regular expressions

This module defines predicates for searching and replacing in strings
using regular expressions.

@see	https://github.com/wvxvw/intro-to-automata-theory
@tbd	Add match_suffix_regex/3, match_all_regex/3, find_regex/3
*/

:- meta_predicate
       match_regex(+, +).

:- use_module(automata(convert)).
:- use_module(library(pldoc)).

step(From, Input, Transitions, Trn) :-
    findall(T, (member(T, Transitions),
                trn_input(T, Input),
                trn_from(T, From)),
            [Trn | _]).

match_regex_helper([], _, Trn) :- !, trn_acc(Trn, true).
match_regex_helper([S | Ss], Diagram, Trn) :-
    char_code(C, S),
    trn_to(Trn, To),
    step(To, C, Diagram, Next),
    match_regex_helper(Ss, Diagram, Next).

%%	match_regex(+Regex, +String) is det.
%
%	Evaluates to true if String is accepted by Regex.
%
%	@see	match_suffix_regex/3, match_all_regex/3, find_regex/3

match_regex(Regex, [S | String]) :-
    regex_to_nfa(Regex, Nfa),
    nfa_to_dfa(Nfa, Dfa),
    table_to_diagram(Dfa, UnsortedDiagram),
    sort(1, @=<, UnsortedDiagram, Diagram),
    Diagram = [First | _],
    trn_from(First, F),
    char_code(C, S),
    findall(T, (member(T, Diagram),
                trn_from(T, F),
                trn_input(T, C)),
            [Trn | _]),
    match_regex_helper(String, Diagram, Trn).
