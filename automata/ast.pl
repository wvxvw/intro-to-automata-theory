:- module('automata/ast',
          [rterminal/1,
           runion/2,
           rstar/1,
           rconcat/2,
           regex/1
          ]).

:- meta_predicate
       rterminal(?),
       runion(+, +),
       rstar(+),
       rconcat(+, +),
       regex(+).

/** <module> Grammar constituents used when parsing regular expressions

This module defines predicates for generating abstract syntax trees
representing regular expressions.

@see    https://github.com/wvxvw/intro-to-automata-theory
*/

%%  rterminal(?Regex) is nondet.
%
%   Evaluates to true if Regex is either an atom or an empty list.
%   Empty list denotes empty string, atoms stand for characters of
%   the strings.
%
%   @see    runion/2, rstar/1, rconcat/2, regex/1

rterminal(X) :- X = [] ; atom(X).

%%  runion(+Regex1, +Regex2) is det.
%
%   Evaluates to true if Regex1 and Regex2 are valid regular expressions
%   as defined in regex/1.
%
%   @see    runion/2, rstar/1, rconcat/2, regex/1

runion(X, Y) :- regex(X), regex(Y).

%%  rstar(+Regex) is det.
%
%   Evaluates to true if Regex is a valid regular expressions
%   as defined in regex/1.
%
%   @see    rterminal/1, rstar/1, rconcat/2, regex/1

rstar(X) :- regex(X).

%%  rconcat(+Regex1, +Regex2) is det.
%
%   Evaluates to true if Regex1 and Regex2 are valid regular expressions
%   as defined in regex/1.
%
%   @see    runion/2, rterminal/1, rconcat/2, regex/1

rconcat(X, Y) :- regex(X), regex(Y).

%%  regex(+Regex) is det.
%
%   Evaluates to true if Regex is either a runion/2, or a rstar/1, or
%   a rconcat/2 or a rterminal/1.
%
%   @see    runion/2, rstar/1, rconcat/2, rterminal/1

regex(X) :- X = rterminal(_) ;
            X = runion(Y, Z), regex(Y), regex(Z) ;
            X = rstar(Y), regex(Y) ;
            X = rconcat(Y, Z), regex(Y), regex(Z).

join_unions(A, B, C) :- is_list(A), is_list(B), !, append(A, B, C).
join_unions(A, B, C) :- is_list(A), !, append(A, [B], C).
join_unions(A, B, [A | B]) :- is_list(B), !.
join_unions(A, B, [A, B]).

unions_to_lists(rterminal(X), rterminal(X)).
unions_to_lists(rstar(X), rstar(Y)) :-
    unions_to_lists(X, Y).
unions_to_lists(rconcat(A, B), rconcat(A1, B1)) :-
    unions_to_lists(A, A1), unions_to_lists(B, B1).
unions_to_lists(runion(A, B), C) :-
    format('joining: ~w with ~w~n', [A, B]),
    unions_to_lists(A, A1), unions_to_lists(B, B1),
    join_unions(A1, B1, C).

optimize_unions(Regex, Optimized) :-
    format('optimizing: ~w~n', [Regex]),
    unions_to_lists(Regex, Lists),
    format('Lists: ~w~n', [Lists]).
