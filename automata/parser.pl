:- module('automata/parser',
          [gstar/3,
           gunion/3,
           gchar/3,
           gexps//1
           ]).

:- meta_predicate
       gstar(+, +, -),
       gunion(+, +, -),
       gchar(+, +, -),
       gexps(+, +, -).

/** <module> DCG rules for parsing regular expressions

This module defines DCG rules for parsing regular expressions from
string.

@see	https://github.com/wvxvw/intro-to-automata-theory
*/

:- use_module('automata/ast').

gstar_helper(rstar(S), [Y, 42 | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    phrase(gstarred(S), Test),
    Xs = Ys.
gstar_helper(Exp, [Y, Z | Ys], Acc, Xs) :-
    append(Acc, [Y], Test),
    gstar_helper(Exp, [Z | Ys], Test, Xs).

%%	gstar(+Exp, +Prefix, -Suffix) is det.
%
%	Parses a regular expression followed by an asterisk (the Kleene
%	operator).  Instantiates its first term to the rstar AST nonterminal.
%
%	@see	rstar/1

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
    
%%	gunion(+Exp, +Prefix, -Suffix) is det.
%
%	Parses a union of two regular expressions joined by the `+` sign.
%	Instantiates its first term to the runion AST nonterminal.
%
%	@see	runion/2

gunion(runion(R, L), [X, 43 | Xs], Ys) :-
    phrase(gchar(R), [X]), phrase(gexp(L), Xs, Ys).
gunion(Exp, [X, Y | Ys], Xs) :-
    gunion_helper(Exp, [Y | Ys], [X], Xs).

%%	gchar(+Exp, +Prefix, -Suffix) is det.
%
%	Parses a single terminal character and instantiates it to
%	AST rterminal term.
%
%	@see	rterminal/1

gchar(rterminal(C), [X | Xs], Xs) :-
    %% Our regex character class is somewhat limited...
    member(X, `abcdefghjklmnopqrstuvwxyzABCDEFGHJKLMNOPQRSTUVWXYZ012345678`),
    char_code(C, X).

gstarred(Node) -->
    gstar(Node) ;
    "(", gexps(Node), ")" ;
    gchar(Node).

gexp(Node) --> gstarred(Node) ; gunion(Node).

%%	gexps(+Tree, +Prefix, -Suffix) is det.
%
%	Parses regular expression from the string Prefix and instantiates
%	the Tree to the parse regex/1 term.
%
%	@see	regex/1

gexps(Tree) -->
    gexp(Tree) ;
    gexp(Node), gexps(Rest), { Tree = rconcat(Node, Rest) }.
