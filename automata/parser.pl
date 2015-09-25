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

@see    https://github.com/wvxvw/intro-to-automata-theory
*/

:- use_module('automata/ast').

upto(_, [], _) :- !, fail.
upto(X, [X | Xs], Ys) :- Xs = Ys ; upto(X, Xs, Ys).
upto(X, [Y | Xs], Ys) :- dif(X, Y), upto(X, Xs, Ys).

upto(_, [], _, _) :- !, fail.
upto(X, [X | Xs], Ys, Zs) :-
    Xs = Zs, Ys = [] ; upto(X, Xs, Ys1, Zs), Ys = [X | Ys1].
upto(X, [Y | Xs], [Y | Ys], Zs) :-
    dif(X, Y), upto(X, Xs, Ys, Zs).

balanced_helper(N, _, M, _, []) :- M = N, !.
balanced_helper(N, _, M, _, _) :- M > N, !, fail.
balanced_helper(N, Start, M, End, [Start | Ss]) :-
    N1 is N + 1,
    balanced_helper(N1, Start, M, End, Ss).
balanced_helper(N, Start, M, End, [End | Ss]) :-
    M1 is M + 1,
    balanced_helper(N, Start, M1, End, Ss).
balanced_helper(N, Start, M, End, [S | Ss]) :-
    Start \== S, End \== S,
    balanced_helper(N, Start, M, End, Ss).

balanced(Start, End, String) :-
    Start \== End,
    balanced_helper(0, Start, 0, End, String).

%%  gstar(+Exp, +Prefix, -Suffix) is det.
%
%   Parses a regular expression followed by an asterisk (the Kleene
%   operator).  Instantiates its first term to the rstar AST nonterminal.
%
%   @see    rstar/1

gstar(rstar(S), [X, 42 | Xs], Xs) :- gchar(S, [X], _).
gstar(rstar(S), [X, Y | Ys], Xs) :-
    Y \== 42,
    upto(42, [X, Y | Ys], Prefix, Xs),
    balanced(40, 41, Prefix),
    phrase(gstarred(S), Prefix).
    
%%  gunion(+Exp, +Prefix, -Suffix) is det.
%
%   Parses a union of two regular expressions joined by the `+` sign.
%   Instantiates its first term to the runion AST nonterminal.
%
%   @see    runion/2

gunion(runion(R, L), [X, 43 | Xs], Ys) :-
    gchar(R, [X], _), phrase(gexp(L), Xs, Ys).
gunion(runion(R, L), [X, Y | Ys], Xs) :-
    Y \== 43,
    upto(43, [X, Y | Ys], Prefix, Suffix),
    balanced(40, 41, Prefix),
    phrase(gexps(R), Prefix),
    phrase(gexps(L), Suffix, Xs).

%%  gchar(+Exp, +Prefix, -Suffix) is det.
%
%   Parses a single terminal character and instantiates it to
%   AST rterminal term.
%
%   @see    rterminal/1

gchar(rterminal(C), [X | Xs], Xs) :-
    %% Our regex character class is somewhat limited...
    (
        %% 603 is the code for epsilon
        X = 603 -> C = [] ;
        member(X, `abcdefghjklmnopqrstuvwxyzABCDEFGHJKLMNOPQRSTUVWXYZ012345678`),
        char_code(C, X)
    ).

ggroup(Exp, [40 | Prefix], Suffix) :-
    upto(41, Prefix, Group, Suffix),
    balanced(40, 41, Group),
    phrase(gexps(Exp), Group).

gstarred(Node) --> gstar(Node) ; ggroup(Node) ; gchar(Node).

gexp(Node) --> gstarred(Node) ; gunion(Node).

%%  gexps(+Tree, +Prefix, -Suffix) is det.
%
%   Parses regular expression from the string Prefix and instantiates
%   the Tree to the parse regex/1 term.
%
%   @see    regex/1

gexps(Tree) -->
    gexp(Tree) ;
    gexp(Node), gexps(Rest), { Tree = rconcat(Node, Rest) }.
