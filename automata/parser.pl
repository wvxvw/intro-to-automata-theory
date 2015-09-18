:- module('automata/parser',
          [gstar/3,
           gunion/3,
           gchar/3,
           gstarred/3,
           gexp/3,
           gexps/3
           ]).

:- meta_predicate
       gstar(+, +, -),
       gunion(+, +, -),
       gchar(+, +, -),
       gstarred(+, +, -),
       gexp(+, +, -),
       gexps(+, +, -).

:- use_module('automata/ast').

%%
%% regular expression parser
%% 

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
