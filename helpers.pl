:- use_module(library(lists)).

concatentated_member(L1, L2, L3) :-
    member(M1, L1), member(M2, L2),
    string_concat(M1, M2, L3).

concatentated(L1, L2, L3) :-
    findall(X, concatentated_member(L1, L2, X), X),
    list_to_set(X, L3).

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

%% nfa(Regex, Diagram) :-.
