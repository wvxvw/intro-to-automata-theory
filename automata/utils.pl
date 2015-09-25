:- module('automata/utils',
          [reflexive_pairs/2,
           cmp_lists/3,
           replace_all/4,
           replace_all_lift/4,
           replace_all_tree/4,
           replace_all_tree_lift/4
           ]).

:- meta_predicate
       reflexive_pairs(+, -),
       cmp_lists(+, +, -),
       replace_all(+, +, +, -),
       replace_all_lift(+, +, +, -),
       replace_all_tree(+, +, +, -),
       replace_all_tree_lift(+, +, +, -).

/** <module> Vairous utilitis for working with lists

This module defines several utilities for working with lists
used across multiple other automata modules.

@see    https://github.com/wvxvw/intro-to-automata-theory
*/

reflexive_pair(_, [], []).
reflexive_pair(X, [Y | Ys], [[X, Y] | Pairs]) :-
    reflexive_pair(X, Ys, Pairs).

reflexive_pairs(_, [], []).
reflexive_pairs(X, [Y | Ys], Pairs) :-
    reflexive_pair(X, [Y | Ys], Z),
    reflexive_pairs(Y, Ys, YPairs),
    append(Z, YPairs, Pairs).

%%  reflexive_pairs(+Source, -Pairs) is det.
%
%   Evaluates to true when Pairs contains lists of length 2 each of
%   which contains a unique pair from the elements of Source.  For
%   this purpose `[X, Y]` is the same as `[Y, X]`.

reflexive_pairs([X | Xs], Pairs) :-
    reflexive_pairs(X, Xs, Pairs).

%%  cmp_lists(+List1, +List2, -Op) is det.
%
%   Lexicographically compares List1 and List2.  Op is set to either
%   one of `<`, `=` and `>` respectively.

cmp_lists([], [], '=').
cmp_lists(X, [], '>') :- X \== [].
cmp_lists([], X, '<') :- X \== [].
cmp_lists([X | _], [Y | _], '>') :- X > Y.
cmp_lists([X | _], [Y | _], '<') :- X < Y.
cmp_lists([X | Xs], [X | Ys], Result) :-
    cmp_lists(Xs, Ys, Result).

%%  replace_all(+Searched, +Replacement, +Source, -Destination) is det.
%
%   Evaluates to true when Destination contains all the elements of
%   Source with Searched element replaced by Replacement.
%
%   @see replace_all_lift/4, replace_all_tree/4, replace_all_tree_lift/4

replace_all(_, _, [], []).
replace_all(X, Y, [Z | Xs], [Z | Ys]) :-
    dif(X, Z),
    replace_all(X, Y, Xs, Ys).
replace_all(X, Y, [X | Xs], [Y | Ys]) :-
    replace_all(X, Y, Xs, Ys).

%%  replace_all_lift(+Replacement, +Searched, +Source, -Destination) is det.
%
%   Same as replace_all/4 except that Replacement element is
%   substituted for each of the elements of Searched list.
%
%   @see replace_all/4, replace_all_tree/4, replace_all_tree_lift/4

replace_all_lift(_, [], Zs, Zs).
replace_all_lift(X, [Y | Ys], Zs, Qs) :-
    replace_all(Y, X, Zs, Zs1),
    replace_all_lift(X, Ys, Zs1, Qs).

replace_all_tree_helper(_, _, [], []).
replace_all_tree_helper(X, Y, [X | Xs], [Y | Zs]) :-
    replace_all_tree_helper(X, Y, Xs, Zs).
replace_all_tree_helper(X, Y, [Z | Xs], [Z | Zs]) :-
    \+ is_list(Z),
    dif(X, Z),
    replace_all_tree_helper(X, Y, Xs, Zs).
replace_all_tree_helper(X, Y, [Z | Xs], [Qs | Zs]) :-
    is_list(Z),
    replace_all_tree_helper(X, Y, Z, Qs),
    replace_all_tree_helper(X, Y, Xs, Zs).

%%  replace_all_tree(+Searched, +Replacement, +Source, -Destination) is det.
%
%   Same as replace_all/4 except that Searched cannot be a list, and
%   all sublists of Source are processed recursively.
%
%   @see replace_all/4, replace_all_lift/4, replace_all_tree_lift/4

replace_all_tree(X, Y, Xs, Ys) :-
    \+ is_list(X),
    replace_all_tree_helper(X, Y, Xs, Ys).

%%  replace_all_tree_lift(+Searched, +Replacement, +Source, -Destination) is det.
%
%   Same as replace_all_tree/4 except that Replacement element is
%   substituted for each of the elements of Searched list.
%
%   @see replace_all/4, replace_all_tree/4, replace_all_lift/4

replace_all_tree_lift(_, [], Xs, Xs).
replace_all_tree_lift(X, [Y | Ys], Xs, Zs) :-
    replace_all_tree(Y, X, Xs, Qs),
    replace_all_tree_lift(X, Ys, Qs, Zs).
