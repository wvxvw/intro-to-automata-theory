:- module('automata/interface',
          [match_regex/2        % :Pred, +Regex, +String
           ]).

/** <module> High-level predicates for dealing with regular expressions

This module defines predicates for searching and replacing in strings
using regular expressions.

@see	https://github.com/wvxvw/intro-to-automata-theory
@tbd	Add match_suffix_regex/3, match_all_regex/3, find_regex/3
*/

:- meta_predicate
       match_regex(+, +).

:- use_module(automata/convert).

%%
%% regex matching
%%

next_states_rec(From, Input, Diagram, Transitions, Cache) :-
    next_states(From, Input, Diagram, NTransitions),
    include('='(trn(_, _, [], _)), NTransitions, ETransitions),
    ord_subtract(ETransitions, Cache, Rest),
    findall(X, next_states(From, [], Diagram, Rest), NextGen),
    ord_subtract(NextGen, Cache, New),
    ( New = [] -> 
          append([Cache, Rest, NextGen], Transitions)
     ;
     append([Cache, Rest, NextGen], NCache),
     findall(Y, (member(trn(FromN, _, _, _), NextGen),
                 next_states_rec(FromN, Input, Diagram, Y, NCache)),
             TransitionsRaw),
     append(TransitionsRaw, Transitions) ).

next_states(Form, Input, Diagram, Transitions) :-
    include('='(trn(From, _, Input, _)), Diagram, Transitions).

next_states(From, Diagram, Transitions) :-
    include('='(trn(From, _, _, _)), Diagram, Transitions).

start_states(Diagram, Transitions) :- next_states(1, Diagram, Transitions).

matcher([trn(From, To, S, Accepting) | Transitions], S, Diagram, Result) :-
    Result = trn(From, To, S, Accepting) ;
    matcher(Transitions, S, Diagram, Result).
matcher([trn(_, To, [], _) | Transitions], S, Diagram, Result) :-
    %% There's a problematic part: if we ahve two states with epsilon-transitions
    %% to each other, we will loop forever...
    format('Following epsilon-transition: ~w~n', [To]),
    next_states(To, Diagram, NTransitions),
    matcher(NTransitions, S, Diagram, Result)
    ;
    matcher(Transitions, S, Diagram, Result).
matcher([trn(_, _, Input, _) | Transitions], S, Diagram, Result) :-
    Input \== S, matcher(Transitions, S, Diagram, Result).

match_regex_helper([], _, _, trn(_, _, _, true)).
match_regex_helper(_, [], _, _) :- fail.
match_regex_helper([S | Suffix], States, Diagram, Matched) :-
    member(State, States),
    format('Matching: ~w, State: ~w~n', [S, State]),
    matcher(State, S, Diagram, Matched),
    format('State: ~w, Matched: ~w~n', [State, Matched]),
    next_states(Matched, Diagram, Next),
    match_regex_helper(Suffix, Next, Diagram, Matched).

%%	match_regex(+Regex, +String) is det.
%
%	Evaluates to true if String is accepted by Regex.
%
%	@see	match_suffix_regex/3, match_all_regex/3, find_regex/3

match_regex(Regex, String) :-
    regex_to_nfa(Regex, Diagram),
    start_states(Diagram, [First | States]),
    format('States: ~w~n', [[First | States]]),
    match_regex_helper(String, [First | States], Diagram, First).
