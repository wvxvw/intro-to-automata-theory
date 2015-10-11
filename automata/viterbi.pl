:- module('automata/viterbi',
          [viterbi/3,
           make_observation/2,
           observation_state/2,
           observation_prob/2,
           make_hmm/2,
           hmm_states/2,
           hmm_outs/2,
           hmm_initial/2, 
           hmm_emission/2]).

:- meta_predicate
       viterbi(+, +, -).

:- dynamic make_observation/2, observation_state/2, observation_prob/2,
           make_hmm/2, hmm_states/2, hmm_outs/2, hmm_initial/2, 
           hmm_emission/2.

:- use_module(library(record)).
:- use_module(library(heaps)).
:- use_module(library(pairs)).
:- use_module('automata/graph').

:- record observation(state, prob).
:- record hmm(states, outs, initial).

make_list(_, 0, []).
make_list(Elt, Len, [Elt | Result]) :-
    NLen is Len - 1,
    make_list(Elt, NLen, Result).

add_observation(_, [], Graph, Graph).
add_observation(Head, [P-O | Tail], OldGraph, NewGraph) :-
    make_observation([prob(P), state(O)], Obs),
    add_arc(Head, Obs, OldGraph, InterGraph),
    add_observation(Head, Tail, InterGraph, NewGraph).

add_observationс([], _, Graph, Graph).
add_observations([H | Heads], Tail, OldGraph, NewGraph) :-
    add_observation(H, Tail, OldGraph, InterGraph),
    add_observations(Heads, Tail, InterGraph, NewGraph).

add_states([], Graph, Graph).
add_states([Head-Tail | States], OldGraph, NewGraph) :-
    findall(H, (make_observation([value(Head)], O),
                find_vertex(O, OldGraph, H)),
            Heads),
    add_observations(Heads, Tail, OldGraph, InterGraph),
    add_states(States, InterGraph, NewGraph).

hmm_graph(Hmm, Graph) :-
    make_observation([state('^'), prob(1.0)], Start),
    hmm_initial(Hmm, Initial),
    length(Initial, Len),
    make_list(Start, Len, Starts),
    pairs_keys_values(Starts, Initial, Pairs),
    add_arcs(Pairs, [], Graph1),
    hmm_states(Hmm, States),
    add_states(States, Graph1, Graph).

hmm_emission(Hmm, Emission) :-
    format('hmm_emission: ~w~n', [[Hmm, Emission]]).

viterbi_helper(_, [], _, [C | _], C).
viterbi_helper(Model, [P | Path], Front, Candidates, Reason) :-
    format('viterbi_helper: ~w~n', [[Model, [P | Path], Front, Candidates, Reason]]).

viterbi(Model, [P | Path], Reason) :-
    empty_heap(Front),
    hmm_graph(Model, Graph),
    findall(K-Vertex, (make_observation([state(P)], W),
                       find_vertex(W, Graph, Vertex),
                       observation_prob(K, W)),
            Candidates),
    list_to_heap(Candidates, Cands),
    viterbi_helper(Model, Path, Front, Cands, Reason).
