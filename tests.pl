:- use_module(automata).
:- use_module(automata(viterbi)).

test_viterbi :-
    make_hmm([states([healthy-[0.7-healthy, 0.3-fever],
                     fever-[0.4-healthy, 0.6-fever]]),
              outs([healty-[(normal, 0.5), (cold, 0.4), (dizzy, 0.1)]),
                   fever-[(normal, 0.1), (cold, 0.3), (dizzy, 0.6)]],
              initial([0.6-healthy, 0.4-fever])], Hmm),
    viterbi(Hmm, [normal, cold, dizzy], Reason),
    format('Reason: ~w~n', [Reason]).
              
