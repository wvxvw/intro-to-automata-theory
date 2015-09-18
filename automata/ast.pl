:- module('automata/ast',
          [rterminal/1,
           runion/2,
           rstar/1,
           rconcat/2,
           regex/1
          ]).

:- meta_predicate
       rterminal(+),
       runion(+, +),
       rstar(+),
       rconcat(+, +),
       regex(+).

%% 
%% regular expression constituents
%% 

rterminal([]).                  % this is epsilon
rterminal(X)  :- atom(X).
runion(X, Y)  :- regex(X), regex(Y).
rstar(X)      :- regex(X).
rconcat(X, Y) :- regex(X), regex(Y).
regex(X)      :- rterminal(X) ;
                 X = runion(Y, Z), regex(Y), regex(Z) ;
                 X = rstar(Y), regex(Y) ;
                 X = rconcat(Y, Z), regex(Y), regex(Z).
