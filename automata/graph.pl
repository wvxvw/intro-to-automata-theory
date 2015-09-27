:- module('automata/graph',
          [make_graph/2,
           add_arc/4,
           has_arc/3,
           find_vertex/3,
           vertex_value/2,
           vertex_arcs/2,
           make_vertex/2
          ]).

:- meta_predicate
       make_graph(+, -),
       add_arc(+, +, +, -),
       has_arc(+, +, +),
       find_vertex(+, +, -),
       vertex_value(?, ?),
       vertex_arcs(?, ?),
       make_vertex(?, ?).

:- dynamic vertex_value/2, vertex_arcs/2, make_vertex/2.

/** <module> Graph data-structure for housing the FSA

This module defines predicates for working with graph data-structure,
these should be useful for working with NFA and DFA.

@see    https://github.com/wvxvw/intro-to-automata-theory
*/

:- use_module(library(record)).

:- record vertex(value, arcs=[_ | _]).

lookup(X, [X | _]).
lookup(X, [Y | Xs]) :- X \== Y, lookup(X, Xs).

instantiated(Goal, [X | _], []) :- \+ call(Goal, X).
instantiated(Goal, [X | Xs], [X | Ys]) :- call(Goal, X), instantiated(Goal, Xs, Ys).

vertex_instantiated(Vertex) :-
    make_vertex([], Vertex),
    vertex_value(Vertex, Value),
    ground(Value).
    
find_vertex_helper(Value, _, Vertex) :- vertex_value(Vertex, Value).
find_vertex_helper(V1, Cache, V2) :-
    vertex_arcs(V2, Arcs),
    instantiated(vertex_instantiated, Arcs, InstArcs),
    subtract(InstArcs, Cache, FilteredArcs),
    union(Cache, InstArcs, NewCache),
    findnsols(1, V, (member(V, FilteredArcs),
                     find_vertex_helper(V1, NewCache, V)),
              [V2]).

find_vertex(_, [], _) :- !, fail.
find_vertex(Value, [V | Graph], Vertex) :-
    vertex_value(V, Value), Vertex = V
    ;
    vertex_arcs(V, Arcs),
    instantiated(vertex_instantiated, Arcs, InstArcs),
    include(find_vertex_helper(Value, []), InstArcs, [Vertex])
    ;
    find_vertex(Value, Graph, Vertex).

find_or_create_vertex(Value, Vertex, Graph, Graph) :-
    find_vertex(Value, Graph, Vertex), !.
find_or_create_vertex(Value, Vertex, OldGraph, [Vertex | OldGraph]) :-
    make_vertex([value(Value)], Vertex).

add_arc(From, To, OldGraph, NewGraph) :-
    find_or_create_vertex(From, VertexFrom, OldGraph, Graph1),
    find_or_create_vertex(To, VertexTo, Graph1, NewGraph),
    vertex_arcs(VertexFrom, Arcs),
    lookup(VertexTo, Arcs).

make_graph_helper([], Graph, Graph).
make_graph_helper([From-To | Vs], GraphIn, GraphOut) :-
    add_arc(From, To, GraphIn, NewGraph),
    make_graph_helper(Vs, NewGraph, GraphOut).

make_graph(Vs, Graph) :- make_graph_helper(Vs, [], Graph).

has_arc(Graph, From, To) :-
    find_vertex(From, Graph, FromVertex),
    vertex_arcs(FromVertex, Arcs),
    instantiated(vertex_instantiated, Arcs, InstArcs),
    findnsols(1, A, (member(A, InstArcs),
                     vertex_value(A, To)),
              [_]).

test(G) :-
    make_graph([x1-x2, x1-x3, x2-x1, x2-x3, x3-x5, x3-x6, x3-x4,
                x4-x7, x5-x2, x5-x6, x6-x3, x6-x7], G),
    findall(X, (member(From-To, [x1-x2, x1-x3, x2-x1, x2-x3, 
                                 x3-x5, x3-x6, x3-x4, x4-x7, 
                                 x5-x2, x5-x6, x6-x3, x6-x7,
                                 x6-x5]),
                ( has_arc(G, From, To) -> X = [From, To, true]
                 ;
                 X = [From, To, false] )),
            Xs),
    format('Arcs: ~w~n', [Xs]).
