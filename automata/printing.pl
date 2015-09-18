:- module('automata/printing',
          [regex_to_string/2,
           format_table/1
           ]).

:- meta_predicate
       regex_to_string(+, -),
       format_table(+).

%%
%% printing regular expression
%% 

vexp(rterminal(C))  --> { char_code(C, R) }, [R].
vexp(runion(L, R))  --> "(", vexp(L), "+", vexp(R), ")".
vexp(rstar(E))      --> "(", vexp(E), ")*".
vexp(rconcat(L, R)) --> vexp(L), vexp(R).

regex_to_string(Exp, Result) :-
    phrase(Exp, Codes), text_to_string(Codes, Result).

%% 
%% pretty printing
%% 

format_table_helper([]).
format_table_helper([row(N, Row) | Table]) :-
    format('~d | ~w |~n', [N, Row]),
    format_table_helper(Table).
format_table(table(Inputs, Table)) :-
    format('~w~n', [Inputs]),
    format_table_helper(Table).
