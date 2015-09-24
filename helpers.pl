:- doc_server(4000).    % Start PlDoc at port 4000
:- portray_text(true).  % Enable portray of strings

:- use_module(library(lists)).
:- use_module(library(doc_latex)).
:- use_module(automata).
:- use_module(automata(convert)).
:- use_module(automata(printing)).

:- doc_collect(true).

concatentated_member(L1, L2, L3) :-
    member(M1, L1), member(M2, L2),
    string_concat(M1, M2, L3).

concatentated(L1, L2, L3) :-
    findall(X, concatentated_member(L1, L2, X), X),
    list_to_set(X, L3).

test_automata(X) :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_table(X, Y),
    format_table(Y).

test_to_string :-
    phrase('automata/parser':gexps(Parsed), `x(y+x)*+z`),
    regex_to_string(Parsed, S),
    format('Regex: ~w~n', [S]).

test_nfa_to_dfa(Dfa) :-
    regex_to_nfa(`x(y+x)*+z`, Nfa),
    nfa_to_dfa(Nfa, Dfa),
    format_table(Dfa).

test_match :-
    match_regex(`x(y+x)*+z`, `xyyxxxyxxy`).

test_mismatch :-
    match_regex(`x(y+x)*+z`, `xyyxxxyxxyz`).

test_smatch_suffix(Suffix) :-
    match_suffix_regex(`x(y+x)*+z`, `xyyxxxyxxyzab`, Suffix).

test_reacheable_epsilon(States) :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_table(X, Y),
    'automata/convert':reacheable_epsilon(3, x, Y, States).

test_match_all(Matches) :-
    findall(X, match_all_regex(`x(y+x)*+z`, `xyyxxxyxxyz`, X), Matches).

test_dfa_to_regex(Regex) :-
    regex_to_nfa(`x(y+x)*+z`, X),
    nfa_to_dfa(X, Y),
    dfa_to_regex(Y, Regex).

test_invert(Regex) :-
    invert_regex(`x(y+x)*+z`, Regex).

gen_doc :-
    doc_latex(['automata',
               'automata/ast',
               'automata/convert',
               'automata/parser',
               'automata/printing'],
              'automata-doc.tex',
              [stand_alone(false),
               section_level(subsection)]).

largest_subseq_sum(Seq, Max) :-
    findall(S, (append([_, X, _], Seq), sum_list(X, S)), Subs),
    max_list(Subs, Max).

% ?- largest_subseq_sum([3, -2, 5, -9, 7, 1], X).
% X = 8.

replace_tex(Out) -->
    [], { Out = "" } ;
    "*", replace_tex(Y), { string_concat("^*", Y, Out) } ;
    [603], replace_tex(Y), { string_concat("\\epsilon", Y, Out) } ;
    [X], replace_tex(Y), { text_to_string([X], Xs), string_concat(Xs, Y, Out) }.

assignment_12a :-
    invert_regex(`x(y+x)*+z`, Regex),
    string_codes(Regex, Codes),
    phrase(replace_tex(X), Codes),
    format('$$~w$$', [X]).

test_union_optimize(Optimized) :-
    phrase('automata/parser':gexps(Parsed), `((((z+y)z+((z+y)y+(z+y)x))+((z+y)+(((z+y)z+((z+y)y+(z+y)x))((z+(y+x)))*+((xy+xx)z+((xy+xx)((y+x))*+xz(z+(y+x)))))))+(((xy+xx)zz+((xy+xx)zy+((xy+xx)zx+(xz(z+(y+x))z+(xz(z+(y+x))y+xz(z+(y+x))x)))))(ɛ+((z+(y+x)))*)+ɛ))`),
    'automata/ast':optimize_unions(Parsed, Optimized),
    format('Optimized: ~w~n', [Optimized]).
