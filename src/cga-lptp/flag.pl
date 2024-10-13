:- module(flag,[current_cti_flag/2,set_cti_flag/2]).

:- use_module(predef).

:- dynamic(current_cti_flag/2).

% default values for flags
current_cti_flag(cTI_version,'2.0').
current_cti_flag(process_include_ensure_loaded,no).
current_cti_flag(time_out,10).  % in seconds
current_cti_flag(nb_ite_clpn,4).
current_cti_flag(print_info,yes).
current_cti_flag(poly_lib,poly_clpq).
current_cti_flag(size,term_size).
current_cti_flag(known_predicate,PI) :-
	(var(PI) ->
	    predef(Atom),
	    functor(Atom,P,N),
	    PI=P/N
	;
	    (ground(PI) ->
		PI=P/N,
		functor(Atom,P,N),
		predef(Atom))).

% update value for flag
set_cti_flag(X,_) :- var(X),!,fail.
set_cti_flag(time_out,V) :-
	integer(V), V >= 10, !, % min for timeout
	retractall(current_cti_flag(time_out,_)),
	asserta(current_cti_flag(time_out,V)).
set_cti_flag(nb_ite_clpn,V) :-
	integer(V), V >= 1, !,
	retractall(current_cti_flag(nb_ite_clpn,_)),
	asserta(current_cti_flag(nb_ite_clpn,V)).
set_cti_flag(process_include_ensure_loaded,V) :-
	(V==yes ; V==no),!,
	retractall(current_cti_flag(process_include_ensure_loaded,_)),
	asserta(current_cti_flag(process_include_ensure_loaded,V)).
set_cti_flag(size,N) :-
    (N==term_size ; N==list_size ; N==term_size_list_size),!,
	retractall(current_cti_flag(size,_)),
	asserta(current_cti_flag(size,N)).
set_cti_flag(print_info,V) :-
	(V==yes ; V==no),!,
	retractall(current_cti_flag(print_info,_)),
	asserta(current_cti_flag(print_info,V)).
set_cti_flag(Option,Value) :-
    write('% unknown option/value pair in set_cti_flag/2: '),writeln(Option-Value),
    fail.
