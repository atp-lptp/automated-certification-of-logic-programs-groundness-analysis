/* Filename: ciao.pl 							*/
/* Abstract: System predicates for Ciao-Prolog. */

% Compiling with Ciao:

:- use_module(library(classic/classic_predicates)).

%%d io__lptp_home(gr::out)

io__lptp_home('/Users/Shared/logic-program-theorem-prover-ciao').

%%d io__path_sep(gr::out)

io__path_sep(/).

%%d atomic_length(gr::in,int::out)

atomic_length(Atom,N) :-
	(	atomic(Atom) ->
		atom_length(Atom,N)
	;	number_chars(Atom,CharL),
		length(CharL,N)
	).

%%d io__get_stream(gr::in,gr::in,gr::out)

io__get_stream(File,Mode,Stream) :-
	open(File,Mode,Stream).

%%d io__set_output(gr::in)

io__set_output(Stream) :- set_output(Stream).

%%d io__set_input(gr::in)

io__set_input(Stream) :- set_input(Stream).

%%d db__user_stream(gr::out)

:- dynamic db__user_stream/1.

db__user_stream(user).

%%d io__original_user(gr::out)

io__original_user(user).

%%d read_with_variables(any,any)

read_with_variables(Term,VarL) :-
	read_term(Term,[variable_names(VarL)]).

log_info(Prefix, Message) :-
    File = 'output',
    ParentDirectory = '/Users/Shared/logic-program-theorem-prover-ciao/log',
%    io__open('log', ParentDirectory),
	concat_atom([ParentDirectory, '/', File, '.log'], File_log),
	io__get_stream(File_log, append, Stream_log),
    set_output(Stream_log),

	datime(datime(Y,M,D,H,Mn,S))

    Sep = "=====================================",
    concat_atom([Sep, Y,"-", M, "-", D, " ", H, "-", Mn,"-", S, Sep], Now),
    write(Now), nl,
    concat_atom([Prefix, ":"], MessagePrefix),
    write(MessagePrefix), nl,
    writeq(Message), nl,
    write(Now), nl,
	close(Stream_log).

% Example:
% 
% | ?- read_term([variable_names(L)],T).
% |: f(X,_Y,_,X).
% 
% L = ['X'=_6711,'_Y'=_6728],
% T = f(_6711,_6728,_6745,_6711) ;

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

%%d initialization(any)

% initialization(Goal).

% swi.pl ends here
