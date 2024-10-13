:- module(bool_clph_bool,[clphs_clpbs/2]).

:- use_module(utils).

    
clphs_clpbs(ClpHClauses,ClpBClauses) :-
    h_bool(ClpHClauses,ClpBClauses).
    
h_bool([],[]).
h_bool([ClpH|ClpHs],[ClpB|ClpBs]) :-
	clause_head(ClpH,Head),
	clause_body(ClpH,Bs),
	h_bool_body(Bs,Bs3),
	build_clause(Head,Bs3,ClpB),
	h_bool(ClpHs,ClpBs).

% clause_head(Cl,H) :- arg(1,Cl,H).
% clause_body(Cl,B) :- arg(2,Cl,B).
% build_clause(H,B,obj_clause(H,B)).

h_bool_body([],[]).
h_bool_body(['$constraint'(Cs)|Bs],['$constraint'(Cbs)|Es]) :-
	!,nb_eqs(Cs,Cbs),
	h_bool_body(Bs,Es).
h_bool_body(['$predef'(A)|Bs],['$predef'(A),'$constraint'(Ba)|Ds]) :-
	!,predef_bool(A,Ba),
    h_bool_body(Bs,Ds).
h_bool_body([B|Bs],[B|Ds]) :-
	h_bool_body(Bs,Ds).

nb_eqs([],1).
nb_eqs([A=Term|Eqs],C*Cs) :-
    term_variables(Term,Vars),
    bool_product(Vars,P),
    C = (A=:=P),
	nb_eqs(Eqs,Cs).

bool_product([],1).
bool_product([X|Xs],X*P) :- 
    bool_product(Xs,P).
    
predef_bool(A=B,BC) :- !,
    term_variables(A,Va),
    bool_product(Va,Pa),
    term_variables(B,Vb),
    bool_product(Vb,Pb),
    BC = (Pa=:=Pb). 
predef_bool(E is _, E) :- !.   
predef_bool('$num'(_),1) :- !.
predef_bool('$bool'(B),B) :- !.
predef_bool(_,1).

