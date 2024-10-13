member(X,[X|L]).
member(X,[Y|L]) :- member(X,L).

tc(X,Y,E,_) :- member(e(X,Y),E).
tc(X,Z,E,V) :-
	member(e(X,Y),E),
	\+ member(Y,V),
	tc(Y,Z,E,[Y|V]).

path(X,[],Y,E) :- member(e(X,Y),E).
path(X,[Y|P],Z,E) :-
	member(e(X,Y),E),
	path(Y,P,Z,E).

cycle_free([]).
cycle_free([X|L]) :-
	\+ member(X,L),
	cycle_free(L).

disjoint(L1,L2) :- \+ not_disjoint(L1,L2).

not_disjoint(L1,L2) :-
	member(X,L1),
	member(X,L2).
