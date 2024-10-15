%query: popt3(i,o).

popt3([],[]).
popt3(Rest, Pil) :-
	popt31(Rest, Pil).
popt3([Inst|_], Pil) :-
	Pil = [Inst|Pil1],
	popt3(Pil, Pil1).

popt31([g(_)|Rest], OptRest) :-
	popt3(Rest,OptRest).
