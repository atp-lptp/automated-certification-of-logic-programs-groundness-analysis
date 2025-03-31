member(X,[X|L]).
member(X,[Y|L]) :- member(X,L).


