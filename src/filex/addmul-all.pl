a(0,Y,Y).
a(s(X),Y,s(Z)) :- a(X,Y,Z).

m(0,_Y,0).
m(s(X),Y,P) :- m(X,Y,Pxy),a(Y,Pxy,P).

