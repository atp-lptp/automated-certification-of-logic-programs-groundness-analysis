
%query: p(i,i).
p(0,0).
p(s(X),Y):-q(X,Y).
q(X,s(Y)):-p(X,Y).

