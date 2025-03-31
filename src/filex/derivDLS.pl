deriv(d(t),t,1).
deriv(d(N),t,0) :- atom(N).
deriv(d(add(X,Y)),t,add(L,M)) :- deriv(d(X),t,L),deriv(d(Y),t,M).
deriv(d(mul(X,Y)),t,add(mul(X,L),mul(Y,M))) :- deriv(d(X),t,M),deriv(d(Y),t,L).
% avec la clause ci-dessous, ct=0
% d'apres Dershowitz, Lindenstrauss, on ne peut pas
% montrer la term avec une norme lineaire -> omega
deriv(d(d(X)),t,L) :- deriv(d(X),t,M),deriv(d(M),t,L).

%query: deriv(i,i,o).
