%query: ino(i,o).

ino(T,I):-ino(T,I,[],[],[],[]).

ino(nil,X,X,[],[],[]).
ino(nil,X,X,[C|Cs],[H|Hs],[T|Ts]):- ino(C,H,T,Cs,Hs,Ts).
ino(tree(L,V,R),H,T,Cs,Hs,Ts):- ino(L,H,[V|T1],[R|Cs],[T1|Hs],[T|Ts]).
