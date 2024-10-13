
q.
q :- q.

r.

s :- s.

p([]).
p([a|Xs]) :- p(Xs).

t([]).
t([_|Xs]) :- t(Xs).
