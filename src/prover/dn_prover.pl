% from lptp.pl:
:- module(dn_prover, [
    expand_gr/2,
    expand_grs/2,
    write_proof/1
]).

:- op(980, xfy, by).
:- op(970, xfy, :).
:- op(960, yfx, <=>).		% equivalence, left-associative
:- op(950, xfy, =>).		% implication, right-associative
:- op(940, yfx, \/).		% disjunction, left-associative
:- op(930, yfx, &).		    % conjunction, left-associative
:- op(900, fy, ~).
:- op(900, fy, succeeds).
:- op(900, fy, fails).
:- op(800, fy, all).
:- op(800, fy, ex).
:- op(100, fy, ?).

% For testing with other Prolog systems, uncomment these 4 lines:
%gensym(l,l).
%append([],[]).
%append([X|Xs],L) :- append(Xs,M), append(X,M,L).
%:- initialization(consult('mod_lptp.pl')).
% and comment this one:
%:- [mod_lptp].


% We only consider boolean formulas built with ff, &, \/, =>:
% ~ F       ==> (F => ff)
% tt        ==> (ff => ff)
% F <=> G   ==> (F => G) & (G => F)
% See the examples at the end of this file.
%
% Within LPTP, ~p trivially implies (p => ff), but p => ff does not trivially implies ~p
% ?-lptp_check(~ p => (p =>ff),[]).
% LPTP: ok
% true.
% ?- lptp_check((p =>ff) => ~p,[]).
% ! LPTP-Error: underivable formula 
% (p => ff) => ~ p.
% LPTP: no
% true.
% We need to add a proof:
% ?- lptp_check((p =>ff) => ~p,[assume(p => ff, [contra(p,ff)], ~ p)]).
% LPTP: ok
% true.


% nd_proof(+F,-Pr) iff Pr is an LPTP-checked natural deduction proof of F

nd_proof(F,Pr) :- 
  nd_proof([], F, Pr),
  lptp_check(F,Pr).

% nd_proof(+Hyp,+F,-Pr) iff Pr is an LPTP-checked natural deduction proof of F assuming the list of hypothesys Hyp

nd_proof(Hyp,Concl,Proof) :-
  proof(Hyp,Concl,Proof),
  lptp_check(Hyp,toplevel,Concl,Proof).
  

% write_proof(+Proof): print an indented version of Proof 
write_proof(P) :- nl, writeln('['), write_proof(P,2), nl, writeln(']').

write_proof([],_).
write_proof([P],N) :- !, wp_step(P,N).
write_proof([P1,P2|Ps],N) :- wp_step(P1,N), write(','), nl, write_proof([P2|Ps],N).

  wp_step(assume(H,P,C),N) :- !,
    tab(N), write('assume('), wp_formula(H,0), write(', '),write('['), nl,
    N1 is N+2, write_proof(P,N1),writeln('],'),wp_formula(C,N1),write(')').
  wp_step(cases(B, P, C, Q, A),N) :- !,
     tab(N), M is N+2, writeln('cases('),tab(M),write(B),writeln(',['),write_proof(P,M),writeln('],'),
     tab(M),write(C),writeln(',['),write_proof(Q,M),writeln(']'),
     wp_formula(A,M),write(')').
  wp_step(cases(Cs,A),N) :- !, % cases(Cs,A)
    tab(N), M is N+2, writeln('cases(['),wp_case(Cs,M),writeln('], '),wp_formula(A,M),write(')').
  wp_step(indirect(F,P), N) :- !,
     tab(N), M is N+2, writeln('indirect('),wp_formula(F,M),writeln(',['),write_proof(P,M),write('])').
  wp_step(contra(F,P), N) :- !,
     tab(N), M is N+2, writeln('contra('),wp_formula(F,M),writeln(',['),write_proof(P,M),write('])').
   wp_step(F,N) :- wp_formula(F,N). 
  
  wp_case([],_).
  wp_case([case(A,Pr)|Cs],N) :-    
      tab(N), M is N+2, writeln('case('),wp_formula(A,M),writeln(',[]'),
      write_proof(Pr,M),writeln(']), '),
      wp_case(Cs,N).

  wp_formula(F,N) :- tab(N),write(F).

% expand_gr(+F,-F45) iff F45 is the result of applying the axiom 4 and 5 to the formula F
expand_gr(gr(T), Gr) :- expand_gr_term(T,Gr).
expand_gr(~ gr(T), Gr) :- expand_not_gr_term(T,Gr).
expand_gr(ff, ff).
expand_gr(F1 => F2, G1 => G2) :- expand_gr(F1, G1), expand_gr(F2, G2).
expand_gr(F1 \/ F2, G1 \/ G2) :- expand_gr(F1, G1), expand_gr(F2, G2).
expand_gr(F1 & F2, G1 & G2)   :- expand_gr(F1, G1), expand_gr(F2, G2).

  expand_gr_term(T, gr(T)) :- atomic(T), !.
  expand_gr_term(?(Id), gr(?(Id))) :- !.
  expand_gr_term(T, Gr) :- functor(T, F, N), F/N \== '?'/1, expand_gr_term(N, T, Gr).
  
    expand_gr_term(1, T, Gr) :- 
      !, arg(1, T, A1), expand_gr_term(A1, Gr).
    expand_gr_term(N, T, Grn & Grs) :- 
      N > 1, !, P is N -1, 
      arg(N, T, An), expand_gr_term(An, Grn), expand_gr_term(P, T, Grs).

  expand_not_gr_term(T, ff) :- atomic(T), !.
  expand_not_gr_term(?(Id), ~ gr(?(Id))) :- !.
  expand_not_gr_term(T, Gr) :- functor(T, F, N), F/N \== '?'/1, expand_not_gr_term(N, T, Gr).

    expand_not_gr_term(1, T, Gr) :-
      !, arg(1, T, A1), expand_not_gr_term(A1, Gr).
    expand_not_gr_term(N, T, Grn \/ Grs) :-
      N > 1, !, P is N -1,
      arg(N, T, An), expand_not_gr_term(An, Grn), expand_not_gr_term(P, T, Grs).

expand_grs([],[]).
expand_grs([F|Fs],[F45|F45s]) :- expand_gr(F,F45), expand_grs(Fs,F45s).

% prop_var(+X) iff X is a propositional variable, ie gr(Term)
prop_var(gr(_)).

% literal(+L) iff L is a literal 
literal(gr(_)).
literal(gr(_) => ff).


:- discontiguous proof/3.

% case 1 a
proof(G, _A, []) :-
  member(ff, G), 
  !.
  %lptp_check(G, c1a, A, []). 
  
% case 1 b
proof(G, _A, [ff]) :-
  literal(Lit),
  member(Lit, G), 
  member(Lit => ff, G), 
  !.
  %lptp_check(G, c1b_a, A,[ff]). 
  
proof(G, A, []) :-
  literal(A), 
  member(A, G), 
  !.
  %lptp_check(G, c1b_b, A, []). 
  
  
% case 2 c
proof(G, B & C, Pr) :-
  proof(G, B, Prb), 
  proof(G, C, Prc), !, 
  append([Prb, Prc, [B & C]], Pr).
  %lptp_check(G, c2c, B & C, Pr).

% case 2 d
proof(G, B => C, [assume(B, Prc, C)]) :-
  C \== ff,
  proof([B | G], C, Prc), 
  !.
  %lptp_check(G, c2d_a, B => C, [assume(B, Prc, C)]).
  
proof(G, B => ff, [contra(B, Prc), ~ B]) :-
  proof([B | G], ff, Prc), 
  !.
  %lptp_check(G, c2d_b, B => ff, [contra(B, Prc), ~ B, B => ff]).

% case 2 e: first the two trivial subcases, else full power
proof(G, B \/ C, Pr) :-
  proof(G, B, Pb), !,
  append(Pb, [B \/ C], Pr).
  %lptp_check(G, c2e_a, B \/ C, Pr).
proof(G, B \/ C, Pr) :-
  proof(G, C, Pc), !,
  append(Pc, [B \/ C], Pr).
  %lptp_check(G, c2e_b, B \/ C, Pr).
    
proof(G, B \/ C, Pr) :-
  proof([ B => ff | G], C, Pr0), !, % (B => ff) => C, almost ~ B => C
  lemma(p1, B, C, _, Pr1),          % (~ B => C) => B \/ C,
  Pr = [assume(B => ff, Pr0, C), 
        (B => ff) => C,
        assume(~ B, [ B => ff, C], C), 
        ~ B => C,
        Pr1, 
        B \/ C].
  %lptp_check(G, c2e_c, B \/ C, Pr).
  

% case 3 f
proof(G, A, Pr) :-
  select(B & C, G, Delta),
  proof([B, C | Delta], A, P), !,
  Pr = [B & C, B, C | P].
  %lptp_check(G, c3f, A, Pr).
  
  
% case 3 g_a -- only when B is NOT a disjunction
proof(G, A, Pr) :-
  select(B \/ C, G, Delta),
  functor(B,F,N), F/N \== \/ / 2,
  proof([B | Delta], A, PrB), 
  proof([C | Delta], A, PrC), 
  !,
  Pr = [ B \/ C, cases(B, PrB, C, PrC, A), A].
  % lptp_check(G, c3g_a, A, Pr).

% case 3 g_b -- B is a disjunction 
proof(G, A, Pr) :-
  select(B \/ C, G, Delta),
  B = (_ \/ _),
  decompose(B \/ C, Ors),
  proofs(Ors, Delta, A, Proofs), %  proof([B | Delta], A, PrB),   proof([C | Delta], A, PrC), 
  !,
  cases(Ors, Proofs, Cases), % Cases is a liste of case(F,Pr)
  Pr = [ B \/ C, cases(Cases, A), A].
  % lptp_check(G, c3g_b, A, Pr).

  decompose(B \/ C, [B,C]) :- functor(B,F,N), F/N \== \/ / 2, !.
  decompose(B \/ C, Ors) :- B = (_ \/ _), decompose(B,Bs), append(Bs,[C],Ors).
  
  proofs([], _Delta, _A, []).
  proofs([B|Bs], Delta, A, [PrB|PrBs]) :- proof([B| Delta], A, PrB), proofs(Bs, Delta, A, PrBs).

  cases([],[],[]).
  cases([B|Bs],[Prb|PrBs],[case(B,Prb)|Cases]) :- cases(Bs,PrBs,Cases).
  
% case 3 h
proof(G, A, Pr) :-
  select(B => C, G, Delta),
  C \== ff,
  proof([ B => ff | Delta], A, P),
  proof([ C | Delta], A, Q), !,
  lemma(p2, B, C, _, P2),  % (B => C) => ~ B \/  C,
  Pr = [P2, 
        B => C, 
        ~ B \/  C, 
        cases(~ B, [B => ff | P], C, Q, A)].
  %lptp_check(G,c3h,A, Pr).
  
  
% case 3 i
proof(G, A, Pr) :-
  select((B & C) => ff, G, Delta),
  proof([B => ff | Delta], A, P),
  proof([C => ff | Delta], A, Q), !,
  lemma(p3, B, C, _, P3), %  ~ (B & C) => ~ B \/ ~ C,
  Pr = [(B & C) => ff,
        contra(B & C, [ff]), 
        ~ (B & C), 
        P3, 
        ~ B \/ ~ C,
        cases(~ B, [B => ff | P], ~ C, [C => ff | Q], A), 
        A].
  %lptp_check(G, c3i, A, Pr).
  
  
% case 3 j
proof(G, A, Pr) :-
  select( (B \/ C) => ff, G, Delta),
  proof([B => ff, C => ff | Delta], A, P), !,
  lemma(p4, B, C, _, P4), % ~(B \/ C) => ~ B
  lemma(p5, B, C, _, P5), % ~(B \/ C) => ~ C
  Pr = [(B \/ C) => ff,
        contra(B \/ C, [ff]), 
        ~(B \/ C), 
        P4, 
        ~ B, 
        B => ff, 
        P5, 
        ~ C, 
        C => ff | P].
  %lptp_check(G, c3j, A, Pr).
  
      
% case 3 k
proof(G, A, Pr) :-
  select((B => C) => ff, G, Delta),
  proof([B, C => ff | Delta], A, P), !,
  lemma(p6, B , C, _, P6), % ~(B => C) => B,
  lemma(p7, B , C, _, P7), % ~(B => C) => ~ C,
  Pr = [(B => C) => ff,
        contra(B => C, [ff]), 
        ~(B => C), 
        P6, 
        B,
        P7, 
        ~ C, 
        C => ff | P].
  %lptp_check(G, c3k, A, Pr).
  


/* tests:
make.
nd_proof((ff => ff), P).
nd_proof(ff, P).
nd_proof(gr(?p) \/ (gr(?p) => ff), P).
nd_proof(gr(?p), P).
nd_proof(gr(?a) => gr(?b), P).
nd_proof(gr(?a) => gr(?a), P).
nd_proof(gr(?a) => ((gr(?a)=> ff) => ff), P).
nd_proof(((gr(?a)=> ff) => ff) => gr(?a), P).
nd_proof( (gr(?a) => gr(?b)) \/ (gr(?b) => gr(?a)), P).
nd_proof(((gr(?a) => ff) \/ gr(?b)) => (gr(?a) => gr(?b)), P).
nd_proof((gr(?a) => gr(?b)) => ((gr(?a)=> ff) \/ gr(?b)), P).
nd_proof(((gr(?b)=> ff) => (gr(?a)=> ff)) => (gr(?a) => gr(?b)), P).
nd_proof(((gr(?b)=> ff) => gr(?c)) => gr(?b) \/ gr(?c), P).
*/
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The following seven lemmas are LPTP-correct.

lemma(p1, P, Q, (~ P => Q) => P \/ Q,
assume( ~ P => Q,
 [indirect(~ (P \/ Q),
   [contra(P, [P \/ Q, ff]),  ~ P,
    Q, P \/ Q, ff])],
 P \/ Q)). %:- write(p1).

lemma(p2, P, Q, (P => Q) => ~ P \/ Q,
assume(P => Q,
 [indirect(~ (~ P \/ Q),
  [indirect(~ P, [~ P \/ Q, ff]),  P,
   Q, ~ P \/ Q, ff])],
~ P \/ Q)). %:- write(p2).

lemma(p3, P, Q, ~ (P & Q) => ~ P \/ ~ Q,
assume( ~ (P & Q),
  [indirect( ~  (~ P \/ ~ Q),
    [indirect(~ P,[~ P \/ ~ Q, ff]), P,
     indirect(~ Q, [~ P \/ ~ Q, ff]), Q,
     P & Q, ff])],
  ~ P \/ ~ Q)). %:- write(p3).

lemma(p4, P, Q, ~(P \/ Q) => ~ P,
assume(~(P \/ Q),
 [contra(P,[P \/ Q, ff])],
 ~ P)). %:- write(p4).

lemma(p5, P, Q, ~(P \/ Q) => ~ Q,
assume(~(P \/ Q),
 [contra(Q,[P \/ Q, ff])],
 ~ Q)). %:- write(p5).

lemma(p6, P, Q, ~(P => Q) => P,
assume(~(P => Q),
 [indirect(~ P, [assume(P, [ff, Q], Q), ff])],
 P)). %:- write(p6).
    
lemma(p7, P, Q, ~(P => Q) => ~ Q,
assume(~(P => Q),
 [contra(Q,[assume(P, [], Q), ff])],
 ~ Q)). %:- write(p7).

/* lemma P1 -- P7
make.
nd_proof(((gr(?p) => ff) => gr(?q)) => gr(?p) \/ gr(?q),P).
nd_proof((gr(?p) => gr(?q))  => (gr(?p)=> ff) \/ gr(?q),P).
nd_proof(((gr(?p) & gr(?q)=> ff))  => (gr(?p) => ff) \/ (gr(?q)=> ff),P).
nd_proof( ((gr(?p) \/ gr(?q))=> ff) => (gr(?p) => ff) ,P).
nd_proof(((gr(?p) \/ gr(?q))=> ff) => (gr(?q)=> ff) ,P).
nd_proof(((gr(?p) => gr(?q))=> ff) => gr(?p) ,P).
nd_proof(((gr(?p) => gr(?q)) => ff) => (gr(?q)=> ff) ,P).
*/

/* ex. 56:
make.
nd_proof( ((gr(?a) => ff) \/ gr(?b)) => (gr(?a) => gr(?b)), P).
nd_proof(((gr(?b)=> ff) => (gr(?a)=> ff)) => (gr(?a) => gr(?b)),Pr).
*/

/* ex. 57
make.
nd_proof( ((gr(?a) & (gr(?a) => ff) => ff)), P).
nd_proof( (gr(?a) \/ gr(?a)) => gr(?a), P).
nd_proof((gr(?a) & gr(?a)) => gr(?a), P).
nd_proof((gr(?a) & (gr(?b) \/gr(?c))) => gr(?a) & gr(?b) \/ gr(?a) & gr(?c), P).
nd_proof((gr(?a) & gr(?b) \/ gr(?a) & gr(?c)) => (gr(?a) & (gr(?b) \/ gr(?c))), P).
nd_proof((gr(?a) \/ gr(?b) & gr(?c) ) => ((gr(?a) \/ gr(?b))  & (gr(?a) \/ gr(?c))), P).
nd_proof( ((gr(?a) \/ gr(?b))  & (gr(?a) \/ gr(?c))) => (gr(?a) \/ gr(?b) & gr(?c)), P).
*/

/* ex. 58:
make.
nd_proof( ((gr(?b) => ff) => gr(?c)) => gr(?b) \/ gr(?c), P).
nd_proof( (gr(?b) => gr(?c)) => (gr(?b) => ff) \/ gr(?c), P).
nd_proof( ((gr(?b) & gr(?c)) => ff) => (gr(?b) => ff) \/ (gr(?c)=> ff), P).
nd_proof( ((gr(?b) \/ gr(?c))=> ff) => (gr(?b)=> ff), P).
nd_proof( ((gr(?b) \/ gr(?c))=> ff) => (gr(?c)=> ff), P).
nd_proof( ((gr(?b) => gr(?c))=> ff) => gr(?b), P).
nd_proof( ((gr(?b) => gr(?c))=> ff) => (gr(?c) => ff), P).
*/

/* ex. 59:
make.
nd_proof(((gr(?a) \/ gr(?b))=> ff) => (gr(?a) => ff) & (gr(?b)=> ff), P).
nd_proof( (gr(?a)=>ff) & (gr(?b)=> ff) => ((gr(?a) \/ gr(?b))=> ff),P).
nd_proof( ((gr(?a) &  gr(?b))=>ff) => (gr(?a)=>ff) \/ (gr(?b)=>ff), P).
nd_proof( (gr(?a)=>ff) \/  (gr(?b)=>ff) => ((gr(?a) & gr(?b))=>ff), P).
nd_proof( (gr(?a) \/ gr(?b)) & ((gr(?a)=>ff) \/ gr(?b)) => gr(?b), P).
nd_proof( (gr(?a) \/ gr(?b)) & ((gr(?b)=>ff) \/ gr(?c)) => (gr(?a) \/ gr(?c)), P).
*/   
    
/* exo 60:
make.
nd_proof((gr(?p)=>ff) & ( ((gr(?p)=>ff) & gr(?q))=>ff) => (gr(?q)=>ff), P).
nd_proof( ((gr(?p) & gr(?q)) & (gr(?p) & gr(?r)) & (gr(?p)=>ff)) => gr(?q) \/ gr(?r), P).
nd_proof( (gr(?p)=>ff) \/ ((gr(?p) & gr(?q))=>ff) => ((gr(?q)=>ff) \/ (gr(?p)=>ff)), P).
*/

/* exo 61:
make.
nd_proof((gr(?p) \/ gr(?q)) => ((gr(?p)=> ff) & (gr(?q)=>ff)) => gr(?r), P).
nd_proof((gr(?p) => gr(?q)) & (gr(?q) => gr(?r)) & (gr(?r) => ff) => (gr(?p)=> ff), P).
nd_proof((gr(?p) => gr(?q)) => ((gr(?p) & gr(?q) ) \/ (gr(?p)=> ff)), P).
*/

/*
% ex. 62: 
make.
nd_proof( (gr(?p) \/ gr(?q)) & (gr(?p) => gr(?r)) => (gr(?q) \/ gr(?r)),P).
*/

/*
make.
nd_proof([gr(?a) => ff,gr(?b) => ff],(gr(?a) \/ gr(?b)) => ff, Pr).
nd_proof([gr(?a) => ff,gr(?b) => ff, gr(?c) => ff],(gr(?a) \/ gr(?b) \/ gr(?c)) => ff, Pr).
nd_proof([gr(?a) & gr(?b), gr(?a) => gr(?c), gr(?b)=> gr(?d)],gr(?b) &gr(?d), P). 
nd_proof([gr(?a) & gr(?b) & gr(?c), gr(?a) => gr(?d), gr(?b)=> gr(?e),gr(?c)=>gr(?f)],gr(?e) & gr(?d) & gr(?f), P).  
*/
 
/*
make.

nd_proof(
  [gr([?x3|?x4]) => gr(?x3) & gr(?x4),
   gr(?x3) & gr(?x4) => gr([?x3|?x4])],

  gr([?x3|?x4])&gr(?x3)\/(gr([?x3|?x4])=>ff)&gr(?x3)\/(gr([?x3|?x4])=>ff)&(gr(?x3)=>ff),

P),term_size(P,Ts).

P = ...
TS = 2221


nd_proof(
  [],

  (gr(?x3)&gr(?x4))&gr(?x3)\/((gr(?x3)&gr(?x4))=>ff)&gr(?x3)\/((gr(?x3)&gr(?x4))=>ff)&(gr(?x3)=>ff),

P),term_size(P,Ts).

P = ...
TS = 1365


nd_proof(
  [gr([?x6|?x7]) => gr(?x6) & gr(?x7), 
   gr(?x6) & gr(?x7) => gr([?x6|?x7]),
   gr(?x7)&gr(?x5)\/(gr(?x7)=>ff)&gr(?x5)\/(gr(?x7)=>ff)&(gr(?x5)=>ff)],

  gr([?x6|?x7])&gr(?x5)\/(gr([?x6|?x7])=>ff)&gr(?x5)\/(gr([?x6|?x7])=>ff)&(gr(?x5)=>ff),

  P),term_size(P,Ts).

P = ...
TS = 3857


nd_proof(
  [gr(?x7)&gr(?x5)\/(gr(?x7)=>ff)&gr(?x5)\/(gr(?x7)=>ff)&(gr(?x5)=>ff)],

  (gr(?x6) & gr(?x7))&gr(?x5)\/((gr(?x6) & gr(?x7))=>ff)&gr(?x5)\/((gr(?x6) & gr(?x7))=>ff)&(gr(?x5)=>ff),

  P),term_size(P,Ts).
P = ...
TS = 2555
*/
 
 
 
 
