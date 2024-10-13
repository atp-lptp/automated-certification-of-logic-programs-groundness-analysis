:- module(prover, [
    derive_groundness_property/3,
    prove/4,
    prove_groundness_property/4,
    prove_with_premises/5,
    is_compound_form_except_list_question_mark/1
]).

% The next line is used for proving termination using cTI:
%query: prove(i,i,i,o).

% Huth and Ryan, Sect. 1.4.4 (completeness of the
% natural deduction rules of propositional logic).
%
% This implementation is based on the
% proof of prop. 1.38 and the example that
% follows this proof (i.e., p & q => p).

% Propositional formulas are built from
% propositional variables (Prolog atoms)
% and the connectors & (and), \/ (or),
% => (entails), ~ (not), e.g.,
% (p & q) => p.

:- op(100, fy,  ?).
:- op(150, xfy, :).
:- op(140, xfy, =>).
:- op(130, yfx, \/).
:- op(120, yfx, &).
:- op(110, fy,  ~).
:- op(100, fy,  all).
:- op(700, yfx, =).		    % equality
:- op(700, xfy, <>).		% different
:- op(700, xfy, @<).		% less (nat) - builtin
:- op(700, xfy, @=<).		% less than or equal (nat) - builtin
:- op(700, xfy, lte).		% less than or equal (nat)
:- op(960, yfx, <=>).
:- op(980, xfy, by).

% prove(+Phi, +V, +Name, -Lemma)
% Phi is a propositional formula
% V is a list consisting of all the
%   propositional variables of Phi
% If Phi is a tautology then Lemma
%   is a term that encodes a LPTP
%   lemma, with name Name, stating
%   Phi together with its proof.
% Otherwise, this predicate fails.
% Note that a query in prove(i,i,i,o)
% may have several (many) solutions.
prove(Phi, V, Name, lemma(Name, all V : Phi, Cases)) :-
    gen_cases(V, Phi, [], Cases).

prove_groundness_property(Phi, V, Name, Lemma) :-
    gen_cases_gr(V, Phi, [], Cases),
    Lemma = lemma(Name, all V : Phi, [
        Cases
    ]).

derive_groundness_property(Phi, V, Derivation) :-
    gen_cases_gr(V, Phi, [], Cases),
    ( ( Cases = [_|_] ; Cases = [] )
    ->  Derivation = Cases
    ;   Derivation = [Cases] ).

% gen_cases(+V, +Phi, +P, -C)
% V is a list consisting of all
% the propositional variables of
% formula Phi
% P is an input list of premises
% C is a LPTP term of the form
% cases(p,
%       [cases(q, ... D1 ..., ~q, ... D2 ..., Phi), Phi],
%       ~p,
%       [cases(q, ... D3 ..., ~q, ... D4 ..., Phi), Phi],
%       Phi)
% where [p,q,...] = V and
% D1 is a derivation of [p,  q, ... | P] |- Phi
% D2 is a derivation of [p, ~q, ... | P] |- Phi
% ...
gen_cases([], Phi, P, D) :-
    prove_with_premises(Phi, true, P, [], D).
gen_cases([A | V], Phi, L, cases(A, C1, ~ A, C2, Phi)) :-
    gen_cases(V, Phi, [A | L], C1),
    gen_cases(V, Phi, [~ A | L], C2).

gen_cases_gr([], Phi, P, D) :-
    prove_with_premises(Phi, true, P, [], D).
gen_cases_gr([A | V], Phi, L, cases(gr(?A), C1, ~ gr(?A), C2, Phi)) :-
    gen_cases_gr(V, Phi, [gr(?A) | L], C1),
    gen_cases_gr(V, Phi, [~ gr(?A) | L], C2).

disjunction_cases(Phi1, Cases) :-
    Phi1 \= (_ \/ _),
    (   Phi1 = ~ Form
    ->  Cases = [case(Phi1, [Phi1, Form, ff])]
    ;   Cases = [case(Phi1, [Phi1, ~ Phi1, ff])] ).

disjunction_cases(Phi1 \/ Phi2, Cases) :-
    (   Phi2 = ~ Form
    ->  Case = case(Phi2, [Phi2, Form, ff])
    ;   Case = case(Phi2, [Phi2, ~ Phi2, ff])),
    disjunction_cases(Phi1, CasesL),
    Cases = [Case|CasesL].

by_cases(Phi1 \/ Phi2, Cases) :-
    disjunction_cases(Phi1 \/ Phi2, DisjunctionCases),
    Cases = cases(DisjunctionCases, ff).

or_neg_gr_list([], []).
or_neg_gr_list([Var], gr(Var)).
or_neg_gr_list([Var|Vars], OrList) :-
    \+ (Var = []),
    or_neg_gr_list(Vars, OrListRest),
    ( OrListRest = []
    ->  OrList = ~ gr(Var)
    ;   OrList = ~ gr(Var) \/ OrListRest ).

and_pos_gr_list([], []).
and_pos_gr_list([Var], gr(Var)).
and_pos_gr_list([Var|Vars], AndList) :-
    \+ (Var = []),
    and_pos_gr_list(Vars, AndListRest),
    ( AndListRest = []
    -> AndList = gr(Var)
    ; AndList = gr(Var) & AndListRest ).

% Apply de Morgan law to axiom II.5 (The theoretical foundations of LPTP (a logic program theorem prover))
% X is a term
% Y is a term
% ByLemma is an equivalence derived from axiom II.5
by_axiom_2_5(X,Y,false,ByLemma) :-
    (   is_compound_form_except_list_question_mark(Y)
    ->
        Y =.. [_|YArgs],
        or_neg_gr_list(YArgs, YORList)
    ;   YORList = ~ gr(Y) ),

    ByLemma = ((~gr([X|Y]) <=> ~ gr(X) \/ YORList) by lemma(axiom_2_5_de_morgan)).

by_axiom_2_5(X,Y,true,ByLemma) :-
    (   is_compound_form_except_list_question_mark(Y)
    ->
        Y =.. [_|YArgs],
        and_pos_gr_list(YArgs, YAndList)
    ;   YAndList = gr(Y) ),

    ByLemma = ((gr([X|Y]) <=> gr(X) & YAndList) by lemma(axiom_2_5)).

by_contraposition(X,Y,D1,D2) :-
    D2 = [
        gr([X|Y]) => gr(X) & gr(Y)|[assume(
            ~ (gr(X) & gr(Y)),
            contra(
                gr([X|Y]),
                [gr(X) & gr(Y), ff]
            ),
            ~ gr([X|Y])
        )|D1]
    ].

gr_implication(Compound, Args, D1, [Impl|[Proof|D1]]) :-
    into_gr_conjunction(Args, Conjunction),
    Impl = Conjunction => gr(Compound),
    Proof = assume(~ gr(Args), contra(gr(Compound), [gr(Compound), gr(Args),ff]), ~ gr(Compound)).

    into_gr_conjunction([], _Conjunction) :- fail.
    into_gr_conjunction([Arg|Args], Conjunction) :-
        into_gr_conjunction(Args, ConjunctsRest)
        -> Conjunction = gr(Arg) & ConjunctsRest
        ;  Conjunction = gr(Arg).

is_compound_form_except_list_question_mark(Form) :-
    compound(Form),
    Form \= ?(_),
    Form \= [?_|?_],
    \+ is_list(Form).

% prove_with_premises(+Phi, +B, +P, +D1, -D2)
% Phi is a propositional formula
% B is true or false
% P is a list of premises
% D1 is the input  derivation (a list of LPTP terms)
% D2 is the output derivation (a list of LPTP terms)
% If B is true  then proves that P |- Phi.
% If B is false then proves that P |- ~ Phi.
%
% Proof of Prop. 1.38, case 1 (propositional variables):
prove_with_premises(A, true, P, D, D) :-
    % We check whether A is a premise.
    % atom(A),
    member(A, P).
prove_with_premises(A, false, P, D, D) :-
    % We check whether ~ A is a premise.
    % atom(A),
    member(~ A, P).

% see Axiom II.4 from The theoretical foundations of LPTP (a logic program theorem prover)
prove_with_premises(~ gr([]), false, _P, D, D).
prove_with_premises(gr([]), true, _P, D, D).

prove_with_premises(~ gr([X]), true, P, D1, D2) :-
    \+ is_compound_form_except_list_question_mark(X),
    prove_with_premises(~gr(X), true, P, [~gr([X]) <=> ~ gr(X) by lemma(axiom_2_5_single_element_list_de_morgan)|D1], D2).

prove_with_premises(~ gr([X]), false, P, D1, D2) :-
    \+ is_compound_form_except_list_question_mark(X),
    prove_with_premises(~gr(X), false, P, [gr([X]) <=> gr(X) by lemma(axiom_2_5_single_element_list)|D1], D2).

prove_with_premises(gr([X]), true, P, D1, D2) :-
    \+ is_compound_form_except_list_question_mark(X),
    prove_with_premises(gr(X), true, P, [gr([X]) <=> gr(X) by lemma(axiom_2_5_single_element_list)|D1], D2).

prove_with_premises(gr([X]), false, P, D1, D2) :-
    \+ is_compound_form_except_list_question_mark(X),
    prove_with_premises(gr(X), false, P, [~gr([X]) <=> ~ gr(X) by lemma(axiom_2_5_single_element_list_de_morgan)|D1], D2).

prove_with_premises(~ gr([X|Y]), true, P, D1, D2) :-
    by_axiom_2_5(X,Y,false,ByLemma),
    prove_with_premises(~gr(X) \/ ~gr(Y), true, P, [ByLemma|D1], D2).
prove_with_premises(~ gr([X|Y]), false, P, D1, D2) :-
    by_axiom_2_5(X,Y,false,ByLemma),
    prove_with_premises(~gr(X) \/ ~gr(Y), false, P, [ByLemma|D1], D2).

prove_with_premises(gr([X|Y]), true, P, D1, D2) :-
    by_axiom_2_5(X,Y,true,ByLemma),
    by_contraposition(X,Y,[ByLemma|D1],D3),
    prove_with_premises(gr(X) & gr(Y), true, P, D3, D2).
prove_with_premises(gr([X|Y]), false, P, D1, D2) :-
    by_axiom_2_5(X,Y,true,ByLemma),
    by_contraposition(X,Y,[ByLemma|D1],D3),
    prove_with_premises(gr(X) & gr(Y), false, P, D3, D2).

prove_with_premises(gr(Atom), true, _P, D, D) :-
    atomic(Atom).
prove_with_premises(~ gr(Atom), false, _P, D, D) :-
    atomic(Atom).

prove_with_premises(gr(Form), true, P, D1, D2) :-
    is_compound_form_except_list_question_mark(Form),
    Form =.. [_|Args],
    gr_implication(Form, Args, D1, D3),
    prove_with_premises(gr(Args), true, P, D3, D2).
prove_with_premises(gr(Form), false, P, D1, D2) :-
    is_compound_form_except_list_question_mark(Form),
    Form =.. [_|Args],
    gr_implication(Form, Args, D1, D3),
    prove_with_premises(gr(Args), false, P, D3, D2).
prove_with_premises(~ gr(Form), true, P, D1, D2) :-
    is_compound_form_except_list_question_mark(Form),
    Form =.. [_|Args],
    gr_implication(Form, Args, D1, D3),
    prove_with_premises(~ gr(Args), true, P, D3, D2).
prove_with_premises(~ gr(Form), false, P, D1, D2) :-
    is_compound_form_except_list_question_mark(Form),
    Form =.. [_|Args],
    gr_implication(Form, Args, D1, D3),
    prove_with_premises(~ gr(Args), false, P, D3, D2).

%
% Proof of Prop. 1.38, case 2 (Phi = ~ Phi1):
prove_with_premises(~ Phi1, true, P, D1, D2) :-
    prove_with_premises(Phi1, false, P, D1, D2).
prove_with_premises(~ Phi1, false, P, D1, D2) :-
    prove_with_premises(Phi1, true, P,
                        [contra(~ Phi1, []), ~ ~ Phi1 | D1],
                        D2).

prove_with_premises(Phi1 <=> Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi1 => Phi2, true, P, D1, D3),
    prove_with_premises(Phi2 => Phi1, true, P, [Phi1 => Phi2|[Phi2 => Phi1|D3]], D2).
prove_with_premises(Phi1 <=> Phi2, false, P, D1, D2) :-
    prove_with_premises(~ ( Phi1 => Phi2 ) \/ ~ ( Phi2 => Phi1), true, P, D1, D2).

%
% Proof of Prop. 1.38, case 3 (Phi = (Phi1 => Phi2)):
prove_with_premises(Phi1 => Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi1, false, P, [assume(Phi1, [], Phi2) | D1], D2).
prove_with_premises(Phi1 => Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi2, true, P, [assume(Phi1, [], Phi2) | D1], D3),
    prove_with_premises(Phi1, true, P, D3, D2).
prove_with_premises(Phi1 => Phi2, false, P, D1, D2) :-
    Contra = contra(Phi1 => Phi2, [Phi1, Phi2, ~Phi2, ff]),
    prove_with_premises(Phi2, false, P,
                        [Contra, ~ (Phi1 => Phi2) | D1],
                        D3),
    prove_with_premises(Phi1, true,  P, D3, D2).


prove_with_premises(Phi1 & Phi2, false, P, D1, D2) :-
    ( Phi2 = gr(Form) ; Phi2 = ~ gr(Form) ),
    is_compound_form_except_list_question_mark(Form),

    (   Phi2 = gr(Form)
    ->  prove_with_premises(Phi2, false, P,
                            [contra(Phi1 & Phi2, [Phi2,~Phi2,ff]), ~ (Phi1 & Phi2) | D1],
                            D2)
    ;   prove_with_premises(Phi2, false, P,
                                    [contra(Phi1 & Phi2, [Phi2,gr(Form),ff]), ~ (Phi1 & Phi2) | D1],
                                    D2)) .

prove_with_premises(Phi1 & Phi2, false, P, D1, D2) :-
    (
        ( Phi2 = gr([X]),
        Form = [X] )
    ;
        ( Phi2 = ~ gr([X]),
        Form = [X] )
    ;
        ( Phi2 = gr([X|Y]),
        Form = [X|Y] )
    ;
        ( Phi2 = ~ gr([X|Y]),
        Form = [X|Y] )
    )
    ->  prove_with_premises(Phi2, false, P,
                            [contra(Phi1 & Phi2, [gr(Form),~ gr(Form),ff]), ~ (Phi1 & Phi2) | D1],
                            D2)
    ;   Phi2 = ~ gr(X),
        atomic(X),
        prove_with_premises(Phi2, false, P,
                            [contra(Phi1 & Phi2, [gr(X),ff]), ~ (Phi1 & Phi2) | D1],
                            D2)
    ;
        prove_with_premises(Phi2, false, P,
                            [contra(Phi1 & Phi2, []), ~ (Phi1 & Phi2) | D1],
                            D2).

%
% Proof of Prop. 1.38, case 4 (Phi = (Phi1 & Phi2)):
prove_with_premises(Phi1 & Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi2, true, P, [Phi1 & Phi2 | D1], D3),
    prove_with_premises(Phi1, true, P, D3, D2).
prove_with_premises(Phi1 & Phi2, false, P, D1, D2) :-
    Phi1 = ~ Form
    ->
        prove_with_premises(Phi1, false, P,
                            [contra(Phi1 & Phi2, [Form,Phi1,ff]), ~ (Phi1 & Phi2) | D1],
                            D2)
    ;
        prove_with_premises(Phi1, false, P,
                            [contra(Phi1 & Phi2, [Phi1,~Phi1,ff]), ~ (Phi1 & Phi2) | D1],
                            D2).

% Proof of Prop. 1.38, case 5 (Phi = (Phi1 \/ Phi2)):
prove_with_premises(Phi1 \/ Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi1, true, P, [Phi1 \/ Phi2 | D1], D2).
prove_with_premises(Phi1 \/ Phi2, true, P, D1, D2) :-
    prove_with_premises(Phi2, true, P, [Phi1 \/ Phi2 | D1], D2).
prove_with_premises(Phi1 \/ Phi2, false, P, D1, D2) :-
    by_cases(Phi1 \/ Phi2, Cases),

%    Cases  = cases(Phi1, [], Phi2, [], ff),
    Contra = contra(Phi1 \/ Phi2, Cases),
    prove_with_premises(Phi2, false, P,
                        [Contra, ~ (Phi1 \/ Phi2) | D1],
                        D3),
    prove_with_premises(Phi1, false, P, D3, D2).
