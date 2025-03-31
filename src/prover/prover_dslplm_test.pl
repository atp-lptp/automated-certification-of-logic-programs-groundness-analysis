:- use_module(prover_dslplm_test).

:- set_prolog_flag(plunit_output, always).
:- use_module(library(prolog_stack)).
:- use_module(prover_dslplm).
:- use_module(dn_prover).
:- debug.

:- use_module(mod_lptp).
:- use_module('../lptp', [
    prt__write/1
]).

:- op(100, fy,  ?).
:- op(150, xfy, :).
:- op(140, xfy, =>).
:- op(130, yfx, \/).
:- op(120, yfx, &).
:- op(110, fy,  ~).
:- op(100, fy,  all).
:- op(700, yfx, =).		    % equality
:- op(700, xfy, <>).		% different
:- op(700, xfy, @<).		% less (nat) - builtin in SWI-Prolog
:- op(700, xfy, @=<).		% less than or equal (nat) - builtin in SWI-Prolog
:- op(700, xfy, lte).		% less than or equal (nat)
:- op(900, fy,  succeeds).
:- op(900, fy,  fails).
:- op(960, yfx, <=>).
:- op(980, xfy, by).

:- begin_tests(app).

test(append_base_case) :-
    A = (gr(?x4) & gr(?x4) & gr([]) \/
        (gr(?x4) => ff) & gr(?x4) & (gr([]) => ff) \/
        (gr(?x4) => ff) & (gr(?x4) => ff) & gr([]) \/
        (gr(?x4) => ff) & (gr(?x4) => ff) & (gr([]) => ff)),
    once(dn_prover:proof(
        [],
        A,
        Proof
    )).
%    once(dn_prover:proof([], A, Proof)),
%    gensym(l, L),
%    lptp:lemma(
%        L,
%        all [x4]: A,
%        Proof
%    ).

:- end_tests(app).

%:- begin_tests(case_1).
%
%test(case_1_a) :-
%    Gamma = [ff],
%    once(prove(Gamma, A, Proof)),
%    Proof = [ff,A].
%
%test(case_1_b_1) :-
%    Gamma = [gr(?Var)|[~ gr(?Var)]],
%    A = ff,
%    once(prove(Gamma, A, Proof)),
%    Proof = [gr(?_),~gr(?_),ff].
%
%test(case_1_b_2_a) :-
%    Gamma = [gr(?Var)|[~ gr(?Var)]],
%    A = gr(?Var2),
%    dif(Var2, Var),
%    once(prove(Gamma, A, Proof)),
%    Proof = [gr(?_),~gr(?_),ff,A].
%
%test(case_1_b_2_a) :-
%    Gamma = [gr(?Var)|[~ gr(?Var)]],
%    A = (~ gr(?Var2)),
%    dif(Var2, Var),
%    once(prove(Gamma, A, Proof)),
%    Proof = [gr(?_),~gr(?_),ff,A].
%
%test(case_1_b_2_b) :-
%    Gamma = [gr(?Var)],
%    A = gr(?Var),
%    once(prove(Gamma, A, Proof)),
%    Proof = [].
%
%test(case_1_b_2_b) :-
%    Gamma = [~ gr(?Var)],
%    A = (~ gr(?Var)),
%    once(prove(Gamma, A, Proof)),
%    Proof = [].
%
%:- end_tests(case_1).
%
%:- begin_tests(case_2).
%
%%   m(B & C, MA)
%%   m(B => C, MA)
%%   m(B \/ C, MA)
%
%%   m(A, MA)
%%   m(B, MB)
%%   m(C, MC)
%%   MA #> MB + MC
%
%test(case_2_a) :-
%    B = gr(?x0),
%    C = (~gr(?x1)),
%    A = (B & C),
%    Gamma = [gr(?x0),~ gr(?x1)],
%    once(prove(Gamma, B, BProof)),
%    once(prove(Gamma, C, CProof)),
%    once(prove(Gamma, A, ActualProof)),
%
%    append(
%        [BProof,
%        CProof,
%        [A]],
%        Proof
%    ),
%    assertion(ActualProof = Proof).
%
%test(case_2_b) :-
%    B = gr(?x1),
%    C = gr(?x1),
%    A = (B => C),
%    Gamma = [],
%    once(prove([B|Gamma], C, CProof)),
%    once(prove(Gamma, A, ActualProof)),
%
%    Proof = [
%        assume(
%            B,
%            CProof,
%            C
%        ),
%        A
%    ],
%    assertion(ActualProof = Proof).
%
%test(case_2_c) :-
%    B = gr(?x1),
%    C = gr(?x2),
%
%    A = (B \/ C),
%
%    Gamma = [gr(?x2),gr(?x1)],
%    once(prove([~ B|Gamma], C, P)),
%    once(prove_p1([~ B => C|Gamma], B \/ C, P1)),
%
%    once(prove(Gamma, A, ActualProof)),
%
%    Proof = [
%        assume(
%            ~ B,
%            P,
%            C
%        ),
%        assume(
%            ~ B => C,
%            P1,
%            B \/ C
%        ),
%        A
%    ],
%    assertion(ActualProof = Proof),
%
%    gensym(l,L),
%    mod_lptp:lemma(
%        L,
%        all [x1,x2]: (~ B => C) => (B \/ C),
%        P1
%     ).
%
%:- end_tests(case_2).
%
%:- begin_tests(case_3).
%
%test(case_3_f) :-
%    B = gr(?x1) & gr(?x2),
%    C = gr(?x3),
%
%    A = (B & C),
%
%    Gamma = [gr(?x1), gr(?x2) & gr(?x3)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        gr(?x2),gr(?x3),gr(?x2)&gr(?x3),
%        gr(?x2),gr(?x3),gr(?x2)&gr(?x3),
%        gr(?x1)&gr(?x2),gr(?x2),gr(?x3),
%        gr(?x2)&gr(?x3),gr(?x1)&gr(?x2)&gr(?x3)
%    ]).
%
%test(case_3_g) :-
%    B = gr(?x3),
%    C = gr(?x2),
%
%    A = (B \/ C),
%
%    Gamma = [gr(?x1), gr(?x2) \/ gr(?x3)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        assume(~ gr(?x3),
%          [assume(gr(?x2),[],gr(?x2)),
%           gr(?x2) => gr(?x2),
%           assume(gr(?x3),
%            [gr(?x3),
%             ~ gr(?x3),
%             ff,
%             gr(?x2)],
%            gr(?x2)),
%           gr(?x3) => gr(?x2),
%           [gr(?x2)]],
%          gr(?x2)),
%         assume(~ gr(?x3) => gr(?x2),
%          [assume(~ gr(?x3) => gr(?x2),
%            [~ gr(?x3) \/ ~ ~ gr(?x3),
%             cases(~ gr(?x3),
%              [contra(~ (gr(?x3) \/ gr(?x2)),
%                [assume(~ gr(?x3),[gr(?x2)],gr(?x2)),
%                 gr(?x2),
%                 gr(?x3) \/ gr(?x2)])],
%              ~ ~ gr(?x3),
%              [indirect(~ gr(?x3),[gr(?x3),~ gr(?x3),ff])],
%              gr(?x3) \/ gr(?x2)),
%             gr(?x3) \/ gr(?x2)],
%            gr(?x3) \/ gr(?x2))],
%          gr(?x3) \/ gr(?x2)),
%         gr(?x3) \/ gr(?x2)
%    ]).
%
%test(case_3_h) :-
%    B = gr(?x2),
%    C = gr(?x3) & gr(?x1),
%
%    A = (B => C),
%
%    Gamma = [gr(?x2) => gr(?x3) & gr(?x1)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        assume(gr(?x2),
%          [assume(gr(?x2) => gr(?x3) & gr(?x1),
%            [cases(~ gr(?x2),
%              assume(~ gr(?x2),
%               [~ gr(?x2) \/ gr(?x3) & gr(?x1)],
%               ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%              gr(?x2),
%              assume(gr(?x3) & gr(?x1),
%               [~ gr(?x2) \/ gr(?x3) & gr(?x1)],
%               ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%              ~ gr(?x2) \/ gr(?x3) & gr(?x1))],
%            ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%           assume(~ gr(?x2),
%            [gr(?x2),
%             ~ gr(?x2),
%             ff,
%             gr(?x3)],
%            ~ gr(?x2) => gr(?x3)),
%           assume(gr(?x3) & gr(?x1),
%            [gr(?x3),
%             gr(?x1),
%             gr(?x3) & gr(?x1)],
%            gr(?x3) & gr(?x1) => gr(?x3)),
%           gr(?x3),
%           assume(gr(?x2) => gr(?x3) & gr(?x1),
%            [cases(~ gr(?x2),
%              assume(~ gr(?x2),
%               [~ gr(?x2) \/ gr(?x3) & gr(?x1)],
%               ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%              gr(?x2),
%              assume(gr(?x3) & gr(?x1),
%               [~ gr(?x2) \/ gr(?x3) & gr(?x1)],
%               ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%              ~ gr(?x2) \/ gr(?x3) & gr(?x1))],
%            ~ gr(?x2) \/ gr(?x3) & gr(?x1)),
%           assume(~ gr(?x2),
%            [gr(?x2),
%             ~ gr(?x2),
%             ff,
%             gr(?x1)],
%            ~ gr(?x2) => gr(?x1)),
%           assume(gr(?x3) & gr(?x1),
%            [gr(?x3),
%             gr(?x1),
%             gr(?x3) & gr(?x1)],
%            gr(?x3) & gr(?x1) => gr(?x1)),
%           gr(?x1),
%           gr(?x3) & gr(?x1)],
%          gr(?x3) & gr(?x1)),
%         gr(?x2) => gr(?x3) & gr(?x1)
%    ])
%.
%
%test(case_3_i) :-
%    B = gr(?x2),
%    C = gr(?x3),
%
%    A = (~ B \/ ~ C),
%
%    Gamma = [~ (gr(?x2) & gr(?x3)), ~gr(?x2),~gr(?x3),gr(?x1)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        assume(~ ~ gr(?x2),
%          [assume(~ (gr(?x2) & gr(?x3)),
%            indirect(~ (~ gr(?x2) \/ ~ gr(?x3)),
%             [indirect(~ gr(?x2),[~ gr(?x2) \/ ~ gr(?x3),ff]),
%              indirect(~ gr(?x3),
%               [~ gr(?x2) \/ ~ gr(?x3),
%                ff]),
%              gr(?x2) & gr(?x3),
%              ff]),
%            ~ gr(?x2) \/ ~ gr(?x3)),
%           assume(~ gr(?x2),[],
%            ~ gr(?x2) => ~ gr(?x3)),
%           assume(~ gr(?x3),[],
%            ~ gr(?x3) => ~ gr(?x3)),
%           ~ gr(?x3)],
%          ~ gr(?x3)),
%         assume(~ ~ gr(?x2) => ~ gr(?x3),
%          [assume(~ ~ gr(?x2) => ~ gr(?x3),
%            [~ ~ gr(?x2) \/ ~ ~ ~ gr(?x2),
%             cases(~ ~ gr(?x2),
%              [contra(~ (~ gr(?x2) \/ ~ gr(?x3)),
%                [assume(~ ~ gr(?x2),[~ gr(?x3)],~ gr(?x3)),
%                 ~ gr(?x3),
%                 ~ gr(?x2) \/ ~ gr(?x3)])],
%              ~ ~ ~ gr(?x2),
%              [indirect(~ ~ gr(?x2),[~ gr(?x2),~ ~ gr(?x2),ff])],
%              ~ gr(?x2) \/ ~ gr(?x3)),
%             ~ gr(?x2) \/ ~ gr(?x3)],
%            ~ gr(?x2) \/ ~ gr(?x3))],
%          ~ gr(?x2) \/ ~ gr(?x3)),
%         ~ gr(?x2) \/ ~ gr(?x3)
%    ]).
%
%test(case_3_j) :-
%    B = gr(?x2),
%    C = gr(?x3),
%
%    A = (~ B & ~ C),
%
%    Gamma = [~ (gr(?x2) \/ gr(?x3)), ~gr(?x2),~gr(?x3),gr(?x1)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        assume(~ (gr(?x2) \/ gr(?x3)),
%          contra(gr(?x2),
%           [gr(?x2) \/ gr(?x3),
%            ff]),
%          ~ gr(?x2)),
%         assume(~ (gr(?x2) \/ gr(?x3)),
%          contra(gr(?x3),
%           [gr(?x2) \/ gr(?x3),
%            ff]),
%          ~ gr(?x3)),
%         ~ gr(?x2),
%         assume(~ (gr(?x2) \/ gr(?x3)),
%          contra(gr(?x2),
%           [gr(?x2) \/ gr(?x3),
%            ff]),
%          ~ gr(?x2)),
%         assume(~ (gr(?x2) \/ gr(?x3)),
%          contra(gr(?x3),
%           [gr(?x2) \/ gr(?x3),
%            ff]),
%          ~ gr(?x3)),
%         ~ gr(?x3),
%         ~ gr(?x2) & ~ gr(?x3)
%    ]).
%
%test(case_3_k) :-
%    B = gr(?x2),
%    C = gr(?x3),
%
%    A = (B & ~ C),
%
%    Gamma = [~ (gr(?x2) => gr(?x3)), gr(?x2),~gr(?x3),gr(?x1)],
%    once(prove(Gamma, A, ActualProof)),
%
%    assertion(ActualProof = [
%        gr(?x2)& ~gr(?x3)
%    ]).
%
%:- end_tests(case_3).
%
%:- begin_tests(decomposability).
%
%test(form_decomposability) :-
%    setof(A, undecomposable_form(A), L),
%    assertion(L = [ff, gr(_), ~gr(_)]).
%
%test(gamma_decomposability) :-
%    \+ undecomposable_gamma([_ => _]).
%test(gamma_decomposability) :-
%    \+ undecomposable_gamma([_ <=> _]).
%test(gamma_decomposability) :-
%    \+ undecomposable_gamma([_ \/ _]).
%test(gamma_decomposability) :-
%    \+ undecomposable_gamma([_ & _]).
%test(gamma_decomposability) :-
%    once(undecomposable_gamma([ff])).
%
%:- end_tests(decomposability).
%
%:- begin_tests(measure).
%
%test(measure) :-
%    once(m(ff, M)),
%    assertion(M=0).
%
%test(measure) :-
%    once(m(gr(?x0), M)),
%    assertion(M=1).
%
%test(measure) :-
%    once(m(~ gr(?x0), M)),
%    assertion(M=2).
%
%test(measure) :-
%    once(m(gr([?x0]), M)),
%    assertion(M=1).
%
%test(measure) :-
%    once(m(~ gr([?x0]), M)),
%    assertion(M=2).
%
%test(measure) :-
%    once(m(gr(s(?x0)), M)),
%    assertion(M=1).
%
%test(measure) :-
%    once(m(~ gr(s(?x0)), M)),
%    assertion(M=2).
%
%test(measure) :-
%    once(m(gr([?x0|?x1]), M)),
%    assertion(M=3).
%
%test(measure) :-
%    once(m(~ gr([?x0|?x1]), M)),
%    assertion(M=5).
%
%test(measure) :-
%    once(m(gr([?x0,?x1|?x2]), M)),
%    assertion(M=5).
%
%test(measure) :-
%    once(m(gr(?x0) & gr(?x1), M)),
%    assertion(M=3).
%
%test(measure) :-
%    once(m(~ gr(?x0) & ~ gr(?x1), M)),
%    assertion(M=5).
%
%test(measure) :-
%    once(m(gr(?x0) & gr(?x1) & gr(?x2), M)),
%    assertion(M=5).
%
%test(measure) :-
%    once(m(gr(?x0) & gr(?x1) & gr(?x2) & gr(?x3), M)),
%    assertion(M=7).
%
%test(measure) :-
%    once(m(~ gr(?x0) & gr(?x1) & gr(?x2) & gr(?x3), M)),
%    assertion(M=8).
%
%test(measure) :-
%    once(m(~ gr(?x0) & gr(?x1) & ~ gr(?x2) & gr(?x3), M)),
%    assertion(M=9).
%
%test(measure) :-
%    once(m(~ gr(?x0) & ~ gr(?x1) & ~ gr(?x2) & gr(?x3), M)),
%    assertion(M=10).
%
%test(measure) :-
%    once(m(gr(?x0) & ~ gr(?x1) & ~ gr(?x2) & gr(?x3), M)),
%    assertion(M=9).
%
%test(measure) :-
%    once(m(~ gr(?x0) & ~ gr(?x1) & ~ gr(?x2) & ~ gr(?x3), M)),
%    assertion(M=11).
%
%test(measure) :-
%    once(m(gr(?x0) \/ gr(?x1), M)),
%    assertion(M=4).
%
%test(measure) :-
%    once(m(gr(?x0) \/ gr(?x1) \/ gr(?x2), M)),
%    assertion(M=7).
%
%test(measure) :-
%    once(m(gr(?x0) \/ gr(?x1) \/ gr(?x2) \/ gr(?x3), M)),
%    assertion(M=10).
%
%test(measure) :-
%    once(m(gr(?x0) \/ ~ gr(?x1) \/ gr(?x2) \/ gr(?x3), M)),
%    assertion(M=11).
%
%test(measure) :-
%    once(m(gr(?x0) \/ ~ gr(?x1) \/ gr(?x2) \/ ~ gr(?x3), M)),
%    assertion(M=12).
%
%test(measure) :-
%    once(m(~ gr(?x0) \/ ~ gr(?x1), M)),
%    assertion(M=6).
%
%test(measure) :-
%    once(m(gr(?x0) => gr(?x0), M)),
%    assertion(M=3).
%
%test(measure) :-
%    once(m(~ gr(?x0) \/ ~ gr(?x1) \/ gr(?x2) \/ ~ gr(?x3) =>
%        ~ gr(?x0) \/ ~ gr(?x1) \/ gr(?x2) \/ ~ gr(?x3), M)),
%    assertion(M=27).
%
%test(measure) :-
%    once(m(~ gr(t(?x0)) => ~ gr(t(?x0)) => ~ gr(t(?x0)), M)),
%    assertion(M=8).
%
%:- end_tests(measure).
