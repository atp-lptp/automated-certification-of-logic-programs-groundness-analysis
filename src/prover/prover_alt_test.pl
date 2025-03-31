:- use_module('./prover_alt').
:- use_module('./prover_dslplm').
:- use_module('./dn_prover').
:- use_module('../prover/prover').
:- use_module('../lptp').
:- set_prolog_flag(plunit_output, always).
:- use_module(library(prolog_stack)).
:- debug.

load_operators :-
    op(100, fy,  ?),
    op(150, xfy, :),
    op(140, xfy, =>),
    op(130, yfx, \/),
    op(120, yfx, &),
    op(110, fy,  ~),
    op(100, fy,  all),
    op(700, yfx, =),		% equality
    op(700, xfy, <>),		% difference
    op(700, xfy, @<),		% less (nat) - builtin in SWI-Prolog
    op(700, xfy, @=<),		% less than or equal (nat) - builtin in SWI-Prolog
    op(700, xfy, lte),		% less than or equal (nat)
    op(900, fy,  succeeds),
    op(900, fy,  fails),
    op(960, yfx, <=>),
    op(980, xfy, by).

:- load_operators.

%:- begin_tests(_induction_step).

%test() :-
%    A =
%    Gamma =
%    once(proof(Gamma, A, Proof)),
%    prt__write(Proof),
%    assertion(Proof = []).

%:- end_tests(_induction_step).

:- begin_tests(list_induction_step).

test(list_base_case) :-
    A = gr([?x3|?x4])&gr(?x3)\/ ~gr([?x3|?x4])&gr(?x3)\/ ~gr([?x3|?x4])& ~gr(?x3),
    expand_gr(A, ExpandedTerm),
    assertion(ExpandedTerm = gr(?x4)&gr(?x3)&gr(?x3)\/(~gr(?x4)\/ ~gr(?x3))&gr(?x3)\/(~gr(?x4)\/ ~gr(?x3))& ~gr(?x3)),
%    prover_dslplm:prove([], ExpandedTerm, Proof),
    prover_alt:proof([], ExpandedTerm, Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x3,x4]: ExpandedTerm,
        Proof
    ).

%test(list_induction_step) :-
%    A = gr(?x9)&gr(?x8)&gr(?x6)\/ ~gr(?x9)& ~gr(?x8)&gr(?x6)\/gr(?x9)& ~gr(?x8)& ~gr(?x6)\/ ~gr(?x9)& ~gr(?x8)& ~gr(?x6)=>gr([?x7|?x9])&gr([?x7|?x8])&gr(?x6)\/ ~gr([?x7|?x9])& ~gr([?x7|?x8])&gr(?x6)\/gr([?x7|?x9])& ~gr([?x7|?x8])& ~gr(?x6)\/ ~gr([?x7|?x9])& ~gr([?x7|?x8])& ~gr(?x6),
%    expand_gr(A, ExpandedTerm),
%    assertion(ExpandedTerm = gr(?x9) & gr(?x8) & gr(?x6) \/ ~ gr(?x9) & ~ gr(?x8) & gr(?x6) \/
%                             gr(?x9) & ~ gr(?x8) & ~ gr(?x6) \/ ~ gr(?x9) & ~ gr(?x8) & ~ gr(?x6) =>
%                              gr(?x9) & gr(?x7) & (gr(?x8) & gr(?x7)) & gr(?x6) \/
%                              (~ gr(?x9) \/ ~ gr(?x7)) & (~ gr(?x8) \/ ~ gr(?x7)) & gr(?x6) \/
%                              gr(?x9) & gr(?x7) & (~ gr(?x8) \/ ~ gr(?x7)) & ~ gr(?x6) \/
%                              (~ gr(?x9) \/ ~ gr(?x7)) & (~ gr(?x8) \/ ~ gr(?x7)) & ~ gr(?x6)),
%    once(prover_alt:proof([], A, Proof)),
%%    prover_alt:proof([], ExpandedTerm, Proof),
%    gensym(l, L),
%    lptp:lemma(
%        L,
%        all [x6,x7,x8,x9]: ExpandedTerm,
%        Proof
%    ).

%test(delete_induction_step) :-
%    A = gr([?x7|?x9]) & gr([?x7|?x8]) & gr(?x6) \/
%            ~ gr([?x7|?x9]) & ~ gr([?x7|?x8]) & gr(?x6) \/
%            gr([?x7|?x9]) & ~ gr([?x7|?x8]) & ~ gr(?x6) \/
%            ~ gr([?x7|?x9]) & ~ gr([?x7|?x8]) & ~ gr(?x6),
%
%    expand_gr(A, ExpandedTerm),
%
%    assertion(ExpandedTerm = gr(?x9) & gr(?x7) & (gr(?x8) & gr(?x7)) & gr(?x6) \/
%                             (~ gr(?x9) \/ ~ gr(?x7)) & (~ gr(?x8) \/ ~ gr(?x7)) & gr(?x6) \/
%                             gr(?x9) & gr(?x7) & (~ gr(?x8) \/ ~ gr(?x7)) & ~ gr(?x6) \/
%                             (~ gr(?x9) \/ ~ gr(?x7)) & (~ gr(?x8) \/ ~ gr(?x7)) & ~ gr(?x6)),
%
%    Gamma = [
%        gr(?x9) & gr(?x8) & gr(?x6) \/ ~ gr(?x9) & ~ gr(?x8) & gr(?x6) \/
%        gr(?x9) & ~ gr(?x8) & ~ gr(?x6) \/ ~ gr(?x9) & ~ gr(?x8) & ~ gr(?x6)
%    ],
%    Gamma = [Hyp0],
%%    once(proof(Gamma, (Hyp0 & Hyp1 & Hyp2 & Hyp3 & Hyp4) => A, Proof)).
%    once(prover_dslplm:prove(Gamma, ExpandedTerm, Proof)),
%%    prt__write(Proof)
%    gensym(l, L),
%    lptp:lemma(
%       L,
%       all [x6,x7,x8,x9]: Hyp0 => (A),
%       Proof
%    ).

:- end_tests(list_induction_step).

:- begin_tests(less).

test(less_base_case) :-
    A = gr(s(?x3)) & gr(0) \/ (~ gr(s(?x3))) & gr(0),
    Gamma = [],
    once(proof(Gamma, A, Proof)),
    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all x3: A,
        Proof
    ).

test(less_induction_step) :-
    A = gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)),
    Gamma = [gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4)],
    [Hyp] = Gamma,
    once(proof(Gamma, Hyp => A, Proof)),
    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x4,x5]: Hyp => A,
        Proof
    ).

:- end_tests(less).

:- begin_tests(member_base_case).

test(member_base_case) :-
    A = ( gr([?x3|?x4]) & gr(?x3) \/ ~ gr([?x3|?x4]) & gr(?x3) \/
              ~ gr([?x3|?x4]) & ~ gr(?x3)),

    once(proof([], A, Proof)),

    gensym(l, L),
    lptp:lemma(
       L,
       all [x3,x4]: A,
       Proof
    ).

test(member_induction_step) :-
    Gamma = [( gr(?x7) & gr(?x5) \/ ~ gr(?x7) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x5) )],
    Gamma = [Hyp],
    A = gr([?x6|?x7]) & gr(?x5) \/ (~ gr([?x6|?x7])) & gr(?x5) \/
            (~ gr([?x6|?x7])) & ~ gr(?x5),

    once(proof([], Hyp => A, Proof)),
%    prt__write(Proof),
    gensym(l, L),
    lptp:lemma(L,
        all [x5,x6,x7]: Hyp => A,
        Proof
    ).

test(length_base_case) :-
    A = gr(0) & gr([]) \/ gr(0) & ~ gr([]),
    once(proof([], A, Proof)),
    gensym(l, L),
    lptp:lemma(
       L,
       A,
       Proof
    ).

test(length_induction_step) :-
    A = gr(s(?x5)) & gr([?x3|?x4]) \/ gr(s(?x5)) & ~ gr([?x3|?x4]),
    Gamma = [gr(?x5) & gr(?x4) \/ gr(?x5) & ~ gr(?x4)],
    Gamma = [Hyp],
    once(proof([], Hyp => A, Proof)),
    gensym(l, L),
    lptp:lemma(
       L,
       all [x3,x4,x5]: Hyp => A,
       Proof
    ).

:- end_tests(member_base_case).

:- begin_tests(constant_term).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr([]),
        Proof
    )),
    assertion(Proof = [tt]),
    once(nd_proof(Gamma, gr([]), Proof)).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr(0),
        [tt]
    )),
    once(nd_proof(Gamma, gr(0), [tt])).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr(t),
        [tt]
    )),
    once(nd_proof(Gamma, gr(t), [tt])).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr(d(t)),
        [tt]
    )),
    once(nd_proof(Gamma, gr(d(t)), [tt])).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr(s(0)),
        []
    )),
    once(nd_proof(Gamma, gr(s(0)), [])).

test(constant_term) :-
    Gamma = [],
    once(proof(
        Gamma,
        gr(e),
        [tt]
    )),
    once(nd_proof(Gamma, gr(e), [tt])).

:- end_tests(constant_term).

:- begin_tests(univ_rec).

test(univ_list_rec) :-
    once(univ_list_rec(gr([-s(?x9),?x4|?x5]), Out)),
    assertion(Out = [?x9,?x4,?x5]),

    once(compound_to_conjunction(Out, Conjunction)),
    assertion(Conjunction = gr(?x9)&(gr(?x4)&gr(?x5))).

test(univ_list_rec) :-
    once(univ_list_rec(gr([-s(?x9),?x4|?x5]), Out)),
    assertion(Out = [?x9,?x4,?x5]),

    once(compound_to_conjunction(Out, Conjunction)),
    assertion(Conjunction = gr(?x9)&(gr(?x4)&gr(?x5))).

test(univ_list_rec) :-
    univ_list_rec(gr([?x4|?x5]), Out),
    assertion(Out = [?x4,?x5]).

test(univ_rec) :-
    univ_rec(gr(-s(?x9)), 1, Acc, Out),
    assertion(Acc = 2),
    assertion(Out = x9).

test(univ_acc_rec) :-
    univ_acc_rec(gr(-s(?x9)), [], Acc, Out),
    assertion(Acc = [gr(s(?x9)),gr(?x9)]),
    assertion(Out = x9).

test(neg_univ_rec) :-
    neg_univ_rec(~ gr(s(?x9)), 1, Depth, Out),
    assertion(Depth = 1),
    assertion(Out = x9).

test(neg_univ_acc_rec) :-
    neg_univ_acc_rec(~ gr(s(?x9)), [], Acc, Out),
    assertion(Acc = [~gr(?x9)]),
    assertion(Out = x9).

test(neg_univ_acc_rec) :-
    neg_univ_acc_rec(~ gr(-s(?x9)), [], Acc, Out),
    assertion(Acc = [~gr(s(?x9)),~gr(?x9)]),
    assertion(Out = x9).

test(double_neg_univ_rec) :-
    double_neg_univ_rec(~ (~ gr(-s(?x9))), 1, Depth, Out),
    assertion(Depth = 2),
    assertion(Out = x9).

test(double_neg_univ_acc_rec) :-
    double_neg_univ_acc_rec(~ (~ gr(-s(?x9))), [], Acc, Out),
    assertion(Acc = [~ ~gr(s(?x9)),~ ~gr(?x9)]),
    assertion(Out = x9).

:- end_tests(univ_rec).

:- begin_tests(deriv_induction_step).

test(deriv_base_case) :-
    A = gr(1) & gr(t) & gr(d(t)) \/ gr(1) & gr(t) & ~ gr(d(t)) \/
            ~ gr(1) & gr(t) & ~ gr(d(t)),
    Gamma = [],
    once(proof(Gamma, A, Proof)),
    gensym(l, L),
    lptp:lemma(L, A, Proof).

test(deriv_induction_step) :-
    A = gr(0) & gr(t) & gr(d(?x4)) \/ gr(0) & gr(t) & ~ gr(d(?x4)) \/
            ~ gr(0) & gr(t) & ~ gr(d(?x4)),
    Gamma = [],
    once(proof(Gamma, A, Proof)),
    gensym(l, L),
    lptp:lemma(L, all x4: A, Proof).

%test(deriv_induction_step) :-
%    Hyp1 = gr(?x7) & gr(t) & gr(d(?x5)) \/ gr(?x7) & gr(t) & (~ gr(d(?x5))) \/
%     (~ gr(?x7)) & gr(t) & (~ gr(d(?x5))),
%    Hyp2 = gr(?x8) & gr(t) & gr(d(?x6)) \/ gr(?x8) & gr(t) & (~ gr(d(?x6))) \/
%     (~ gr(?x8)) & gr(t) & (~ gr(d(?x6))),
%    A = gr(?x7 + ?x8) & gr(t) & gr(d(?x5 + ?x6)) \/
%        gr(?x7 + ?x8) & gr(t) & ~ gr(d(?x5 + ?x6)) \/
%        ~ gr(?x7 + ?x8) & gr(t) & ~ gr(d(?x5 + ?x6)),
%    once(proof([], Hyp1 & Hyp2 => A, Proof)),
%    gensym(l, L),
%    lptp:lemma(L, all [x5,x6,x7,x8]: A, Proof).

%test(deriv_induction_step) :-
%    Hyp1 = gr(?x12) & gr(t) & gr(d(?x9)) \/ gr(?x12) & gr(t) & ~ gr(d(?x9)) \/
%    ~ gr(?x12) & gr(t) & ~ gr(d(?x9)),
%    Hyp2 = gr(?x11) & gr(t) & gr(d(?x10)) \/ gr(?x11) & gr(t) & ~ gr(d(?x10)) \/
%    ~ gr(?x11) & gr(t) & ~ gr(d(?x10)),
%    A = gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & gr(d(?x9 * ?x10)) \/
%        gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & ~ gr(d(?x9 * ?x10)) \/
%        ~ gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & ~ gr(d(?x9 * ?x10)),
%    once(proof([], Hyp1 & Hyp2 => A, Proof)),
%    gensym(l, L),
%    lptp:lemma(L, all [x5,x6,x7,x8]: A, Proof).

:- end_tests(deriv_induction_step).

%:- begin_tests(reverse_induction_step).
%
%test(reverse_induction_step_part) :-
%    A = ~gr(?x8),
%    Gamma = [
%        ~gr(?x7),
%        ~ ~gr(?x8),
%        ~ ~gr(?x8),
%        gr(?x8)&gr([?x5|?x7])&gr(?x6)
%        \/ ~gr(?x8)&gr([?x5|?x7])& ~gr(?x6)
%        \/ ~gr(?x8)& ~gr([?x5|?x7])&gr(?x6)
%        \/ ~gr(?x8)& ~gr([?x5|?x7])& ~gr(?x6)],
%    [Hyp1, Hyp2, Hyp3, Hyp4] = Gamma,
%    once(proof([], Hyp1 & Hyp2 & Hyp3 & Hyp4 => A, _Proof)).
%    gensym(l, L),
%    prt__write(lptp:lemma(
%        L,
%        all [x5,x6,x7,x8]: Hyp1 & Hyp2 & Hyp3 & Hyp4 => A,
%        Proof
%    )).

%    gensym(l, L),
%    lptp:lemma(
%        L,
%        all [x5,x6,x7,x8]: Hyp => A,
%        Proof
%    ).

%test(reverse_induction_step) :-
%    A = gr(?x8)&gr(?x7)&gr([?x5|?x6])
%        \/ (~gr(?x8))&gr(?x7)& (~gr([?x5|?x6]))
%        \/ (~gr(?x8))& (~gr(?x7))&gr([?x5|?x6])
%        \/ (~gr(?x8))& (~gr(?x7))& (~gr([?x5|?x6])),
%    Gamma = [
%        gr(?x8)&gr([?x5|?x7])&gr(?x6)
%        \/ (~gr(?x8))&gr([?x5|?x7])& (~gr(?x6))
%        \/ (~gr(?x8))& (~gr([?x5|?x7]))&gr(?x6)
%        \/ (~gr(?x8))& (~gr([?x5|?x7]))& (~gr(?x6))
%    ],
%    once(proof(Gamma, A, Proof)),
%    % prt__write(Proof),
%    assertion(Proof = []).
%
%:- end_tests(reverse_induction_step).

:- begin_tests(reverse).

test(reverse_base_case) :-
    A = gr(?x4)&gr(?x4)&gr([])
        \/ (~gr(?x4))&gr(?x4)& (~gr([]))
        \/ (~gr(?x4))& (~gr(?x4))&gr([])
        \/ (~gr(?x4))& (~gr(?x4))& ~gr([]),
    Gamma = [],
    once(proof(Gamma, A, Proof)),
    %prt__write(Proof),
    gensym(l,L),
    lptp:lemma(
        L,
        all x4: A,
        Proof
    ).

:- end_tests(reverse).

:- begin_tests(minus_induction_step_part_2_induction_step).

test(minus21_part_1) :-
    A = gr(- s(?x3)) & gr(s(?x3)) \/ ~ gr(- s(?x3)) & ~ gr(s(?x3)),
    once(proof([], A, Proof)),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x3]: A,
        Proof
    ).

test(minus21_part_4) :-
    A = gr(?x4) & gr(- ?x4) \/ ~ gr(?x4) & ~ gr(- ?x4),
    once(proof([], A, Proof)),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x4]: A,
        Proof
    ).

test(minus_induction_step_part_2) :-
    A = (gr(- s(?x9)) & gr(?x8) & gr(?x7)
        \/ (~ gr(- s(?x9))) & (~ gr(?x8)) & gr(?x7)
        \/ (~ gr(- s(?x9))) & gr(?x8) & (~ gr(?x7))),

    append(
        [
            [gr(?x8) & gr(s(?x9)) & gr(?x7) \/
            (~ gr(?x8)) & (~ gr(s(?x9))) & gr(?x7)]
        ], Gamma
    ),

    [Hyp] = Gamma,
    once(proof(Gamma, Hyp => A, Proof)),
    % prt__write(Proof),

    gensym(l, L),
    lptp:lemma(
        L,
        all [x7,x8,x9]: Hyp => A,
        Proof
    ).

:- end_tests(minus_induction_step_part_2_induction_step).

:- begin_tests(minus_induction_step_part_1).

test(minus_induction_step_part_1) :-
    A = (gr(?x6) & gr(?x5) & gr(?x4) \/ (~ gr(?x6)) & (~ gr(?x5)) & gr(?x4) \/
             (~ gr(?x6)) & gr(?x5) & (~ gr(?x4))),
    Gamma = [gr(?x4) & gr(?x6) & gr(?x5) \/
                    (~ gr(?x4)) & (~ gr(?x6)) & gr(?x5)],
    Gamma = [Hyp],
    once(proof([], Hyp => A, Proof)),
    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x4,x5,x6]: Hyp => A,
        Proof
    ).

:- end_tests(minus_induction_step_part_1).

:- begin_tests(nat_induction_step).

test(nat_induction_step) :-
    A = gr(s(?x2)),
    Gamma = [gr(?x2)],
    once(proof(Gamma, A, Proof)),
    %prt__write(Proof),
    assertion(Proof = [gr(?x2)]).

:- end_tests(nat_induction_step).

:- begin_tests(negative_base_case).

test(negative) :-
    A = (gr(-(s(?x2))) \/ (~ gr(-(s(?x2))))),
    Gamma = [],
    once(proof(Gamma, A, Proof)),
    %prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x2]: A,
        Proof
    ).

:- end_tests(negative_base_case).

:- begin_tests(int_induction_step).

test(int_induction_step) :-
    A = (gr(s(?x7)) & gr(?x6) & gr(s(?x5))
        \/ (~ gr(s(?x7))) & (~ gr(?x6)) & gr(s(?x5))),
    Gamma = [gr(?x7) & gr(?x6) & gr(?x5) \/ (~ gr(?x7)) & (~ gr(?x6)) & gr(?x5)],
    Gamma = [Hyp],
    once(proof([], Hyp => A, Proof)),
    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x5,x6,x7]: Hyp => A,
        Proof
    ).

:- end_tests(int_induction_step).

:- begin_tests(int_base_case).

test(int_base_case) :-
    A = (gr(?x4) & gr(?x4) & gr(0) \/ (~ gr(?x4)) & (~ gr(?x4)) & gr(0)),
    Gamma = [],
    once(proof(Gamma, A, Proof)),

    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all x4: A,
        Proof
    ).

:- end_tests(int_base_case).

:- begin_tests(ackermann_induction_step_part_2).

test(ackermann_induction_step_part_2) :-
    A = ( gr(?x9) & gr(s(?x8)) & gr(s(?x7))
        \/ (~gr(?x9)) & (~gr(s(?x8))) &gr(s(?x7)) ),

    append([
        [gr(?x10) & gr(?x8) & gr(s(?x7)) \/ ~ gr(?x10) & ~ gr(?x8) & gr(s(?x7))],
        [gr(?x9) & gr(?x10) & gr(?x7) \/ ~ gr(?x9) & ~ gr(?x10) & gr(?x7)]
    ], Gamma),

    Gamma = [Hyp,Hyp2],

    once(proof(
        [],
        (Hyp & Hyp2) =>  A,
        Proof
    )),

    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x7,x8,x9,x10]: (Hyp & Hyp2) => A,
        Proof
    ).

:- end_tests(ackermann_induction_step_part_2).


:- begin_tests(ackermann_induction_step_part_1).

test(ackermann) :-
    A = gr(?x6)&gr(0)&gr(s(?x5))\/ ~gr(?x6)& ~gr(0)&gr(s(?x5)),

    append([
        [gr(?x6)&gr(s(0))&gr(?x5)\/ (~gr(?x6))& (~gr(s(0))) & gr(?x5)]
    ], Gamma),

    Gamma = [Hyp],
    once(proof(
        [],
        Hyp => A,
        Proof
    )),

    % prt__write(Proof),
    gensym(l, L),
    lptp:lemma(
        L,
        all [x5,x6]: (Hyp) => A,
        Proof
    ).

:- end_tests(ackermann_induction_step_part_1).

:- begin_tests(ackermann_base_case).

test(ackermann) :-
    A = gr(s(?x4)) & gr(?x4) & gr(0) \/ ~ gr(s(?x4)) & ~ gr(?x4) & gr(0),
    Gamma = [],
    once(proof(
        Gamma,
        A,
        Proof
    )),

    %prt__write(Proof),
    gensym(l,L),
    lptp:lemma(L,
        all x4: A,
        Proof
    ).

:- end_tests(ackermann_base_case).

:- begin_tests(prover).

test(ground_term_in_gamma) :-
    Gamma = [p],
    A = p,
    once(proof(
        Gamma,
        A,
        Proof
    )),
    assertion(Proof = []).

test(ground_term_in_gamma) :-
    Gamma = [gr(?x0)],
    A = gr(?x0),
    once(proof(
        Gamma,
        A,
        Proof
    )),
    assertion(Proof = []).

test(axiom_2_5) :-
    Gamma = [gr(?x0)],
    once(proof(
        Gamma,
        gr([?x0]),
        Proof
    )),
    assertion(Proof = [assume(
        gr(?x0),
        [],
        gr([?x0])
    )]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all x0: gr(?x0) => gr([?x0]),
        Derivation
    ).

test(axiom_2_5) :-
    Gamma = [gr(?x0), gr(?x1)],
    once(proof(
        Gamma,
        gr([?x0|?x1]),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0) & gr(?x1),
            [],
            gr([?x0|?x1])
        )
    ]),
    Proof = [Derivation],

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) & gr(?x1) => gr([?x0|?x1]),
        Derivation
    ).

test(axiom_2_5) :-
    Gamma = [gr(?x0)],
    once(proof(
        Gamma,
        gr(s(?x0)),
        Proof
    )),

    % prt__write(Proof),
    assertion(Proof = [
        gr(?x0)
    ]).

test(axiom_2_5) :-
    Gamma = [gr(?x0), gr(?x1), gr(?x2)],
    once(proof(
        Gamma,
        gr('[|]'(?x0, [?x1|[?x2]])),
        Proof
    )),
    %prt__write(Proof),
    assertion(Proof = [
        assume(gr(?x0) & (gr(?x1) & gr(?x2)),
            [assume(
                gr(?x1) & gr(?x2),
                [],
                gr([?x1|?x2]))
            ],
            gr([?x0,?x1,?x2])
        )
    ]),
    Proof = [Derivation],

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1, x2]: gr(?x0) & gr(?x1) & gr(?x2) =>
            gr([?x0|[?x1|[?x2]]]),
        Derivation
    ).

test(axiom_2_5) :-
    Gamma = [gr([?x0|?x1])],
    once(proof(
        Gamma,
        gr(?x0) & gr(?x1),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr([?x0|?x1]),
            [],
            gr(?x0) & gr(?x1)
        )
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr([?x0|?x1]) => gr(?x0) & gr(?x1),
        Derivation
    ).

test(conjunction) :-
    Gamma = [gr(?x0) & gr(?x1)],
    once(proof(
        Gamma,
        gr(?x0),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0) & gr(?x1),
            [],
            gr(?x0)
        )
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) & gr(?x1) => gr(?x0),
        Derivation
    ).

test(conjunction) :-
    Gamma = [gr(?x0) & gr(?x1)],
    once(proof(
        Gamma,
        gr(?x1),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0) & gr(?x1),
            [],
            gr(?x1)
        )
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) & gr(?x1) => gr(?x1),
        Derivation
    ).

test(conjunction) :-
    Gamma = [gr(?x0) & gr(?x1) & gr(?x2)],
    once(proof(
        Gamma,
        gr(?x1),
        Proof
    )),

    assertion(Proof = [
        gr(?x0) & gr(?x1),gr(?x2),assume(gr(?x0) & gr(?x1),[],gr(?x1))
    ]).

test(disjunction) :-
    Gamma = [gr(?x0)],
    once(proof(
        Gamma,
        gr(?x0) \/ gr(?x1),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0),
            [],
            gr(?x0) \/ gr(?x1)
        )
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) => gr(?x0) \/ gr(?x1),
        Derivation
    ).

test(disjunction) :-
    Gamma = [gr(?x1)],
    once(proof(
        Gamma,
        gr(?x0) \/ gr(?x1),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x1),
            [],
            gr(?x0) \/ gr(?x1)
        )
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x1) => gr(?x0) \/ gr(?x1),
        Derivation
    ).

test(disjunction) :-
    Gamma = [gr(?x1)],
    once(proof(
        Gamma,
        gr(?x0) \/ gr(?x1),
        Proof
    )),

    % prt__write(Proof),
    assertion(Proof = [
        assume(gr(?x1),[],gr(?x0) \/ gr(?x1))
    ]),

    Proof = [Derivation],
    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1, x2]: gr(?x1) => gr(?x0) \/ gr(?x1),
        Derivation
    ).

test(disjunction_elimination) :-
    ~ gr(?x0) => ~ gr([?x0|?x1]) = Hyp,
    ~ gr(?x1) => ~ gr([?x0|?x1]) = Hyp1,
    ~ gr(?x0) \/ ~ gr(?x1) = Hyp2,
    _Gamma = [
        Hyp,
        Hyp1,
        Hyp2
    ],
    A = ~ gr([?x0|?x1]),
    once(proof(
        [],
        Hyp & Hyp1 & Hyp2 => A,
        Proof
    )),

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: Hyp & Hyp1 & Hyp2 => A,
        Proof
    ).

test(indirect) :-
    Gamma = [~ ~ gr(?x0)],
    once(proof(
        Gamma,
        gr(?x0),
        Proof
    )),
    assertion(Proof = [
        assume(
            ~ ~ gr(?x0),
            indirect(
                ~gr(?x0),
                [gr(?x0),ff]
            ),
            gr(?x0)
        )
    ]),

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: ~ ~ gr(?x0) => gr(?x0),
        Proof
    ).

test(contra) :-
    Gamma = [gr(?x0)],
    once(proof(
        Gamma,
        ~ ~ gr(?x0),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0),
            contra(
                ~ gr(?x0),
                [gr(?x0),ff]
            ),
            ~ ~ gr(?x0)
        )
    ]),

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) => ~ ~ gr(?x0),
        Proof
    ).

test(equivalence) :-
    Gamma = [gr(?x0), gr([?x0])],
    once(proof(
        Gamma,
        gr(?x0) <=> gr([?x0]),
        Proof
    )),
    assertion(Proof = [
        assume(
            gr(?x0) & gr([?x0]),
            [
                assume(
                    gr(?x0),
                    [assume(
                        gr(?x0),
                        [],
                        gr([?x0]))
                    ],
                    gr([?x0])
                ),
                assume(
                    gr([?x0]),
                    [],
                    gr(?x0)
                ),
                gr(?x0)<=>gr([?x0])
            ],
            gr(?x0)<=>gr([?x0])
        )
    ]),

    gensym(l,L),
    lptp:lemma(L,
        all [x0, x1]: gr(?x0) & gr([?x0]) => (gr(?x0)<=>gr([?x0])),
        Proof
    ).

test(p1) :-
    prover_alt:lemma(
        p1,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    assertion(
        Proof = assume(
            ~gr(?x)=>gr(?y),
            [indirect(
                ~ (gr(?x)\/gr(?y)),
                [contra(gr(?x),[gr(?x)\/gr(?y),ff]),gr(?y),gr(?x)\/gr(?y),ff])],
            gr(?x)\/gr(?y)
        )
    ),

    lptp:lemma(
        p1,
        all [x,y]: Impl,
        [Proof]
    ).

test(p2) :-
    prover_alt:lemma(
        p2,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    assertion(
        Proof = assume(
            gr(?x) => gr(?y),
            indirect(
                ~ (~ gr(?x) \/ gr(?y)),
                [indirect(~ gr(?x),[~ gr(?x) \/ gr(?y),ff]),
                gr(?y),
                ~ gr(?x) \/ gr(?y),
                ff]
            ),
            ~ gr(?x) \/ gr(?y)
     )
    ),

    lptp:lemma(
        p2,
        all [x,y]: Impl,
        [Proof]
    ).

test(p3) :-
    prover_alt:lemma(
        p3,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    % prt__write(Proof),
    assertion(
        Proof = assume(
            ~ (gr(?x) & gr(?y)),
            indirect(
                ~ (~ gr(?x) \/ ~ gr(?y)),
                [indirect(~ gr(?x),[~ gr(?x) \/ ~ gr(?y),ff]),
                contra(
                    gr(?y),
                    [gr(?x),
                contra(~ (~ gr(?x) \/ ~ gr(?y)),
                  [gr(?x) & gr(?y),
                   ff]),
                ff]),
                ~ gr(?x) \/ ~ gr(?y),
                ff]
            ),
            ~ gr(?x) \/ ~ gr(?y)
        )
    ),

    lptp:lemma(
        p3,
        all [x,y]: Impl,
        [Proof]
    ).

test(p4) :-
    prover_alt:lemma(
        p4,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    % prt__write(Proof),
    assertion(
        Proof = assume(
            ~ (gr(?x)\/gr(?y)),
            contra(gr(?x),[gr(?x)\/gr(?y),ff]),
            ~gr(?x)
        )
    ),

    lptp:lemma(
        p4,
        all [x,y]: Impl,
        [Proof]
    ).

test(p5) :-
    prover_alt:lemma(
        p5,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    % prt__write(Proof),
    assertion(
        Proof = assume(
            ~ (gr(?x) \/ gr(?y)),
                contra(
                    gr(?y),
                    [gr(?x) \/ gr(?y),ff]
                ),
                ~ gr(?y)
        )
    ),

    lptp:lemma(
        p5,
        all [x,y]: Impl,
        [Proof]
    ).

test(p6) :-
    prover_alt:lemma(
        p6,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    % prt__write(Proof),
    assertion(
        Proof = assume(
            ~ (gr(?x)=>gr(?y)),
            indirect(
                ~gr(?x),
                [assume(
                    gr(?x),
                    [ff],
                    gr(?y)
                ),ff]
            ),
            gr(?x)
        )
    ),

    lptp:lemma(
        p6,
        all [x,y]: Impl,
        [Proof]
    ).

test(p7) :-
    prover_alt:lemma(
        p7,
        gr(?x), gr(?y),
        Impl,
        Proof
    ),
    % prt__write(Proof),
    assertion(
        Proof = assume(
            ~ (gr(?x)=>gr(?y)),
            contra(
                gr(?y),
                [assume(gr(?x),[],gr(?y)),ff]
            ),
            ~gr(?y)
        )
    ),

    lptp:lemma(
        p7,
        all [x,y]: Impl,
        [Proof]
    ).

test(law_of_excluded_middle) :-
    law_of_excluded_middle([x4], [], Disjunctions),
    assertion(Disjunctions = [gr(?x4) \/ ~ gr(?x4)]).

test(law_of_excluded_middle) :-
    law_of_excluded_middle([x4,x5,x6,x7], [], Disjunctions),
    assertion(Disjunctions = [
        gr(?x4) \/ ~ gr(?x4),
        gr(?x5) \/ ~ gr(?x5),
        gr(?x6) \/ ~ gr(?x6),
        gr(?x7) \/ ~ gr(?x7)
    ]).

test(addmul_base_case) :-
    A = ( gr(?x4) & gr(?x4) & gr(0) ) \/ ( ~ gr(?x4) & ~ gr(?x4) & gr(0) ),
    once(proof([
        gr(?x4) \/ ~ gr(?x4),
        gr(0)
    ], A, Proof)),

    % prt__write(Proof),

    lptp:lemma(
       addmul_base_case,
       all [x4]: A,
       Proof
    ).
:- end_tests(prover).

%test(lte_groundness_property) :-
%    Gamma = [],
%    A = ( gr(?x5)&gr(?x4)\/ ~gr(?x5)&gr(?x4) => ( gr(s(?x5))&gr(s(?x4))\/ ~gr(s(?x5))&gr(s(?x4))) ),
%
%    once(proof(Gamma, A, Proof)),
%
%    %prt__write(Proof),
%    assertion(Proof = [
%        assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
%          [assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
%            cases(gr(?x5) & gr(?x4),
%             [gr(?x5),
%              gr(?x4),
%              gr(?x5)],
%             ~ gr(?x5) & gr(?x4),
%             [contra(gr(s(?x5)),[~ gr(?x5),gr(?x5),ff]),
%              ff],
%             gr(s(?x5))),
%            gr(s(?x5))),
%           assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
%            cases(gr(?x5) & gr(?x4),
%             [gr(?x5),
%              gr(?x4),
%              gr(?x4)],
%             ~ gr(?x5) & gr(?x4),
%             [~ gr(?x5),
%              gr(?x4),
%              gr(?x4)],
%             gr(s(?x4))),
%            gr(s(?x4))),
%           gr(s(?x5)) & gr(s(?x4)),
%           gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4))],
%          gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))
%    ]),
%    gensym(l, L),
%    lptp:lemma(
%        L,
%        all [x4,x5]: A,
%        Proof
%    ).
