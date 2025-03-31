:- module(prover_dslplm, [
    m/2,
    undecomposable_form/1,
    undecomposable_gamma/1,
    prove/3,
    prove_p1/3
]).

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

%prove(_, gr([]), []).
%prove(_, ~ gr([]), [ff]).

prove(Gamma, A, Proof) :-
    case_1(A, Gamma),
    member(ff, Gamma),
    Proof = [ff, A].

prove(Gamma, ff, Proof) :-
    case_1(ff, Gamma),
    \+ member(ff, Gamma),
    select(gr(?Var), Gamma, Gamma2),
    select(~gr(?Var), Gamma2, _),
    Proof = [gr(?Var),~gr(?Var),ff].

prove(Gamma, gr(?Var2), Proof) :-
    case_1(gr(?Var2), Gamma),
    \+ member(ff, Gamma),
    select(gr(?Var), Gamma, Gamma2),
    select(~gr(?Var), Gamma2, _),
    Proof = [gr(?Var),~gr(?Var),ff,gr(?Var2)].

prove(Gamma, gr(?Var2), Proof) :-
    case_1(gr(?Var2), Gamma),
    \+ member(ff, Gamma),
    select(gr(?Var2), Gamma, _),
    Proof = [].

prove(Gamma, ~ gr(?Var2), Proof) :-
    case_1(~ gr(?Var2), Gamma),
    \+ member(ff, Gamma),
    select(gr(?Var), Gamma, Gamma2),
    select(~gr(?Var), Gamma2, _),
    Proof = [gr(?Var),~gr(?Var),ff,~ gr(?Var2)].

prove(Gamma, ~ gr(?Var2), Proof) :-
    case_1(~ gr(?Var2), Gamma),
    \+ member(ff, Gamma),
    select(~ gr(?Var2), Gamma, _),
    Proof = [].

prove(Gamma, B & C, Proof) :-
    case_2(B & C, Gamma),
    prove(Gamma, B, BProof),
    prove(Gamma, C, CProof),
    append([
        BProof,
        CProof,
        [B & C]
    ], Proof).

prove(Gamma, B => C, Proof) :-
    case_2(B => C, Gamma),
    prove([B|Gamma], C, CProof),
    Proof = [
        assume(
            B,
            CProof,
            C
        ),
        B => C
    ].

prove(Gamma, B \/ C, Proof) :-
    case_2(B \/ C, Gamma),
    prove([~ B|Gamma], C, CProof),
    prove_p1([~ B => C|Gamma], B \/ C, P1),
    Proof = [
        assume(
            ~ B,
            CProof,
            C
        ),
        assume(
            ~ B => C,
            P1,
            B \/ C
        ),
        B \/ C
    ].

% 3.f
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    select(B & C, Gamma, Gamma2),

    (   select(B, Gamma2, Gamma3)
    ->  true
    ;   Gamma3 = Gamma2 ),

    (   select(C, Gamma3, Gamma4)
    ->  true
    ;   Gamma4 = Gamma3 ),

    once(prove([B|[C|Gamma4]], B & C, Subproof)),

    append([
        [B],
        [C],
        Subproof
    ], Proof).

% 3.g
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    select(B \/ C, Gamma, Gamma2),

    once(prove([B|Gamma2], A, LeftProof)),
    once(prove([C|Gamma2], A, RightProof)),

    Proof = [
        assume(
            B,
            LeftProof,
            A
        ),
        B => A,
        assume(
            C,
            RightProof,
            A
        ),
        C => A,
        [A]
    ].

% 3.h
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    dif(C, ff),
    select(B => C, Gamma, Gamma2),

    once(prove([~ B|Gamma2], A, P)),
    once(prove([C|Gamma2], A, Q)),

    prove_p2([B => C|Gamma2], ~ B \/ C, P2),

    append([
        P2,
        [assume(
            ~ B,
            P,
            ~ B => A
        )],
        [assume(
            C,
            Q,
            C => A
        )],
        [A]
    ], Proof).

% 3.i
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    select(~ (B & C), Gamma, Gamma2),

    once(prove([~ B|Gamma2], A, P)),
    once(prove([~ C|Gamma2], A, Q)),

    prove_p3([~ (B & C)|Gamma2], ~ B \/ ~ C, P3),

    append([
        P3,
        [assume(
            ~ B,
            P,
            ~ B => A
        )],
        [assume(
            ~ C,
            Q,
            ~ C => A
        )],
        [A]
    ], Proof).

% 3.j
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    select(~ (B \/ C), Gamma, Gamma2),

    once(prove([~ B|[~C|Gamma2]], A, P)),

    prove_p4([~ (B \/ C)|Gamma2], ~ B, P4),
    prove_p5([~ (B \/ C)|Gamma2], ~ C, P5),

    append([
        P4,
        P5,
        P,
        [A]
    ], Proof).

% 3.k
prove(Gamma, A, Proof) :-
    case_3(A, Gamma),

    select(~ (B => C), Gamma, Gamma2),

    once(prove([B|[~C|Gamma2]], A, P)),

    prove_p6([~ (B => C)|Gamma2], B, P6),
    prove_p7([~ (B => C)|Gamma2], ~ C, P7),

    append([
        P6,
        P7,
        P,
        [A]
    ], Proof).

prove_p1(Gamma, B \/ C, Proof) :-
    case_2(B \/ C, Gamma),
    select(~ B => C, Gamma, _),

    Proof = [
        assume(
            ~ B => C,
            [
                ~ B \/ ~ ~ B,
                cases(~ B,
                [
                    contra(
                        ~ (B \/ C),
                        [
                         assume(
                          ~ B,
                          [C],
                          C
                         ),
                         C,
                         B \/ C
                        ])
                ],
                ~ ~ B,
                [
                    indirect(
                        ~ B,
                        [B, ~ B, ff]
                    )
                ], B \/ C),
                B \/ C
            ],
            B \/ C
        )
    ].

prove_p2(Gamma, ~ B \/ C, Proof) :-
    case_3(~ B \/ C, Gamma),
    select(B => C, Gamma, _),

    Proof = [
        assume(
            B => C,
            [
                cases(
                   ~B,
                   assume(
                    ~ B,
                    [~B \/ C],
                    ~B \/ C
                   ),
                   B,
                   assume(C, [~ B \/ C], ~B \/ C),
                   ~B \/ C
                )
            ],
            ~ B \/ C
        )
    ].

prove_p3(Gamma, ~ B \/ ~ C, Proof) :-
    case_3(~ B \/ ~ C, Gamma),
    select(~ (B & C), Gamma, _),

    Proof = [
        assume(
            ~ (B & C),
            indirect(
               ~ (~ B \/ ~ C),
               [indirect(~ B, [~ B \/ ~ C, ff]),
                indirect(~ C, [~ B \/ ~ C, ff]),
                B & C, ff]
            ),
            ~ B \/ ~ C
        )
    ].

prove_p4(Gamma, ~ B, Proof) :-
    select(~ (B \/ C), Gamma, _),
    Proof = [
         assume(
            ~ (B \/ C),
            contra(
                B,
                [B \/ C,ff]),
                ~B
        )
    ].

prove_p5(Gamma, ~ C, Proof) :-
    select(~ (B \/ C), Gamma, _),
    Proof = [
        assume(
            ~ (B \/ C),
            contra(
                C,
                [B \/ C,
                ff]
            ),
            ~C
        )
    ].

prove_p6(Gamma, ~ B, Proof) :-
    select(~ (B => C), Gamma, _),
    Proof = [
        [
        assume(
            ~ (B => C),
            [
                ~ B \/ ~ ~ B,
                cases(
                    ~ B,
                    [
                        assume(
                            B,
                            [ff],
                            C
                        ),
                        B => C,ff
                    ],
                    ~ ~ B,
                    [
                        indirect(
                        ~ B,
                        [~ ~ B]
                        ),
                        B
                    ],
                    B
                )
            ],
            B)
        ]
    ].

prove_p7(Gamma, C, Proof) :-
    select(~ (B => C), Gamma, _),
    Proof = [
        assume(
            ~ (B => C),
            contra(
                C,
                [
                    assume(
                        B,
                        [],
                        B => C
                    ),
                    B => C,
                    ~ (B => C),
                    ff
                ]
            ),
            ~ C
        )
    ].

% prt__write(Proof),
% writeln(proof(Proof)), halt.

case_1(A, Gamma) :-
    undecomposable_form(A),
    undecomposable_gamma(Gamma).

case_2(A, _Gamma) :-
    \+ undecomposable_form(A).

case_3(_A, Gamma) :-
    \+ undecomposable_gamma(Gamma).

undecomposable_form(ff).
undecomposable_form(A) :- A = gr(_).
undecomposable_form(A) :- A = (~ gr(_)).

undecomposable_gamma(Gamma) :- member(ff, Gamma).
undecomposable_gamma(Gamma) :-
    \+ member(~ (_ & _), Gamma),
    \+ member(~ (_ \/ _), Gamma),
    \+ member(_ <=> _, Gamma),
    \+ member(_ => _, Gamma),
    \+ member(_ & _, Gamma),
    \+ member(_ \/ _, Gamma).

m(ff, 0).
m(A, 1) :-
    A = gr(?_).
m(A, 2) :-
    A = (~ gr(?_)).
m(gr(A), 1) :-
    A =.. ['[|]'|[?_|[[]]]].
m(~ gr(A), 2) :-
    A =.. ['[|]'|[?_|[[]]]].
m(gr(A), 1) :-
    dif(Functor, '[|]'),
    A =.. [Functor|[?_]].
m(~ gr(A), 2) :-
    dif(Functor, '[|]'),
    A =.. [Functor|[?_]].
% gr(A) <=> gr(?_) & gr(?_)
m(gr(A), 3) :-
    A =.. ['[|]'|Args],
    Args = [?_,?_].
m(gr(A), M) :-
    A =.. ['[|]'|Args],
    measure(Args, M).
% ~ gr(A) <=> ( gr(?_)    \/   gr(?_)   => \bot )
%             ( m(_, 1) + 2 + m(_, 1) + 1 + 0   )
m(~ gr(A), 5) :-
    A =.. ['[|]'|Args],
    Args = [?_,?_].

m(gr(?_) & gr(?_), 3).

% ~ gr(?_) & ~ gr(?_) <=> ( gr(?_)   => \bot &   gr(?_)   => \bot )
%                         ( m(_,1) +  1    + 1 + m(_,1) + 1
m(~ gr(?_) & ~ gr(?_), 5).

m(gr(?_) \/ gr(?_), 4).

% ~ gr(?_) \/ ~ gr(?_) <=> ( gr(?_)   => \bot \/   gr(?_)   => \bot )
%                         ( m(_,1) +  1    + 2 + m(_,1) + 1
m(~ gr(?_) \/ ~ gr(?_), 6).

m(A, M) :-
    A = (Left & Right),
    Right = gr(_),
    once(m(Right, M1)),
    once(m(Left, M2)),
    M is M1 + 1 + M2.

m(A, M) :-
    A = (Left & Right),
    Right = (~ gr(_)),
    once(m(Right, M1)),
    once(m(Left, M2)),
    M is M1 + 1 + M2.

m(A, M) :-
    A = (Left \/ Right),
    Right = gr(_),
    once(m(Right, M1)),
    once(m(Left, M2)),
    M is M1 + 2 + M2.

m(A, M) :-
    A = (Left \/ Right),
    Right = (~ gr(_)),
    once(m(Right, M1)),
    once(m(Left, M2)),
    M is M1 + 2 + M2.

m(A, M) :-
    A = (Assumption => Conclusion),
    once(m(Assumption, M1)),
    once(m(Conclusion, M2)),
    M is M1 + 1 + M2.

measure([Arg], M) :-
    m(gr(Arg), M).

% gr([?_0,[?_1|?_2]]) <=> ( gr(?_0)   &   gr(?_1)   &   gr(?_2) )
%                           m(_, 1) + 1 + m(_, 1) + 1 + m(_, 1)

measure([Arg|Rest], M) :-
    once(m(gr([Arg]), M1)),
    once(measure(Rest, M2)),
    M is M1 + 1 + M2.
