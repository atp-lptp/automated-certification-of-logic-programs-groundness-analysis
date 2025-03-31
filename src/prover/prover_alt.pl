:- module(prover_alt, [
    derive/4,
    law_of_excluded_middle/3,
    nd_proof/2,
    nd_proof/3,
    nd_proof/4,
    proof/3,
    univ_rec/4,
    univ_acc_rec/4,
    neg_univ_rec/4,
    neg_univ_acc_rec/4,
    double_neg_univ_rec/4,
    double_neg_univ_acc_rec/4,
    univ_list_rec/2,
    compound_to_conjunction/2
]).

% - suite de test
% - principe du tiers exclu
% - lemme intermédiaires
% - Formule A atomique
% - Formule A s'obtient par conjonction
% - Formule A s'obtient par disjunction (cases)
% - Formule A s'obtient par implication
% - Formule A s'obtient par l'absurde indirect)
%   - indirect ( ~ ~ gr(_) en hypothèse afin d'obtenir gr(_) )
%   - contra ( gr(_) en hypothèse afin d'obtenir ~ gr(_) )
% - preuves validées
%  - fib 977 l -> 328 l | 2.9
%  - nat 984 l -> 441 l | 2.2
%  - addmul 918 l -> 389 l | 2.3

% from lptp.pl:
:- op(100, fy, ?).
:- op(960,yfx,<=>).		% equivalence, left-associative
:- op(950,xfy,=>).		% implication, right-associative
:- op(940,yfx,\/).		% disjunction, left-associative 
:- op(930,yfx,&).		  % conjunction, left-associative
:- op(900,fy,~).		  % negation 
:- op(980,xfy,by).

:- use_module(mod_lptp).
:- use_module('./prover').
:- use_module('../lptp', [
    log__debug/1,
    log__info/2
]).

% If print_term is needed to pretty print proofs:
%:- use_module(library(pprint)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% nd_proof(+Formula, -Proof)
%
% Construct an LPTP proof of Formula 
% and check if Proof is indeed a valid 
% LPTP proof of Formula, ie check that the goal
%   lemma(id,Formula, Proof)
% succeeds wrt the LPTP code. E.g.:
%   ?- nd_proof(a => a, Pr).
%   % LPTP: ok
%   Pr = [assume(a, [], a)] ;
%   false.
%
% More tests at the end of this file.

derive(Gamma, A, VarsNoQM, Proof) :-
    law_of_excluded_middle(VarsNoQM, [], Disjunctions),
    append(Gamma, Disjunctions, Gamma2),
    once(
        proof(
            Gamma2,
            A,
            Proof
        )
    ).

nd_proof(F,Proof) :- 
  proof([],F,Proof),
  % print_term(Proof, [indent_arguments(true),tab_width(0),nl(true)]),
  gensym(l,L),
  (mod_lptp:lemma(L,F,Proof) 
  -> writeln('% LPTP: ok') ; writeln('% LPTP: no')
  ).

nd_proof(Gamma, F, Proof) :-
  proof(Gamma,F,Proof),
  % print_term(Proof, [indent_arguments(true),tab_width(0),nl(true)]),
  gensym(l,L),
  (     mod_lptp:lemma(L,F,Proof)
  ->    log__info('LPTP: ok', [lemma(L,F,Proof)])
  ;     log__info('LPTP: ko', [lemma(L,F,Proof)]), fail ).

nd_proof(Gamma, Quant, F, Proof) :-
  (     proof(Gamma,F,Proof)
  ->    true
  ;     writeln('Could not prove:': F), fail ),

  % print_term(Proof, [indent_arguments(true),tab_width(0),nl(true)]),
  gensym(l,L),
  (     mod_lptp:lemma(L,Quant: F,Proof)
  ->    log__info('LPTP: ok', [lemma(L,Quant: F,Proof)])
  ;     writeln('LPTP: ko'),
        log__info('LPTP: ko', [lemma(L,Quant: F,Proof)]), fail ).

% principe du tiers exclu
law_of_excluded_middle([], Disjunctions, Disjunctions).
law_of_excluded_middle([Var|Vars], In, Disjunctions) :-
    append([In, [gr(?Var) \/ (~ gr(?Var))]], NextDisjunctions),
    law_of_excluded_middle(Vars, NextDisjunctions, Disjunctions).

%:- table proof/3.

succeeding(N,A) :-
    (   bb_get(debug, 1)
    ->  writed(succeeding(N,A))
    ;   true ).

writed(A) :-
    bb_get(depth, D),
    write(depth(D)),
    log__debug(depth(D)),
%    (   D = 1000
%    ->  halt
%    ;   true ),
    writed(D, A).

writed(0, A) :-
    writeln(A),
    log__debug(' '),
    log__debug(A),
    log__debug("\n").
writed(D, A) :-
    D > 0,
    % log__debug(' '),
    write(' '),
    NextDepth is D - 1,
    writed(NextDepth, A).

proof(Gamma, A, Proof) :-
    (   bb_get(counter, CountIn)
    ->  true
    ;   CountIn = 0 ),
    bb_put(counter, CountIn),

    (   bb_get(depth, DepthIn)
    ->  NextDepth is DepthIn + 1
    ;   NextDepth = 0 ),
    bb_put(depth, NextDepth),

%    (   CountIn > 1000
%    ->  writeln(count_out_exhausted(A)),
%        halt
%    ;   true ),

    (   \+ ground(Gamma)
    ->  writeln(a(A)),
        writeln(gamma_must_be_ground), fail
    ;   true ),

    once(proof_(Gamma, A, Proof)),
%    writeln(proved(A)-('__')-proof(Proof)),

    bb_get(depth, PostProofDepth),
    Depth is PostProofDepth - 1,
    bb_put(depth, Depth),

    bb_get(counter, ActualCountIn),
    CountOut is ActualCountIn + 1,
    bb_put(counter, CountOut),

%    writeln(count_out(CountOut)),
    !.

%proof_(_Gamma, _A, _) :-
%proof_(Gamma, A, _) :-
%    bb_put(debug, 1),
%    writed(proving-[A]-from-Gamma),
%    log__info(proving_form, [proving(A)-from(Gamma)]),
%    fail.

% 0
proof_(_Gamma, tt, []).

%proof(_Gamma, ~gr(0), [ff]).
%
%proof(_Gamma, gr(0), [tt]).

% A is atomic
proof_(_Gamma, gr(A), [tt]) :-
  ( atomic(A),
  A \= ?(_),
  A \= [?(_)],
  A \= [?(_)|?(_)] ),
  succeeding(1, gr(A)).

proof_(Gamma, ~ gr(A), Proof) :-
  ( atomic(A),
  A \= ?(_),
  A \= [?(_)],
  A \= [?(_)|?(_)] ),

  select(~ gr(Term), Gamma, _),
  Term =.. [_Pred|[Elem]],
  Elem = A,

  Proof = [
    contra(
      gr(A),
      [~ gr(Term), gr(Term), ff]
    ),
    ~ gr(A)
  ],
  succeeding(2,  ~ gr(A)).

proof_(Gamma, A, Proof) :-
    A = gr(?(Left) + ?(Right)),
    proof(Gamma, gr(?Left), LeftProof),
    proof(Gamma, gr(?Right), RightProof),
    append([
        [LeftProof],
        [gr(?Left)],
        [RightProof],
        [gr(?Right)],
        [A]
    ], Proof),
    succeeding(25,  A).

%proof_(Gamma, ~ gr([?First|?Rest]), Proof) :-
%  ( select(gr(?Elem), Gamma, WithoutElem)
%  ; select(gr(?Elem) & _, Gamma, WithoutElem)
%  ; select(_ & gr(?Elem) & _, Gamma, WithoutElem)
%  ; select(gr(?Elem) & _, Gamma, WithoutElem) ),
%
%  ( select(~ gr(?Elem), WithoutElem, _)
%  ; select(~ gr(?Elem) & _, WithoutElem, _)
%  ; select(_ & ~ gr(?Elem) & _, WithoutElem, _)
%  ; select(~ gr(?Elem) & _, WithoutElem, _) ),
%
%  Proof = [
%    contra(
%      gr([?First|?Rest]),
%      [~ gr(Elem), gr(Elem), ff]
%    ),
%    ~ gr([?First|?Rest])
%  ],
%  succeeding(75, ~ gr([?First|?Rest])).

proof_(_Gamma, ~ gr(Term), Proof) :-
  Term \= ?(_),
  Term =.. [_Pred|[Elem]],
  atomic(Elem),

  Proof = [
    contra(
      gr(Term),
      [~ gr(Term), gr(Term), ff]
    )
  ],
  succeeding(7, ~ gr(Term)).

proof_(Gamma, gr(Term), Proof) :-
    select(~ gr(Term), Gamma, WithoutTerm),
    Term = ?(Elem),
    select(gr([?Left|?Elem]), WithoutTerm, _),
    Proof = [
        ~ gr(Term),
        ~ gr(Elem),
        gr(?Left) & gr(?Elem),
        gr(?Elem),
        ff,
        gr(Term)
    ],
    succeeding(8,gr(Term)).

proof_(_Gamma, gr(Term), [tt]) :-
    Term \= ?(_),
    Term =.. [_Pred|[Elem]],
    atomic(Elem),
    succeeding(9,gr(Term)).

proof_(Gamma, gr(Term), Proof) :-
    Term =.. [_Pred|[H]],
    select(gr(H), Gamma, WithoutTerm),
    \+ select(~ gr(H), WithoutTerm, _),
    Proof = [gr(H)],
    succeeding(10,gr(Term)).

proof_(Gamma, gr(Term), Proof) :-
    Term =.. [_Pred|[H]],

    select(gr(H), Gamma, WithoutTerm),
    member(~gr(Term), WithoutTerm),

    Proof = [
        gr(Term),
        ~gr(Term),
        ff
    ],

    succeeding(12,gr(Term)).

proof_(_Gamma, gr(Compound), []) :-
    compound(Compound),
    Compound =.. [Pred|[Singleton]],
    Pred \= '?',
    atomic(Singleton),
    succeeding(13,gr(Compound)).

% gr(Term) is in Gamma
proof_(Gamma, gr(Term), Proof) :-
    Term = [?Elem],
    member(gr(?Elem), Gamma),
    Proof = [assume(
        gr(?Elem),
        [],
        gr([?Elem])
    )],
    succeeding(14,gr(Term)).

% gr(?H) & gr(?T) is in Gamma
proof_(Gamma, gr(Term), Proof) :-
    Term = [?H|?T],
    compound(Term),
    \+ is_list(Term),
    member(gr(?H), Gamma),
    member(gr(?T), Gamma),
    Proof = [assume(
        gr(?H) & gr(?T),
        [],
        gr([?H|?T])
    )],
    succeeding(15,gr(Term)).

proof_(Gamma, gr(Term), Proof) :-
    compound(Term),
    Term =.. [_Pred|[H]],
    member(gr(H), Gamma),
    Proof = [
        assume(
            gr(H),
            [],
            gr(Term)
        )
    ],
    succeeding(16,gr(Term)).

proof_(Gamma, gr([?First|[?Second]]), Proof) :-
    member(gr(?First), Gamma),
    member(gr(?Second), Gamma),
    Proof = [
        assume(
            gr(?First) & gr(?Second),
            [],
            gr([?First|?Second])
        )
    ],
    succeeding(17,gr([?First|[?Second]])).

proof_(Gamma, gr(Compound), Proof) :-
    compound(Compound),
    Compound =.. [_Pred|Args],
    Args = [First|Rest],
    member(gr(First), Gamma),

    Rest \= [?_Second],
    nth0(0, Rest, Term),
    compound(Rest),
    proof(Gamma, gr(Term), RestProof),

    RestProof = [assume(Assumption,_,_)],

    Proof = [
        assume(
            gr(First) & Assumption,
            RestProof,
            gr(Compound)
        )
    ],
    succeeding(18,gr(Compound)).

% 1
proof_(Gamma, A, Proof) :-
    member(A, Gamma),
    Proof = [],
    succeeding(19, A).

% 2

% conjonction de la clôture de termes
proof_(Gamma, gr(B) & gr(C), Proof) :-
    B = ?(_),
    C = ?(_),
    member(gr([B|C]), Gamma),
    Proof = [assume(
        gr([B|C]),
        [],
        gr(B) & gr(C)
    )],
    succeeding(21, gr(B) & gr(C)).

proof_(Gamma,  B & C, [B & C]) :-
    member(B, Gamma),
    member(C, Gamma),
    succeeding(22, B & C).

proof_(Gamma, A, Proof) :-
    A = gr(_),
    ( (
        member(A & B, Gamma),
        Proof = [assume(
          A & B,
          [],
          A
        )]
        )
    ; (
        member(B & A, Gamma),
        Proof = [assume(
          B & A,
          [],
          A
        )]
    ) ),
    succeeding(23,A).

proof_(Gamma, A, [A]) :-
    A \= gr(_),
    A \= ( ~ gr(_) ),
    (     member(A & _, Gamma)
    ;     member(_ & A, Gamma) ),
    succeeding(24,A).

proof_(Gamma, B \/ C, Proof) :-
    (   ( B = gr(_),
        member(B, Gamma),
        Proof = [assume(
            B,
            [],
            B \/ C
        )] )
    ;   ( C = gr(_),
        member(C, Gamma),
        Proof = [assume(
            C,
            [],
            B \/ C
        )] ) ),
    succeeding(25, B \/ C).

proof_(Gamma, B \/ C, [B \/ C]) :-
    B \= gr(_),
    C \= gr(_),
    (     member(B, Gamma)
    ;     member(C, Gamma) ),
    succeeding(26, B \/ C).

proof_(Gamma, A, [A]) :-
    A \= gr(_),
    A \= (~ gr(_)),
    member(B => A, Gamma),
    member(C => A, Gamma),
    member(B \/ C, Gamma),
    succeeding(27,A).

proof_(Gamma, gr(A), [gr(A)]) :-
    member(B => A, Gamma),
    member(C => A, Gamma),
    member(B \/ C, Gamma),
    succeeding(28, gr(A)).

% implication de la non-clôture d'un terme
proof_(Gamma, A, Proof) :-
    A = (~ gr(TermA)),
    TermA = [?H|?T],
    B = (~ gr(TermB)),
    TermB = ?Elem,
    ( Elem = H
    ; Elem = T ),
    Proof = [contra(
        gr(TermA),
        % TermB is either TermA head or tail
        [~ gr(TermB), gr(TermB), ff]
    )],
    member(B => A, Gamma),
    member(B, Gamma),
    succeeding(29,A).

proof_(Gamma, A, [A]) :-
    ( A = gr(_)
    ; A = ( ~ gr(_) ) ),
    B \= gr(_),
    B \= ( ~ gr(_) ),
    member(B => A, Gamma),
    member(B, Gamma),
    succeeding(30,A).

proof_(Gamma, A, [A]) :-
    ( A = gr(_)
    ; A = ( ~ gr(_) ) ),
    B = gr(_),
    member(B => A, Gamma),
    member(B, Gamma),
    succeeding(31,A).

proof_(Gamma, A, Proof) :-
    A = ( ~ gr(TermA) ),
    B = ( ~ gr(TermB) ),

    member(B => A, Gamma),
    member(B, Gamma),

    TermA =.. [_Pred|[?H]],
    TermB = ?H,

    Proof = [contra(
        gr(TermA),
        [~ gr(TermB), gr(TermB), ff]
    ), A],
    succeeding(32,A).

proof_(Gamma, A, [A]) :-
    A \= gr(_),
    A \= ( ~ gr(_) ),
    member(B => A, Gamma),
    member(B, Gamma),
    succeeding(33,A).

proof_(Gamma, A, [A]) :-
    member(ff, Gamma),
    succeeding(34,A).

proof_(Gamma, A, Proof) :-
    A = gr(_),
    member(~ ~ A, Gamma),
    Proof = [
    assume(
        ~ ~ A,
        indirect(
            ~ A,
            [A,ff]
        ),
        A
    )
    ],
    succeeding(35,A).

proof_(Gamma, A, [indirect(~ A, [A,ff]),A]) :-
    A \= gr(_),
    A \= (~ gr(_)),
    member(~ ~ A, Gamma),
    succeeding(36,A).

proof_(Gamma, ~ ~ A, Proof) :-
    A = gr(_),
    member(A, Gamma),
    Proof = [
        assume(
            A,
            contra(~ A, [A,ff]),
            ~ ~ A
        )
    ],
    succeeding(37, ~ ~ A).

proof_(Gamma, ~ ~ A, [contra(~ A, [A,ff]), ~ ~ A]) :-
    A \= gr(_),
    A \= (~ gr(_)),
    member(A, Gamma),
    succeeding(38, ~ ~ A).

proof_(Gamma, A <=> B, Pr) :-
    A \= gr(_),
    A \= ( ~ gr(_) ),
    B \= gr(_),
    B \= ( ~ gr(_) ),
    once(proof(Gamma, A => B, Pab)),
    once(proof(Gamma, B => A, Pba)),
    append(Pab, Pba, Paba),
    append(Paba, [A <=> B], Pr),
    succeeding(39, A <=> B).

proof_(Gamma, A <=> B, Proof) :-
    ( A = gr(_)
    ; A = ( ~ gr(_) ) ),
    ( B = gr(_)
    ; B = ( ~ gr(_) ) ),
    once(proof(Gamma, A => B, Pab)),
    once(proof(Gamma, B => A, Pba)),
    append(Pab, Pba, Paba),
    append(Paba, [A <=> B], Pr),
    Proof = [
        assume(
            A & B,
            Pr,
            A <=> B
        )
    ],
    succeeding(40, A <=> B).

% 3
proof_(Gamma, ff, Proof) :-
    select(~ ~ gr(Form), Gamma, Gamma2),
    select(~ gr(Form), Gamma2, _),
    Proof = [
        indirect(
            ~ gr(Form),
            [~ ~ gr(Form), ~ gr(Form), ff]
        ),
        gr(Form),
        ~ gr(Form),
        ff
    ],
    %writeln(proof(Proof)),
    succeeding(401,ff).

%proof_(Gamma, ff, Proof) :-
%    select(~ ~ gr([?Elem|_]), Gamma, Gamma2),
%    select(~ gr([?Elem|?Rest]), Gamma2, Gamma3),
%    ElemProof = [
%        indirect(
%            ~ gr(?Elem),
%            [~ ~ gr(?Elem), ~ gr(?Elem), ff]
%        ),
%        gr(?Elem),
%        ~ gr(?Elem),
%        ff
%    ],
%    proof_([~gr(?Rest)|Gamma3], ff, RestProof),
%    Proof = cases(
%        [
%            case(~gr(?Elem), ElemProof),
%            case(~gr(?Rest), RestProof)
%        ],
%        ff
%    ),
%%    writeln(proof(Proof)),
%    succeeding(402,ff).

%proof_(Gamma, ff, Proof) :-
%    select(~ ~ gr([?First|?Elem]), Gamma, Gamma2),
%    select(~ gr(?Elem), Gamma2, _),
%    Proof = [
%        indirect(
%            ~ gr(?Elem),
%            [~ ~ gr([?First|?Elem]), ~ gr(?Elem), ff]
%        ),
%        gr(?Elem),
%        ~ gr(?Elem),
%        ff
%    ],
%    %writeln(proof(Proof)),
%    succeeding(403,ff).

%proof_(Gamma, ff, Proof) :-
%    select(~ ~ gr(?Elem), Gamma, Gamma2),
%    once((
%        select(~ gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([_|?Elem]), Gamma2, _)
%    ;   select(~ gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([?Elem|_]), Gamma2, _)
%    ;   select(~ gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & ~ gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & ~ gr(?Elem), Gamma2, _) )),
%%    writeln(here____gamma(Gamma)),
%%    writeln(here____elem(?Elem)),
%    Proof = [
%        indirect(
%            ~ gr(?Elem),
%            [~ ~ gr(?Elem), ~ gr(?Elem), ff]
%        ),
%        gr(?Elem),
%        ~ gr(?Elem),
%        ff
%    ],
%    %writeln(proof(Proof)),
%    succeeding(487,ff).
%
%proof_(Gamma, ff, Proof) :-
%    select(~ gr(?Elem), Gamma, Gamma2),
%%    writeln(here____gamma(Gamma)),
%%    writeln(here____elem(~ gr(?Elem))),
%    once((
%        select(gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & gr(?Elem), Gamma2, _)
%    ;   select(gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & gr([_|?Elem]), Gamma2, _)
%    ;   select(gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & gr([?Elem|_]), Gamma2, _) )),
%%    writeln(here____matching_elem(?Elem)),
%    Proof = [
%        ~ gr(?Elem),
%        gr(?Elem),
%        ff
%    ],
%    succeeding(488,ff).
%
%proof_(Gamma, ff, Proof) :-
%    select(gr(?Elem), Gamma, Gamma2),
%%    writeln(here____gamma(Gamma)),
%%    writeln(here____elem(gr(?Elem))),
%    once((
%        select(~ gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & ~ gr(?Elem) & _, Gamma2, _)
%    ;   select(_ & ~ gr(?Elem), Gamma2, _)
%    ;   select(~ gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([_|?Elem]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([_|?Elem]), Gamma2, _)
%    ;   select(~ gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([?Elem|_]) & _, Gamma2, _)
%    ;   select(_ & ~ gr([?Elem|_]), Gamma2, _) )),
%%    writeln(here____matching_elem(?Elem)),
%    Proof = [
%        gr(?Elem),
%        ~ gr(?Elem),
%        ff
%    ],
%    succeeding(489,ff).

proof_(Gamma, ff, Proof) :-
    select(~ ~ gr(?Elem), Gamma, Gamma2),
    select(~ gr(?Elem) & _, Gamma2, _),
    Proof = [
        ~ gr(?Elem),
        gr(?Elem),
        ff
    ],
    succeeding(490,ff).

proof_(Gamma, ff, [ff]) :-
    select(~ gr(Term), Gamma, _),

    Term \= ?(_),
    Term \= [?(_)|?(_)],
    atomic(Term),
    succeeding(41,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(Term), Gamma, WithoutTerm),
    Term = ?(Elem),
    select(gr([?(Elem)|_]), WithoutTerm, _),

    Proof = [
        ~ gr(Term),
        gr(?Elem),
        ff
    ],
    succeeding(425,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(Term), Gamma, WithoutTerm),
    Term = ?(Elem),
    select(gr([?First|?(Elem)]), WithoutTerm, _),
    % writeln(elem(Elem)),

    Proof = [
        ~ gr(Term),
        gr(?First) & gr(?Elem),
        gr(?Elem),
        ff
    ],
    succeeding(426,ff).

proof_(Gamma, ff, [ff]) :-
    B \= gr(_),
    B \= (~gr(_)),
    member(B, Gamma),
    member(~ B, Gamma),
    succeeding(43,ff).

proof_(Gamma, ff, Proof) :-
    select(gr(LeftTerm), Gamma, WithoutLeftTerm),

    LeftTerm = ?Elem,

    select(~gr(RightTerm), WithoutLeftTerm, _WithoutRightTerm),

    RightTerm =.. [_Pred|[?RightTermElem]],

    Elem = RightTermElem,

    Proof = [
        gr(RightTerm),
        ~gr(RightTerm),
        ff
    ],
    succeeding(44,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(LeftTerm), Gamma, WithoutLeftTerm),

    LeftTerm = ?Elem,
    select(gr(?RightTermElem), WithoutLeftTerm, _WithoutRightTerm),

    Elem = RightTermElem,

    Proof = [
        ~gr(?Elem),
        gr(?RightTermElem),
        ff
    ],
    succeeding(45,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(LeftTerm), Gamma, WithoutLeftTerm),

    LeftTerm = ?Elem,

    select(gr(RightTerm), WithoutLeftTerm, _WithoutRightTerm),

    RightTerm =.. [_Pred|[?RightTermElem]],

    Elem = RightTermElem,

    Proof = [
        ~gr(?Elem),
        gr(?RightTermElem),
        ff
    ],
    succeeding(46,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(LeftTerm), Gamma, WithoutLeftTerm),

    LeftTerm =.. [_|[?Elem]],
    % writeln(left_term_elem:Elem),

    select(gr(RightTerm), WithoutLeftTerm, _WithoutRightTerm),
    RightTerm =.. [_|[?RightTermElem]],
    % writeln(right_term_elem:RightTermElem),

    Elem = RightTermElem,

    Proof = [
        ~gr(?Elem),
        gr(?RightTermElem),
        ff
    ],

    succeeding(47,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(0), Gamma, _WithoutLeftTerm),

    Proof = [
        ~ gr(0),
        gr(0),
        ff
    ],
    succeeding(48,ff).

proof_(Gamma, ff, Proof) :-
  select(gr(Term), Gamma, WithoutTerm),
  univ_acc_rec(gr(Term), [], _TermAcc, Elem),
  select(~gr(OtherTerm), WithoutTerm, _),
  neg_univ_acc_rec(~gr(OtherTerm), [], _OtherTermAcc, Elem),
  append([
    [~gr(OtherTerm)],
    [gr(OtherTerm)],
    [ff]
  ], Proof),
  succeeding(485,ff).

proof_(Gamma, ff, Proof) :-
    select(~ gr(?Elem), Gamma, Gamma2),
    select(gr([?Elem|_]), Gamma2, _),
    Proof = [
        ~ gr(?Elem),
        gr(?Elem),
        ff
    ],
    succeeding(486,ff).
%    proof_(Gamma, ~ gr(?Elem), SubProof),
%
%    append(
%        SubProof,
%        [
%            ~ gr(?Elem),
%            gr(?Elem),
%            ff
%        ],
%        Proof
%    ),
%    succeeding(486,ff).

proof_(Gamma, A, [ff,A]) :-
    A \= gr(_),
    A \= (~gr(_)),
    dif(A,ff),
    member(B, Gamma),
    member(~ B, Gamma),
    succeeding(49,A).

proof_(Gamma, A, [ff,A]) :-
    ( A = gr(_)
    ; A = ( ~ gr(_) ) ),
    member(B, Gamma),
    member(~ B, Gamma),
    succeeding(50,A).

% 4
proof_(Gamma, B & C, Proof) :-
    once(proof(Gamma, B, P)),
    once(proof(Gamma, C, Q)),
    append(P,Q,PQ), append(PQ,[B & C],Proof),
    succeeding(51, B & C).

% 5
proof_(Gamma, B => C, [assume(B, P, C)] ) :-
    once(proof([B|Gamma], C, P)),
    succeeding(52, B => C).

proof_(Gamma, ~ B,  [contra(B, P), ~ B] ) :-
    % writeln('about to prove':(~B)),
    once(proof([B|Gamma], ff, P)),
    succeeding(53, ~ B).

% 6
proof_(Gamma, B \/ C, Proof) :-
    ( once(proof(Gamma, B, P))
    ; once(proof(Gamma, C, P)) ),
    append(
        P,
        [B\/C],
        Proof
    ),
    succeeding(54, B \/ C).

proof_(Gamma, B \/ C, Proof) :-
    ( once(proof(Gamma, B, P)),
    once(proof(Gamma, C, Q)) ),
    Proof = cases(
        [
            case(B, P),
            case(C, Q)
        ],
        B\/C
    ),
    succeeding(55, B \/ C).

% 7
proof_(Gamma, A, [B, C | P]) :-
    select(B & C, Gamma, Gamma2),
    once(proof([B, C | Gamma2], A, P)),
    succeeding(56, A).

% 8
proof_(Gamma, A, [assume(B \/ C, cases(CasesOut, A), A)] ) :-
    select(B \/ C, Gamma, Gamma2),
    B = (_ \/ _),
    C \= (_ \/ _),
    proof_disjunction(Gamma2, A, B, [], Cases),
    once(proof([C | Gamma2], A, Q)),
    append([Cases, [case(C, Q)]], CasesOut),
    succeeding(585, A).

proof_(Gamma, A, [cases([case(B, P), case(C, Q)], A), A] ) :-
    A \= gr(_),
    A \= (~ gr(_)),
    select(B \/ C, Gamma, Gamma2),
    B \= (_ \/ _),
    once(proof([B | Gamma2], A, P)),
    once(proof([C | Gamma2], A, Q)),
    succeeding(57, A).

proof_(Gamma, A, [assume(B \/ C, cases([case(B, P), case(C, Q)], A), A)] ) :-
    B \= (_ \/ _),
    C \= (_ \/ _),
    ( A = (~ gr(_))
    ; A = gr(_) ),
    select(B \/ C, Gamma, Gamma2),
    once(proof([B | Gamma2], A, P)),
    once(proof([C | Gamma2], A, Q)),
    succeeding(58, A).

% 9
proof_(Gamma, A, [P4, ~(B \/ C) => ~ B, P5 , ~(B \/ C) => ~ C | Pr]) :-
    A \= gr(_),
    A \= (~ gr(_)),
    select(~ (B \/ C), Gamma, Gamma2),
    lemma(p4, B, C, ~(B \/ C) => ~ B, P4),
    lemma(p5, B, C, ~(B \/ C) => ~ C, P5),
    once(proof([~ B,  ~ C | Gamma2], A, Pr)),
    succeeding(59, A).

proof_(Gamma, A, [P4, ~(B \/ C) => ~ B, P5 , ~(B \/ C) => ~ C | Pr]) :-
    ( A = gr(_)
    ; A = (~ gr(_)) ),
    select(~ (B \/ C), Gamma, Gamma2),
    lemma(p4, B, C, ~(B \/ C) => ~ B, P4),
    lemma(p5, B, C, ~(B \/ C) => ~ C, P5),
    once(proof([~ B,  ~ C | Gamma2], A, Pr)),
    succeeding(60, A).

% 10
proof_(Gamma, B \/ C, [assume(~ B, P, C), P1, B \/ C]) :-
    once(proof([~ B | Gamma], C, P)),
    lemma(p1, B, C,  (~ B => C) => B \/ C, P1),
    succeeding(61, B \/ C).

% 11
proof_(Gamma, A, [P3, cases(~ B, P, ~ C, Qbis, A), A]) :-
    select(~ (B & C), Gamma, Gamma2),
    once(proof([~ B | Gamma2], A, P)),
    once(proof([~ C | Gamma2], A, Q)),
    (     Q = [ff]
    ->    Qbis = [C, ff]
    ;     Qbis = Q ),
    %  Qbis = [ff],
    lemma(p3, B, C, ~ (B & C) => ~ B \/ ~ C, P3),
    succeeding(62, A).

% 12
proof_(Gamma, A, [P6, ~ (B => C) => B, P7, ~ (B => C) => ~ C | P]) :-
    select(~ (B => C), Gamma, Gamma2),
    lemma(p6, B, C,  ~ (B => C) => B, P6),
    lemma(p7, B, C,  ~ (B => C) => ~ C, P7),
    once(proof([B, ~ C | Gamma2], A, P)),
    succeeding(63, A).

% 13
proof_(Gamma, A, [P2, cases(~ B, P, C, Q, A), A]) :-
    select(B => C, Gamma, Gamma2),
    \+ dif(C, A),
    %dif(C, ff),
    lemma(p2, B, C, (B => C) => ~ B \/ C, P2),
    once(proof([~ B | Gamma2], A, P)),
    once(proof([C | Gamma2], A, Q)),
    succeeding(64, A).

proof_(Gamma, A, [P2, cases(~ B, P, C, Q, A), A]) :-
    select(B => C, Gamma, Gamma2),
    A \= (~ gr(_)),
    A \= gr(_),
    C \= (~ gr(_)),
    C \= gr(_),
    %dif(C, ff),
    lemma(p2, B, C, (B => C) => ~ B \/ C, P2),
    once(proof([~ B | Gamma2], A, P)),
    once(proof([C | Gamma2], A, Q)),
    succeeding(65, A).

proof_(Gamma, A, Proof) :-
    select(Disjunction, Gamma, Gamma2),
    Disjunction = (_ \/ _),
%    writeln(disjunction_r(Disjunction)),
    %writeln(gamma2(Gamma2)),
    proof_disjunction_r(Gamma2, A, Disjunction, [], CasesOut),
    Proof = [assume(Disjunction, cases(CasesOut, A), A)],
    %writeln(Proof),
    succeeding(651,ff).

%proof_(Gamma, A, _) :-
%    writed(could_not_prove(A)-from-Gamma),
%    halt,
%    fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lemma(p1, P, Q, (~ P => Q) => P \/ Q,
assume( ~ P => Q,
 [indirect(~ (P \/ Q),
   [contra(P, [P \/ Q, ff]),
    Q, P \/ Q, ff])],
 P \/ Q)).

lemma(p2, P, Q, (P => Q) => ~ P \/ Q,
assume(P => Q,
 indirect(~ (~ P \/ Q),
  [indirect(~ P, [~ P \/ Q, ff]),
   Q, ~ P \/ Q, ff]),
~ P \/ Q)).

lemma(p3, P, Q, ~ (P & Q) => ~ P \/ ~ Q,
assume(~ (P & Q),
 indirect(~ (~ P \/ ~ Q),
  [indirect(~ P, [~ P \/ ~ Q, ff]),
   contra(Q, [P, contra( ~(~ P \/ ~ Q), [P & Q, ff]), ff]),
   ~ P \/ ~ Q, ff]),
~ P \/ ~ Q)).
     
lemma(p4, P, Q, ~(P \/ Q) => ~ P,
assume(~(P \/ Q),
 contra(P,[P \/ Q, ff]),
 ~ P)).
  
lemma(p5, P, Q, ~(P \/ Q) => ~ Q,
assume(~(P \/ Q),
 contra(Q,[P \/ Q, ff]),
 ~ Q)).


lemma(p6, P, Q, ~(P => Q) => P, Proof) :-
Proof = assume(~(P => Q),
 indirect(~ P,
  [assume(P, [ff], Q),
   ff]),
 P).
    
lemma(p7, P, Q, ~(P => Q) => ~ Q,
assume(~(P => Q),
 contra(Q,
  [assume(P, [], Q),
   ff]),
 ~ Q)).
    

%%%%%%%%%%%%%%%%%%%%%%%
/* Tests
make.
nd_proof(tt, P), fail.
nd_proof(ff, P), fail.
nd_proof(p, P), fail.
nd_proof(a => a, P), fail.
nd_proof(a => b, P), fail.
nd_proof(p \/ ~ p, P), fail.
nd_proof(~ p \/ p, P), fail.
nd_proof( ~ ~ a => a, P), fail.
nd_proof(a => ~ ~ a, P), fail.
nd_proof(a <=> ~ ~ a, P), fail.
nd_proof( ((a => ff) => ff) => a, P), fail.
nd_proof( a => ((a => ff) => ff) , P), fail.
nd_proof( ((a => ff) => ff) <=> a, P), fail.
nd_proof( (a => b) \/ (b => a), P), fail.
nd_proof((~ a \/ b) => (a => b), P), fail.
nd_proof((a => b) => (~ a \/ b), P), fail.
nd_proof((~ b => ~ a) => (a => b), P), fail.
nd_proof((~ b => c) => b \/ c, P), fail.
*/


/* lemma P1 -- P7
make.
nd_proof((~p => q) => p \/ q,P), fail.
nd_proof((p => q)  => ~ p \/ q,P), fail.
nd_proof(~(p & q)  => ~ p \/ ~ q,P), fail.
nd_proof(~(p \/ q) => ~ p ,P), fail.
nd_proof(~(p \/ q) => ~ q ,P), fail.
nd_proof(~(p => q) => p ,P), fail.
nd_proof(~(p => q) => ~ q ,P), fail.
*/

/* ex. 56:
make.
proof_([~ a \/ b], a => b, P), writeln(P), fail.
nd_proof((~ b => ~  a) => (a => b),Pr),fail.
*/

/* ex. 57
make.
nd_proof(~ (a & ~ a), P), fail.
nd_proof((a \/ a) => a, P), fail.
nd_proof((a & a) => a, P), fail.
nd_proof((a & (b \/c)) => a & b \/ a & c, P), fail.
nd_proof((a & b \/ a & c) => (a & (b \/c)), P), fail.
nd_proof((a \/ b & c ) => ((a \/ b)  & (a \/c)), P), fail.
nd_proof( ((a \/ b)  & (a \/c)) => (a \/ b & c), P), fail.
*/


/* ex. 58:
make.
proof_([~ b => c], b \/ c, P), writeln(P),fail.
proof_([b => c], ~ b \/ c, P), writeln(P),fail.
proof_([~(b & c)], ~ b \/ ~ c, P), writeln(P),fail.
proof_([~(b \/ c)], ~ b, P), writeln(P),fail.
proof_([~(b \/ c)], ~ c, P), writeln(P),fail.
proof_([~(b => c)], b, P), writeln(P),fail.
proof_([~(b => c)], ~ c, P), writeln(P),fail.
*/

/* ex. 59:
make.
nd_proof(~ (a \/ b) => ~ a & ~ b, P), fail.
nd_proof( ~ a & ~ b => ~ (a \/ b),P), fail.
nd_proof( ~ (a &  b) => ~ a \/ ~ b, P), fail.
nd_proof( ~ a \/  ~ b => ~ (a & b), P), fail.
nd_proof( (a \/ b) & (~ a \/ b) => b, P), fail.
nd_proof( (a \/ b) & (~ b \/ c) => (a \/ c), P), fail.
*/


/* ex. 60:
make.
nd_proof(~ p & ~ (~ p & q) => ~ q, P), fail.
nd_proof((p & q) & (p  & r) & ~ p => q \/ r, P), fail.
nd_proof( ~ p \/ ~(p & q) => (~ q \/ ~p), P), fail.
*/

/* ex. 61:
make.
nd_proof((p \/ q) => (~p & ~q) => r, P), fail.
nd_proof((p => q) & (q => r) & ~ r => ~ p, P), fail.
nd_proof((p => q) => ((p & q ) \/ ~ p), P), fail.
*/

/*
% ex. 62: 
make.
nd_proof( (p \/ q) & (p => r) => (q \/ r),P), fail.
*/


ensures_vars(Form, ?Var) :-
    Form = ?(Var).

univ(Form, DepthIn, DepthOut, Out) :-
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    Out = Var
  ;     NextDepth = DepthIn + 1,
        univ(Elem, NextDepth, DepthOut, Out) ).

univ_acc(Form, AccIn, AccOut, Out) :-
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([gr(Elem)|AccIn], AccOut),
        Out = Var
  ;     NextAccIn = [gr(Elem)|AccIn],
        univ_acc(Elem, NextAccIn, AccOut, Out) ).

neg_univ_acc(Form, AccIn, AccOut, Out) :-
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([~gr(Elem)|AccIn], AccOut),
        Out = Var
  ;     NextAccIn = [~gr(Elem)|AccIn],
        neg_univ_acc(Elem, NextAccIn, AccOut, Out) ).

double_neg_univ_acc(Form, AccIn, AccOut, Out) :-
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([~(~gr(Elem))|AccIn], AccOut),
        Out = Var
  ;     NextAccIn = [~(~gr(Elem))|AccIn],
        double_neg_univ_acc(Elem, NextAccIn, AccOut, Out) ).

compound_to_conjunction([Form], Out) :-
    Out = gr(Form).
compound_to_conjunction([Form|Rest], Out) :-
    once(compound_to_conjunction(Rest, RestOut)),
    Out = (gr(Form) & RestOut).

    univ_list_rec(Term, Out) :-
      Term = gr(Form),
      Form =.. [Pred|Elems],
      '[|]' = Pred,
      Elems = [First|Rest],

      univ(First, 1, _DOut, FirstElem),
      Rest =.. [_|[Args,[]]],
      Args =.. [Pred2|RestArgs],
      Pred2 = '[|]',
      maplist(ensures_vars, RestArgs, RestOut),

      Out = [?(FirstElem)|RestOut].

    univ_list_rec(Term, Out) :-
      Term = gr(Form),
      Form =.. [Pred|Elems],
      %writeln(pred(Pred)),
      Pred = '[|]',
      (     is_list(Elems)
      ->    maplist(ensures_vars, Elems, Out)
      ;     fail ).

univ_rec(Term, AccIn, AccOut, Out) :-
  Term = gr(Form),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    Out = Var
  ;     univ(Elem, AccIn, AccOut, Out) ).

univ_acc_rec(Term, AccIn, AccOut, Out) :-
  Term = gr(Form),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([gr(Elem)|AccIn], AccOut),
        Out = Var
  ;     univ_acc(Elem, [gr(Elem)|AccIn], AccOut, Out) ).

neg_univ_rec(Term, AccIn, AccOut, Out) :-
  Term = (~ gr(Form)),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    Out = Var
  ;     univ(Elem, AccIn, AccOut, Out) ).

neg_univ_acc_rec(Term, AccIn, AccOut, Out) :-
  Term = (~ gr(Form)),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([~gr(Elem)|AccIn], AccOut),
        Out = Var
  ;     neg_univ_acc(Elem, [~gr(Elem)|AccIn], AccOut, Out) ).

double_neg_univ_rec(Term, AccIn, AccOut, Out) :-
  Term = (~ ~ gr(Form)),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    Out = Var
  ;     univ(Elem, AccIn, AccOut, Out) ).

double_neg_univ_acc_rec(Term, AccIn, AccOut, Out) :-
  Term = (~ ~ gr(Form)),
  Form =.. [_Pred|[Elem]],
  (     Elem = ?(Var)
  ->    reverse([~(~gr(Elem))|AccIn], AccOut),
        Out = Var
  ;     double_neg_univ_acc(Elem, [~(~gr(Elem))|AccIn], AccOut, Out) ).

proof_disjunction(Gamma, Target, Rest, In, Out) :-
    Rest \= (_ \/ _),
    once(proof([Rest | Gamma], Target, Proof)),
    Out = [case(Rest, Proof)|In].
proof_disjunction(Gamma, Target, Leftmost \/ Rest, In, Out) :-
    Leftmost \= (_ \/ _),
    once(proof([Leftmost | Gamma], Target, Proof)),
    proof_disjunction(Gamma, Target, Rest, [case(Leftmost, Proof)|In], Out).

proof_disjunction_r(Gamma, Target, Rest, In, Out) :-
    Rest \= (_ \/ _),
    once(proof([Rest | Gamma], Target, Proof)),
    reverse([case(Rest, Proof)|In], Out).
proof_disjunction_r(Gamma, Target, Rest \/ Rightmost, In, Out) :-
    Rightmost \= (_ \/ _),
    once(proof([Rightmost | Gamma], Target, Proof)),
    proof_disjunction_r(Gamma, Target, Rest, [case(Rightmost, Proof)|In], Out).
