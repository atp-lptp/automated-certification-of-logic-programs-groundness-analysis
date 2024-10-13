:- set_prolog_flag(plunit_output, always).
:- set_prolog_flag(test_environment, true).
:- use_module('../lptp').
:- use_module(library(clpb)).
:- use_module(library(prolog_stack)).
:- debug.

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

:- begin_tests(groundness_analysis).

%% See https://www.swi-prolog.org/pldoc/man?predicate=numbervars%2f3
free_variables_list([]).
free_variables_list([E|Es]) :-
    \+ \+ (
        numbervars(E,0,_),
        print(E),

        ( Es = []
        -> true
        ; write(',') )

    ),
    free_variables_list(Es).

write_to_file(File, Content) :-
    open(File,write,Stream),
    write(Stream,Content),
    close(Stream).

accept_revised_derivation(Derivation, ExpectationFile) :-
    with_output_to(string(Str), prt__write(Derivation)),
    string_concat(Str, '.', StrWithEndingDot),
    write_to_file(ExpectationFile, StrWithEndingDot).

test(remove_qm_steps__average) :-
    SUs = [
        &(&(gr(?(x17)),gr(?(x16))),gr(s(?(x11)))),
        succeeds(p(?(x12),?(x14))),
        succeeds(p(?(x14),?(x15))),
        succeeds(p(?(x15),?(x16))),
        succeeds(average(s(?(x11)),?(x16),?(x17))),
        succeeds(p(?(x13),?(x17)))
    ],

    _Step = step(
        [?(x11),?(x12),?(x13),?(x14),?(x15),?(x16),?(x17)],
        SUs,
        by(ff,gap),
        &(&(gr(?(x13)),gr(?(x12))),gr(?(x11)))
    ),
    Facts = [lemma(eq21,:(all([A,B]),succeeds(=>(eq(A,B),\/(&(gr(B),gr(A)),&(~(gr(B)),~(gr(A))))))),
        induction([:(all([A,B]),succeeds(=>(eq(A,B),\/(&(gr(B),gr(A)),&(~(gr(B)),~(gr(A)))))))],
        [step([C],[],by(ff,gap),\/(&(gr(C),gr(C)),&(~(gr(C)),~(gr(C)))))])),
        lemma(p21,:(all([D,E]),succeeds(=>(p(D,E),\/(&(gr(E),gr(D)),&(~(gr(E)),~(gr(D))))))),
        induction([:(all([D,E]),succeeds(=>(p(D,E),\/(&(gr(E),gr(D)),&(~(gr(E)),~(gr(D)))))))],
        [step([],[],by(ff,gap),\/(&(gr(0),gr(0)),&(~(gr(0)),~(gr(0))))),
        step([F],[],by(ff,gap),\/(&(gr(F),gr(s(F))),&(~(gr(F)),~(gr(s(F))))))]))],

    once(invariant_from_facts_and_hypothesis(SUs, Facts, Proofs, Conjunction)),

    assertion(Proofs = [succeeds p(?x12,?x14)=>gr(?x14)&gr(?x12)\/ ~gr(?x14)& ~gr(?x12)by lemma(p21),succeeds p(?x14,?x15)=>gr(?x15)&gr(?x14)\/ ~gr(?x15)& ~gr(?x14)by lemma(p21),succeeds p(?x15,?x16)=>gr(?x16)&gr(?x15)\/ ~gr(?x16)& ~gr(?x15)by lemma(p21),succeeds p(?x13,?x17)=>gr(?x17)&gr(?x13)\/ ~gr(?x17)& ~gr(?x13)by lemma(p21)]),
    assertion(Conjunction = gr(?x17)&gr(?x16)&gr(s(?x11))&((gr(?x14)&gr(?x12)\/ ~gr(?x14)& ~gr(?x12))&((gr(?x15)&gr(?x14)\/ ~gr(?x15)& ~gr(?x14))&((gr(?x16)&gr(?x15)\/ ~gr(?x16)& ~gr(?x15))&(gr(?x17)&gr(?x13)\/ ~gr(?x17)& ~gr(?x13)))))).

test(matching_dnf) :-
    once(matching_dnf(gr(?x10)&gr([?x8|?x9])&gr(?x7)\/ ~gr(?x10)&gr([?x8|?x9])& ~gr(?x7)\/ ~gr(?x10)& ~gr([?x8|?x9])&gr(?x7))).

test(prove_disjunction) :-
    once(derive_groundness_property((gr([97|?x4]) <=> gr(?x3)) => gr(?x4) & gr(?x3) \/ ~gr(?x4) & ~gr(?x3),[x3,x4], Result)),
    assertion(Result = [cases(gr(?x3),cases(gr(?x4),[gr(97)&gr(?x4),gr([97|?x4])=>gr(97)&gr(?x4),assume(~ (gr(97)&gr(?x4)),contra(gr([97|?x4]),[gr(97)&gr(?x4),ff]),~gr([97|?x4])),gr([97|?x4])<=>gr(97)&gr(?x4)by lemma(axiom_2_5),assume(gr(?x3),[],gr([97|?x4])),gr([97|?x4])=>gr(?x3),gr(?x3)=>gr([97|?x4]),gr(97)&gr(?x4),gr([97|?x4])=>gr(97)&gr(?x4),assume(~ (gr(97)&gr(?x4)),contra(gr([97|?x4]),[gr(97)&gr(?x4),ff]),~gr([97|?x4])),gr([97|?x4])<=>gr(97)&gr(?x4)by lemma(axiom_2_5),assume(gr([97|?x4]),[],gr(?x3)),gr(?x4)&gr(?x3),gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3),assume(gr([97|?x4])<=>gr(?x3),[],gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3))],~gr(?x4),[contra(gr(97)&gr(?x4),[]),~ (gr(97)&gr(?x4)),gr([97|?x4])=>gr(97)&gr(?x4),assume(~ (gr(97)&gr(?x4)),contra(gr([97|?x4]),[gr(97)&gr(?x4),ff]),~gr([97|?x4])),gr([97|?x4])<=>gr(97)&gr(?x4)by lemma(axiom_2_5),contra(gr(?x3)=>gr([97|?x4]),[gr(?x3),gr([97|?x4]),~gr([97|?x4]),ff]),~ (gr(?x3)=>gr([97|?x4])),~ (gr([97|?x4])=>gr(?x3))\/ ~ (gr(?x3)=>gr([97|?x4])),assume(gr([97|?x4])<=>gr(?x3),[],gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3))],(gr([97|?x4])<=>gr(?x3))=>gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3)),~gr(?x3),cases(gr(?x4),[gr(97)&gr(?x4),gr([97|?x4])=>gr(97)&gr(?x4),assume(~ (gr(97)&gr(?x4)),contra(gr([97|?x4]),[gr(97)&gr(?x4),ff]),~gr([97|?x4])),gr([97|?x4])<=>gr(97)&gr(?x4)by lemma(axiom_2_5),contra(gr([97|?x4])=>gr(?x3),[gr([97|?x4]),gr(?x3),~gr(?x3),ff]),~ (gr([97|?x4])=>gr(?x3)),~ (gr([97|?x4])=>gr(?x3))\/ ~ (gr(?x3)=>gr([97|?x4])),assume(gr([97|?x4])<=>gr(?x3),[],gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3))],~gr(?x4),[assume(gr(?x3),[],gr([97|?x4])),gr([97|?x4])=>gr(?x3),gr(?x3)=>gr([97|?x4]),contra(gr(97)&gr(?x4),[]),~ (gr(97)&gr(?x4)),gr([97|?x4])=>gr(97)&gr(?x4),assume(~ (gr(97)&gr(?x4)),contra(gr([97|?x4]),[gr(97)&gr(?x4),ff]),~gr([97|?x4])),gr([97|?x4])<=>gr(97)&gr(?x4)by lemma(axiom_2_5),assume(gr([97|?x4]),[],gr(?x3)),~gr(?x4)& ~gr(?x3),gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3),assume(gr([97|?x4])<=>gr(?x3),[],gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3))],(gr([97|?x4])<=>gr(?x3))=>gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3)),(gr([97|?x4])<=>gr(?x3))=>gr(?x4)&gr(?x3)\/ ~gr(?x4)& ~gr(?x3))]).

test(groundness_analysis_lptp__lex) :-
    once(groundness_analysis_lptp('./examples/filex/lex.pl', Lemmas)),

    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__lex__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__lex) :-
    once(prove_groundness_prop('./examples/filex/lex.pl', Lemmas)),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__lex__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__micgram) :-
    once(groundness_analysis_lptp('./examples/filex/micgram.pl', Lemmas)),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__micgram__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__micgram) :-
    once(prove_groundness_prop('./examples/filex/micgram.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__micgram__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__mini) :-
    once(groundness_analysis_lptp('./examples/filex/mini.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__mini__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    close(Stream),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__mini) :-
    \+ once(prove_groundness_prop('./examples/filex/mini.pl', _Lemmas)).

test(groundness_analysis_lptp__mr) :-
    \+ once(prove_groundness_prop('./examples/filex/mr.pl', _Lemmas)).

test(groundness_analysis_lptp__pi) :-
    \+ once(prove_groundness_prop('./examples/filex/pi.pl', _Lemmas)).

test(groundness_analysis_lptp__pq) :-
    \+ once(prove_groundness_prop('./examples/filex/pq.pl', _Lemmas)).

% Stack limit
%test(groundness_analysis_lptp__sequence) :-
%    prove_groundness_prop('./examples/filex/sequence.pl', Lemmas)
%    assertion(Lemmas = []).

test(groundness_analysis_lptp__testneg) :-
    once(groundness_analysis_lptp('./examples/filex/testneg.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__testneg__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    close(Stream),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__testneg, blocked('contradictory hypothesis')) :-
    once(prove_groundness_prop('./examples/filex/testneg.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__pq__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__tiny) :-
    once(groundness_analysis_lptp('./examples/filex/tiny.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__tiny__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    close(Stream),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__tiny) :-
    once(prove_groundness_prop('./examples/filex/tiny.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__tiny__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    close(Stream),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__mc_pera) :-
    once(groundness_analysis_lptp('./examples/filex/mc_pera.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__mc_pera__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__mc_pera) :-
    once(prove_groundness_prop('./examples/filex/mc_pera.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__mc_pera__expected_lemmas_without_gap.pl',
    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),

    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__extrait_peep) :-
    \+ once(prove_groundness_prop('./examples/filex/extrait_peep.pl', _Lemmas)).

test(groundness_analysis_lptp__expmr) :-
    \+ once(prove_groundness_prop('./examples/filex/expmr.pl', _Lemmas)).

test(groundness_analysis_lptp__ex30) :-
    \+ once(prove_groundness_prop('./examples/filex/ex30.pl', _Lemmas)).

test(groundness_analysis_lptp__derivDLS) :-
    once(groundness_analysis_lptp('./examples/filex/derivDLS.pl', Lemmas)),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__derivDLS__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__derivDLS) :-
    once(prove_groundness_prop('./examples/filex/derivDLS.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__derivDLS__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__average) :-
    once(groundness_analysis_lptp('./examples/filex/average1.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__average__expected_lemmas.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis_lptp__average) :-
    once(prove_groundness_prop('./examples/filex/average1.pl', Lemmas)),
    % prt__write(Lemmas),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__average__expected_lemmas_without_gap.pl',

    accept_revised_derivation(Lemmas, ExpectedLemmasFile),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(groundness_analysis) :-
    groundness_analysis('./examples/filex/apprev.pl', RelsGroundness),

    with_output_to(
        atom(RelsGroundnessAtom),
        free_variables_list(RelsGroundness)
    ),

    assertion(RelsGroundnessAtom = 'app/3-[A,B,C]-(C=:=B*A),rev/2-[A,B]-(B=:=A)*1').

test(groundness_invariant) :-
    groundness_analysis_common('./examples/filex/apprev.pl', Clauses0, Sccs, RelsInterArgsBool0),
    reverse(Clauses0,Clauses),

    simplify(RelsInterArgsBool0,RelsInterArgsBool),

    append(Sccs, PIs),

    assertion(
        PIs = [app/3,rev/2]
    ),

    once(member(app/3-Vars-Cs,RelsInterArgsBool)),

    findall(Vars,(sat(Cs),labeling(Vars)),Model),

    assertion(
        Model = [[0,0,0],[1,0,0],[0,1,0],[1,1,1]]
    ),

    sols_vars_dnf([[0,0,0]],['A','B','C'],DNF),
    assertion(DNF = ~gr('C')& ~gr('B')& ~gr('A')),

    sols_vars_dnf_aux([], [0,0,0], ['A','B','C'], Cond),
    assertion(Cond = ~gr('C')& ~gr('B')& ~gr('A')),

    sol_vars_cond([0,0,0],['A','B','C'],VarsCond),
    assertion(VarsCond =  ~gr('C')& ~gr('B')& ~gr('A')),

    sol_vars_cond_aux([0,0],0,['A','B','C'],CondAuxCs),
    assertion(CondAuxCs = ~gr('C')& ~gr('B')& ~gr('A')),

    sol_vars_cond_aux([],0,['C'],CondAuxCsC),
    assertion(CondAuxCsC = ~gr('C')),

    sols_vars_dnf([[0,0,0],[1,0,0]],['A','B','C'],DNF2),
    assertion(DNF2 = ~gr('C')& ~gr('B')&gr('A')\/ ~gr('C')& ~gr('B')& ~gr('A')),

    sols_vars_dnf(Model,['A','B','C'],ModelDNF),
    assertion(ModelDNF = gr('C')&gr('B')&gr('A')
        \/ ~gr('C')&gr('B')& ~gr('A')
        \/ ~gr('C')& ~gr('B')&gr('A')
        \/ ~gr('C')& ~gr('B')& ~gr('A')),

    model_formula([[0,0,0]],app,['A','B','C'],L),
    assertion(L = all['A','B','C']:(succeeds app('A','B','C')=> ~gr('C')& ~gr('B')& ~gr('A'))),

    model_formula([[0,0,0],[1,0,0],[0,1,0],[1,1,1]],app,['A','B','C'],LBis),
    assertion(LBis = all['A','B','C']:(
        succeeds app('A','B','C')=>
            gr('C')&gr('B')&gr('A')\/
            ~gr('C')&gr('B')& ~gr('A')\/
            ~gr('C')& ~gr('B')&gr('A')\/
            ~gr('C')& ~gr('B')& ~gr('A')
    )),

    with_output_to(
        atom(RelsInterArgsBoolAtom),
        free_variables_list(RelsInterArgsBool)
    ),

    assertion(RelsInterArgsBoolAtom = 'app/3-[A,B,C]-(C=:=B*A),rev/2-[A,B]-(B=:=A)*1'),

    once(build_lemmas(PIs,Clauses,RelsInterArgsBool,Lemmas)),

    %prt__write(Lemmas),

    assertion(Lemmas = [lemma(app32,
     all [x1,x2,x3]:
      (succeeds app(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
        ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
        ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
     induction(
      [all [x1,x2,x3]:
        (succeeds app(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
          ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
          ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
      [step([x4],[],
        ff by gap,
        gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
        ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([])),
       step([x5,x6,x7,x8],
        [gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
         ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
         succeeds app(?x6,?x7,?x8)],
        ff by gap,
        gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
        ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
        ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
        ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))])),
    lemma(rev22,
     all [x1,x2]:
      (succeeds rev(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
     induction(
      [all [x1,x2]:
        (succeeds rev(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
      [step([],[],ff by gap,gr([]) & gr([]) \/ ~ gr([]) & ~ gr([])),
       step([x3,x4,x5,x6],
        [gr(?x6) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x4),
         succeeds rev(?x4,?x6),
         succeeds app(?x6,[?x3],?x5)],
        ff by gap,
        gr(?x5) & gr([?x3|?x4]) \/ ~ gr(?x5) & ~ gr([?x3|?x4]))]))]).

test(groundness_analysis_lptp__apprev) :-
    once(prove_groundness_prop('./examples/filex/apprev.pl', Lemmas)),
    ExpectedLemmasFile = './src/test/expectations/groundness_analysis_lptp__apprev__expected_lemmas_without_gap.pl',

%    with_output_to(string(Str), prt__write(Lemmas)),
%    write_to_file(ExpectedLemmasFile, Str),

    open(ExpectedLemmasFile,read,Stream),
    read(Stream,ExpectedLemmas),
    assertion(Lemmas = ExpectedLemmas).

test(test_prove_groundness_prop) :-
    Phi = (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
              ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)
              =>  gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
                              ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
                              ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
                              ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),

% checked from https://web.stanford.edu/class/cs103/tools/truth-table-tool/
%( ( W /\ Y /\ Z ) \/ ( ~  W /\ Y /\ ~  Z ) \/ ( W /\ ~  Y /\ ~  Z ) \/  ( ~  W /\ ~  Y /\ ~   Z ) =>
%( W /\ X /\ Y /\ Z ) \/  ( (~  W \/ ~  X) /\ Y /\ (~  X  \/ ~  Z )) \/  ( (W \/ X) /\ ~  Y /\ (~  X  \/ ~  Z ))
%\/  ( (~  W \/ ~  X) /\ ~  Y /\ (~  X  \/ ~  Z )) )

    once(prove_with_premises(
        x8 & x7 & x6 \/ ~ x8 & x7 & ~ x6 \/ ~ x8 & ~ x7 & x6,
        false,
        [~ x8,x7,x6,x5],
        [],
        DisjunctionCases
    )),

    % prt__write(DisjunctionCases),

    assertion(
        DisjunctionCases = [contra(x8 & x7,[x8,~ x8,ff]),
                            ~ (x8 & x7),
                            contra(x8 & x7 & x6,
                             [x8 & x7,
                              ~ (x8 & x7),
                              ff]),
                            ~ (x8 & x7 & x6),
                            contra(~ x6,[]),
                            ~ ~ x6,
                            contra(~ x8 & x7 & ~ x6,[]),
                            ~ (~ x8 & x7 & ~ x6),
                            contra(x8 & x7 & x6 \/ ~ x8 & x7 & ~ x6,
                             cases(
                              [case(~ x8 & x7 & ~ x6,[~ x8 & x7 & ~ x6,~ (~ x8 & x7 & ~ x6),ff]),
                               case(x8 & x7 & x6,
                                [x8 & x7 & x6,
                                 ~ (x8 & x7 & x6),
                                 ff])],
                              ff)),
                            ~ (x8 & x7 & x6 \/ ~ x8 & x7 & ~ x6),
                            contra(~ x7,[]),
                            ~ ~ x7,
                            contra(~ x8 & ~ x7,[]),
                            ~ (~ x8 & ~ x7),
                            contra(~ x8 & ~ x7 & x6,
                             [~ x8 & ~ x7,
                              ~ (~ x8 & ~ x7),
                              ff]),
                            ~ (~ x8 & ~ x7 & x6),
                            contra(x8 & x7 & x6 \/ ~ x8 & x7 & ~ x6 \/ ~ x8 & ~ x7 & x6,
                             cases(
                              [case(~ x8 & ~ x7 & x6,[~ x8 & ~ x7 & x6,~ (~ x8 & ~ x7 & x6),ff]),
                               case(~ x8 & x7 & ~ x6,
                                [~ x8 & x7 & ~ x6,
                                 ~ (~ x8 & x7 & ~ x6),
                                 ff]),
                               case(x8 & x7 & x6,
                                [x8 & x7 & x6,
                                 ~ (x8 & x7 & x6),
                                 ff])],
                              ff)),
                            ~ (x8 & x7 & x6 \/ ~ x8 & x7 & ~ x6 \/ ~ x8 & ~ x7 & x6)]),

    once(prove_groundness_property(Phi, [x5,x6,x7,x8], apprev:gr, GroundnessPropLemma)),

    ExpectedLemmaFile = './src/test/expectations/prove_groundness_property__expected_lemma.pl',

%    with_output_to(string(Str), prt__write(GroundnessPropLemma)),
%    write_to_file(ExpectedLemmaFile, Str),

    open(ExpectedLemmaFile,read,Stream),
    read(Stream,ExpectedGroundnessPropLemma),
    assertion(GroundnessPropLemma = ExpectedGroundnessPropLemma),

    BaseCase = gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
        ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([]),

    once(prove_groundness_property(BaseCase, [x4], apprev:gr:base, BaseCaseProof)),

%    prt__write(BaseCaseProof),

    assertion(BaseCaseProof = lemma(apprev:gr:base,
       all [x4]: gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
        ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([]),
       [cases(gr(?x4),
         [gr(?x4) & gr(?x4),
          gr(?x4) & gr(?x4) & gr([]),
          gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]),
          gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
          ~ gr(?x4) & ~ gr(?x4) & gr([]),
          gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
          ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([])],
         ~ gr(?x4),
         [~ gr(?x4) & ~ gr(?x4),
          ~ gr(?x4) & ~ gr(?x4) & gr([]),
          gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
          ~ gr(?x4) & ~ gr(?x4) & gr([]),
          gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
          ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([])],
         gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
         ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([]))])).

test(test_derive_groundness_prop) :-
    Prop = gr(?x8)&gr(?x7)&gr(?x6)\/ ~gr(?x8)&gr(?x7)& ~gr(?x6)\/ ~gr(?x8)& ~gr(?x7)&gr(?x6)
    \/ ~gr(?x8)& ~gr(?x7)& ~gr(?x6)=>gr([?x5|?x8])&gr(?x7)&gr([?x5|?x6])
    \/ ~gr([?x5|?x8])&gr(?x7)& ~gr([?x5|?x6])\/ ~gr([?x5|?x8])& ~gr(?x7)&gr([?x5|?x6])
    \/ ~gr([?x5|?x8])& ~gr(?x7)& ~gr([?x5|?x6]),

    once(derive_groundness_property(Prop, [x5,x6,x7,x8], PropProof)),

    ExpectedDerivationFile = './src/test/expectations/derive_groundness_property__apprev__expected_derivation.pl',

%    accept_revised_derivation(PropProof, ExpectedDerivationFile),

    open(ExpectedDerivationFile,read,Stream),
    read(Stream,ExpectedDerivation),

    assertion(PropProof = ExpectedDerivation).

test(test_derive_groundness_prop__add_mul__base_case) :-
    Prop = gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0),

    once(derive_groundness_property(Prop, [x4], PropProof)),

    ExpectedDerivationFile = './src/test/expectations/derive_groundness_property__add_mul__expected_derivation_base_case.pl',

%    accept_revised_derivation(PropProof, ExpectedDerivationFile),

    open(ExpectedDerivationFile,read,Stream),
    read(Stream,ExpectedDerivation),
    assertion(PropProof = ExpectedDerivation).

test(test_derive_groundness_prop__add_mul__induction_step) :-
    Prop = gr(?x7)&gr(?x6)&gr(?x5)\/ ~gr(?x7)& ~gr(?x6)&gr(?x5)
    => gr(s(?x7))&gr(?x6)&gr(s(?x5))\/ ~gr(s(?x7))& ~gr(?x6)&gr(s(?x5)),

    once(derive_groundness_property(Prop, [x5,x6,x7], PropProof)),
    %prt__write(PropProof),

    ExpectedDerivationFile = './src/test/expectations/derive_groundness_property__add_mul__expected_derivation_induction_step.pl',

%    accept_revised_derivation(PropProof, ExpectedDerivationFile),

    open(ExpectedDerivationFile,read,Stream),
    read(Stream,ExpectedDerivation),

    assertion(PropProof = ExpectedDerivation).

:- end_tests(groundness_analysis).

