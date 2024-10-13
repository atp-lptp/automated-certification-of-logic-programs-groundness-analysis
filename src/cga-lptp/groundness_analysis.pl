:- module(groundness_analysis,[
    groundness_analysis/2,
    groundness_analysis_lptp/2,
    groundness_analysis_common/4,
    infer_groundness_prop_with_cti/2,
    groundness_invariant/4,
    prove_groundness_prop/2,

    invariant_from_facts_and_hypothesis/4,

    matching_dnf/1,

    model_formula/4,
    simplify/2,

    build_lemmas/4,
    write_lemmas/2,

    remove_qm_steps/3,

    sols_vars_dnf/3,
    sols_vars_dnf_aux/4,
    sol_vars_cond/3,
    sol_vars_cond_aux/4,

    derive_groundness_property/3,
    is_compound_form_except_list_question_mark/1,
	prove/4,
	prove_groundness_property/4,
    prove_with_premises/5,

    sccs_having_mutually_recursive_predicates/3
]).
:- use_module('../prover/prover').

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
:- op(900, fy,  succeeds).
:- op(900, fy,  fails).
:- op(960, yfx, <=>).
:- op(980, xfy, by).

%%%
:- use_module(library(clpb)).
:- use_module(library(readutil)).
%%%
:- use_module(file).
:- use_module(prolog_flatprolog).
:- use_module(prolog_clph).
:- use_module(bool_itp).
:- use_module(compat_swi).
:- use_module(db).
:- use_module(bool_clph_bool).
:- use_module(bool_op).
:- use_module(db).
:- use_module(utils).
%%%

% ?- groundness_analysis('examples/filex/apprev.pl',M).
% M = [app(i, i, o), rev(i, o)].

groundness_analysis(FileName, RelsGroundness) :-
    groundness_analysis_common(FileName, _, _, RelsInterArgsBool),
    %write_list(RelsInterArgsBool),
    rias_groundness(RelsInterArgsBool,RelsGroundness),
    %write_list(RelsGroundness),
    true.
    
rias_groundness([],[]).
rias_groundness([P/N-(Vars-BoolF-_X-_Y)|Rias],[P/N-Vars-BoolF|RGs]) :-
    %trace,
    rias_groundness(Rias,RGs).
/*
rias_groundness([P/N-(Vars-BoolF-_X-_Y)|Rias],[P/N-Vars2-BoolF2-Pos|RGs]) :-
    %trace,
    simplify_constraint(Vars,BoolF,Vars2,BoolF2),
    constraint_posconstraint(Vars2,BoolF2,Pos),
    rias_groundness(Rias,RGs).
*/


%%%%%%%%%%%%%%%

% groundness_analysis_lptp('examples/filex/apprev.pl',L),write_lemmas(user,L),fail.

groundness_analysis_lptp(FileName,Lemmas) :-
    groundness_analysis_common(FileName, Clauses0, Sccs, RelsInterArgsBool0),

    simplify(RelsInterArgsBool0,RelsInterArgsBool),
    append(Sccs, PIs),
    reverse(Clauses0,Clauses),

    (   no_mutually_recursive_predicates_in_all_sccs(Sccs)
    ->  true
    ;   atomic_list_concat(['Mutually recursive clauses not yet supported (', FileName, ')'], Message),
        log__info('warning', Message) ),

    build_lemmas(PIs,Clauses,RelsInterArgsBool,Lemmas).

    no_mutually_recursive_predicates_in_all_sccs([]).
    no_mutually_recursive_predicates_in_all_sccs([Scc|Sccs]) :-
        length(Scc, 1),
        no_mutually_recursive_predicates_in_all_sccs(Sccs).

    sccs_having_mutually_recursive_predicates([], Sccs, Sccs).
    sccs_having_mutually_recursive_predicates([Scc|Sccs], SccsIn, SccsOut) :-
        (   length(Scc, 1)
        ->  SccsIn = NextSccsIn
        ;   [Scc|SccsIn] = NextSccsIn ),
        sccs_having_mutually_recursive_predicates(Sccs, NextSccsIn, SccsOut).

% infer_groundness_prop_with_cti('examples/filex/apprev.pl',PIs).

infer_groundness_prop_with_cti(FileName,PIs) :-
    groundness_analysis_common(FileName, Clauses0, Sccs, RelsInterArgsBool0),

    simplify(RelsInterArgsBool0,RelsInterArgsBool),
    append(Sccs, PIs),

    (
        getenv('CGA_LPTP_MODE', Mode),
        Mode = 'infer_groundness_prop_with_cti'
    ->
        length(PIs, N),
        atom_concat(N, ' ', HowManyPredicates),
        write(HowManyPredicates),

        term_variables(RelsInterArgsBool, VarsList),
        length(VarsList, HowManyVars),
        write(' & '),

        write(HowManyVars),
        write(' & ')

    ;   true    ),

    reverse(Clauses0,_Clauses).

prove_groundness_prop(FileName,Lemmas) :-
    debug,
    groundness_analysis_common(FileName, Clauses0, Sccs, RelsInterArgsBool0),

    simplify(RelsInterArgsBool0,RelsInterArgsBool),
    %
    % write_list(RelsInterArgsBool),
    append(Sccs, PIs),
    reverse(Clauses0,Clauses),

    % write(Sccs), nl,
    (   no_mutually_recursive_predicates_in_all_sccs(Sccs)
    ->  true
    ;   atomic_list_concat(['Mutually recursive clauses not yet supported (', FileName, ')'], Message),
        log__info('warning', Message),
        fail ),

    build_lemmas(PIs,Clauses,RelsInterArgsBool,[],Lemmas).

    groundness_analysis_common(FileName, Clauses, Sccs, RelsInterArgsBool) :-
        file_clauses(FileName,Clauses),
        %
        prologs_flatprologs(Clauses,FPClauses),
%        write_list(FPClauses),
        flatprologs_clphs(FPClauses,ClpHClauses),
        %write_list(ClpHClauses),
        clphs_clpbs(ClpHClauses,ClpBClauses),
        %write_list(ClpBClauses),
        %
        call_graph(ClpBClauses,CallGraph),
        graph_sccs(CallGraph,Sccs),
        %write_list(Sccs),
        %
        empty_db(Db0),
        add_cls_domain_dbs(ClpBClauses,clpb,Db0,Db1),
        sccs_db_domain_sccscls(Sccs,Db1,clpb,SccsClsB),
        %
        TimeOut = 1000,
        tp(SccsClsB,bool_op,no_widening,BaseBool,[star-union],TimeOut),
        assoc_to_list(BaseBool,RelsInterArgsBool).

simplify([],[]).
simplify([P/N-(Args-Cs-_-_)|Riabs],[P/N-Args-Cs|Rs]) :- simplify(Riabs,Rs).

write_lemmas(Stream,[]) :- nl(Stream).
write_lemmas(Stream,[L|Ls]) :- nl(Stream),write_lemma(Stream,L),write_lemmas(Stream,Ls).
 
  write_lemma(Stream, L) :-
    getenv('FORMAT_PROOF', _),
    with_output_to(string(Lemma), prt__write(L)),
    write(Stream, (:-)),write(Stream, ' '),write(Stream, Lemma),writeln(Stream, '.').

  write_lemma(Stream, L) :-
    write(Stream, (:-)),write(Stream, ' '),write(Stream, L),writeln(Stream, '.').

%%%%%%%%%%%%%%%

% Génération de l'invariant de clôture pour P/N 
% sous forme de DNF de gr(Term) et ~gr(Term),
% syntaxe LPTP
%
% groundness_invariant(+P,+N,+Rias,-LptpFormula)


groundness_invariant(P,N,Rias,LPTPFormula) :-
  member(P/N-Vars-Cs,Rias), !,
  findall(Vars,(sat(Cs),labeling(Vars)),Model),
  model_formula(Model,P,Vars,LPTPFormula).

model_formula([],P,Vars,L) :-
  H =.. [P|Vars],
  L = (all Vars: (fails H)).
model_formula([S|Solns],P,Vars,L) :-
  H =.. [P|Vars],
  sols_vars_dnf([S|Solns],Vars,DNF),
  gen_formula(DNF,H,Vars,L).
      
  gen_formula(tt,H,Vars,all Vars : (succeeds H)).
  gen_formula(gr(Var),H,Vars,all Vars : (succeeds H => gr(Var))).
  gen_formula(Cs & C,H,Vars,all Vars : (succeeds H => Cs & C)).
  gen_formula(Ds \/ C,H,Vars,all Vars : (succeeds H => Ds \/ C)).
    
sols_vars_dnf([Sol|Solns],Vars,Cond) :-
  sols_vars_dnf_aux(Solns,Sol,Vars,Cond).
    
  sols_vars_dnf_aux([],Sol,Vars,Cond) :-
    sol_vars_cond(Sol,Vars,Cond).
  sols_vars_dnf_aux([S1|Ss],Sol,Vars,Cond2 \/ Cond1) :-
    sol_vars_cond(Sol,Vars,Cond1),
    sols_vars_dnf_aux(Ss,S1,Vars,Cond2).

    sol_vars_cond([],_Vars,tt).
    sol_vars_cond([TF|TFs],Vars,Cs) :-
      sol_vars_cond_aux(TFs,TF,Vars,Cs).

      sol_vars_cond_aux([],TF,[X],C) :- sol_vars_cond1(TF,X,C).
      sol_vars_cond_aux([TF1|TFs],TF,[X|Xs],Cs & C) :- 
        sol_vars_cond1(TF,X,C),
        sol_vars_cond_aux(TFs,TF1,Xs,Cs).

        sol_vars_cond1(1,X,gr(X)).
        sol_vars_cond1(0,X,~ gr(X)).

%%%%%%%%%%%%
% build_lemmas(+PIs,+Clauses,+Rias,-Ls) 
build_lemmas([],_,_,[]).
build_lemmas([P/N|PIs],Clauses,Rias,[L|Ls]) :-
  build_lemma(P,N,Clauses,Rias,L),
  build_lemmas(PIs,Clauses,Rias,Ls).

% build_lemmas(+PIs,+Clauses,+Rias,+Facts,-Ls)
build_lemmas([],_,_,_,[]).
build_lemmas([P/N|PIs],Clauses,Rias,Facts,[L|Ls]) :-
  build_lemma(P,N,Clauses,Rias,Facts,Lemma,L),
  Lemma = lemma(_, all _: Invariant, _PartialProof),
  (     Invariant = (fails _)
  ->    build_lemmas(PIs,Clauses,Rias,Facts,Ls)
  ;     build_lemmas(PIs,Clauses,Rias,[Lemma|Facts],Ls)   ).

% construction du lemme de clôture pour P/N en syntaxe LPTP
% généré à partir de l'invariant de clôture ci-dessus. 
% La preuve du lemme démarre effectivement par une induction au format LPTP. 
% En revanche, les preuves des cas de base et des cas inductifs
% ne sont pas présentes et remplacées par des ff by gap.
%
% build_lemma(+P,+N,-LptpLemma)

build_lemma(P,N,Clauses,Rias,Llptp) :-
  groundness_invariant(P,N,Rias,Invariant),
  %trace,
  build_lemma_aux(Invariant,P,N,Clauses,Llptp).

% build_lemma(+P,+N,+Facts,-LptpLemma)
build_lemma(P,N,Clauses,Rias,Facts,Lemma,Llptp) :-
  groundness_invariant(P,N,Rias,Invariant),
  %trace,
  build_lemma_aux(Invariant,P,N,Clauses,Facts,Lemma,Llptp).
  
  build_lemma_aux(Invariant,P,N,_Clauses,Llptp) :-
    Invariant=(all _: (fails _)), !,
    atom_concat(P,N,PN),gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, ff by gap),
    lptp_syntax(L,Llptp).
  build_lemma_aux(Invariant,P,N,Clauses,Llptp) :-
    Invariant=(all _: (succeeds _ => _DNF )), !,
    atom_concat(P,N,PN),gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant,PartialProof),
    build_outer_induction(P,N,Clauses,Invariant,PartialProof),
    lptp_syntax(L,Llptp).
  build_lemma_aux(Invariant,P,N,_Clauses,Llptp) :-
    Invariant=(all _: (succeeds _)), !,
    atom_concat(P,N,PN),gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, ff by gap),
    lptp_syntax(L,Llptp).

  build_lemma_aux(Invariant,P,N,_Clauses,Facts,L,Llptp) :-
    Invariant=(all _: (fails _)), !,
    atom_concat(P,N,PN),
    reset_gensym(PN),
    gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, ff by gap),
    lptp_syntax(L,Facts,Llptp).
  build_lemma_aux(Invariant,P,N,Clauses,Facts,L,Llptp) :-
    Invariant=(all _: (succeeds _ => _DNF )), !,
    atom_concat(P,N,PN),
    reset_gensym(PN),
    gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant,PartialProof),
    build_outer_induction(P,N,Clauses,Invariant,PartialProof),
    lptp_syntax(L,Facts,Llptp).
  build_lemma_aux(Invariant,P,N,_Clauses,Facts,L,Llptp) :-
    Invariant=(all _: (succeeds _)), !,
    atom_concat(P,N,PN),
    reset_gensym(PN),
    gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, ff by gap),
    lptp_syntax(L,Facts,Llptp).

build_outer_induction(P,N,Clauses,Invariant,PartialProof) :-
  %write_list(Clauses),
  PartialProof = induction([Invariant],Steps),
  get_clauses(Clauses,P,N,L), % L = the P/N clauses in the same order of Clauses
  build_steps(L,Invariant,Steps).

  get_clauses(Clauses,P,N,L) :- get_clauses(Clauses,P,N,[],L).
  
    get_clauses([],_P,_N,L1,L2) :- reverse(L1,L2).
    get_clauses([Cl|Cls],P,N,L1,L2) :-
      Cl = (H :- B), functor(H,P,N), !, round_list(B,Bs), get_clauses(Cls,P,N,[H-Bs|L1],L2).
    get_clauses([Cl|Cls],P,N,L1,L2) :-
      Cl = H, functor(H,P,N), !, get_clauses(Cls,P,N,[H-[]|L1],L2).
    get_clauses([_Cl|Cls],P,N,L1,L2) :-
      get_clauses(Cls,P,N,L1,L2).
    
  round_list((A,As),[A|Bs]) :- !, round_list(As,Bs).
  round_list(true,[]) :- !.
  round_list(A,[A]).
    
  build_steps([],_,[]).
  build_steps([Cl|Cls],Invariant,[Step|Steps]) :-
    copy_term(Invariant,Invariantc),
    build_step(Cl,Invariantc,Step),
    build_steps(Cls,Invariant,Steps).

    build_step(H-Bs,Inv,step(Vars,Hyp,ff by gap,DNF)) :-
      copy_term(Inv,Invc),
      Inv = (all _Vars: (succeeds H => DNF)),
      functor(H,P,N),
      term_variables(H-Bs,Vars),
      build_step_aux(Bs,P,N,Invc,Hyps,SUs),
      append(Hyps,SUs,Hyp).

      build_step_aux([],_P,_N,_Inv,[],[]).
      build_step_aux([Atom|Bs],P,N,Inv,Hyps,[Atom|SUs]) :-
        functor(Atom,=,2), !,
        log__info('atom cut', [Hyps|[Atom|SUs]]),
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).
      build_step_aux([Atom|Bs],P,N,Inv,[DNF|Hyps],[SU|SUs]) :-
        functor(Atom,P,N), !,
        copy_term(Inv,(all _VarsInvc: (succeeds Atom => DNF))),
        (   Atom = (\+ Left = Right)
        ->  SU = (Left <> Right)
        ;   Atom = (\+ RestAtom),
            SU = (fails RestAtom)
        ;   SU = (succeeds Atom)  ),
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).
      build_step_aux([Atom|Bs],P,N,Inv,Hyps,[SU|SUs]) :-
        functor(Atom,Q,M), dif(P/N,Q/M),
        (   Atom = (\+ Left = Right)
        ->  SU = (Left <> Right)
        ;   Atom = (\+ RestAtom),
            SU = (fails RestAtom)
        ;   SU = (succeeds Atom)  ),
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).

lptp_syntax(L,Llptp) :-
  term_variables(L,Vars), 
  lptp_vars(Vars),
  remove_qm(L,Llptp).

lptp_syntax(L,Facts,Llptp) :-
  copy_term(L, LCopy),
  term_variables(LCopy,Vars),
  lptp_vars(Vars),
  remove_qm(LCopy,Facts,Llptp).

lptp_vars(Vars) :- 
  reset_gensym(x), 
  lptp_vars_aux(Vars).

  lptp_vars_aux([]).
  lptp_vars_aux([?X|Xs]) :- 
    gensym(x,X), 
    lptp_vars_aux(Xs).

/* Removing question mark */
remove_qm(lemma(Name,all Vars1:F,ff by gap),
          lemma(Name,all Vars2:F,ff by gap)) :-
  remove_qm_vars(Vars1,Vars2).
remove_qm(lemma(Name,all Vars1:F,induction([all Vars1:F],Steps1)),
          lemma(Name,all Vars2:F,induction([all Vars2:F],Steps2))) :-
  remove_qm_vars(Vars1,Vars2),
  remove_qm_steps(Steps1,Steps2).

/* Removing question mark with facts */
remove_qm(lemma(Name,all Vars1:F,ff by gap),_Facts,
          lemma(Name,all Vars2:G,ff by gap)) :-
  copy_term(Vars1,Vars1Copy),
  copy_term(F,G),
  remove_qm_vars(Vars1Copy,Vars2).
remove_qm(lemma(Name,all Vars1:F,induction([all Vars1:F],Steps1)),Facts,
          lemma(Name,all Vars2:G,induction([all Vars2:G],Steps2))) :-
  copy_term(Vars1,Vars1Copy),
  copy_term(F,G),
  remove_qm_vars(Vars1Copy,Vars2),
  copy_term(Steps1,Steps1Copy),
  remove_qm_steps(Steps1Copy,Facts,Steps2).
  
  remove_qm_vars([],[]).
  remove_qm_vars([?X|Xs],[X|Ys]) :- remove_qm_vars(Xs,Ys).
  
  remove_qm_steps([],[]).
  remove_qm_steps([step(Vars,Hs,Deriv,Conc)|Ss],[step(VarsNoQM,Hs,Deriv,Conc)|SNQMs]) :-
    remove_qm_vars(Vars,VarsNoQM),
    remove_qm_steps(Ss,SNQMs).

  remove_qm_steps([],_Facts,[]).
  remove_qm_steps([step(Vars,Hs,Deriv,Conc)|Ss],Facts,[step(VarsNoQM,Hs,Derivation,Conc)|SNQMs]) :-
    remove_qm_vars(Vars,VarsNoQM),

    log__info('Hs', Hs),

    invariant_from_facts_and_hypothesis(Hs, Facts, Proofs, DNF),

    log__info('DNF', DNF),
    log__info('Form', DNF => Conc),
    log__info('Proofs', Proofs),

    (   DNF = []
    ->  once(derive_groundness_property(Conc, VarsNoQM, DerivationCases))
    ;   once(derive_groundness_property( DNF  => Conc, VarsNoQM, DerivationCases))
    ;   DerivationCases = Deriv ),

    (   Proofs = []
    ->  Derivation = DerivationCases
    ;   append(Proofs, DerivationCases, Derivation) ),

    remove_qm_steps(Ss,Facts,SNQMs).

    invariant_from_facts_and_hypothesis([], _Facts, [], []).
    invariant_from_facts_and_hypothesis([SU], Facts, Proofs, Conjunction) :-
        match_succeed_clause_with_fact(SU, Facts, Proofs, Conjunction)
        ->  true
        ;   Proofs = [],
            Conjunction = [].
    invariant_from_facts_and_hypothesis([SU|SUs], Facts, Proofs, Conjunction) :-
        SU \= (succeeds _)
        ->  invariant_from_facts_and_hypothesis(SUs, Facts, SubProofs, SubConjunction),
            (   SubConjunction = []
            ->
                (   matching_dnf(SU)
                ->  Conjunction = SU,
                    Proofs = SubProofs
                ;   SU = ( Left = Right )
                ->  Conjunction = ( gr(Left) <=> gr(Right) ),
                    Proofs = [gr(Right) => gr(Left)|[gr(Left) => gr(Right)|SubProofs]]
                ;   Conjunction = [],
                    Proofs = SubProofs )
            ;
                (   matching_dnf(SU)
                ->  Conjunction = (SU & SubConjunction),
                    Proofs = SubProofs
                ;   SU = ( Left = Right )
                ->  Conjunction = ( SubConjunction & ( gr(Left) <=> gr(Right) ) ),
                    Proofs = [gr(Right) => gr(Left)|[gr(Left) => gr(Right)|SubProofs]]
                ;   Conjunction = SubConjunction,
                    Proofs = SubProofs) )
        ;   match_succeed_clause_with_fact(SU, Facts, Proof, InvariantConjunction),
            invariant_from_facts_and_hypothesis(SUs, Facts, SubProofs, SubConjunction),
            append(Proof, SubProofs, Proofs),
            (   SubConjunction = []
            ->  Conjunction = InvariantConjunction
            ;   InvariantConjunction = []
            ->  Conjunction = SubConjunction
            ;   Conjunction = (InvariantConjunction & SubConjunction) ).

            matching_dnf(Form) :- matching_conjunction(Form).
            matching_dnf(Form) :-
                (
                    matching_conjunction(Form)
                ;
                    Form = Left \/ Right,
                    matching_dnf(Left),
                    matching_dnf(Right)
                ).

                matching_conjunction(~ gr(_)).
                matching_conjunction(gr(_)).
                matching_conjunction(Form) :-
                    Form = Left & Right,
                    matching_conjunction(Left),
                    matching_conjunction(Right).

        match_succeed_clause_with_fact(_SU, [], [], []).
        match_succeed_clause_with_fact(SU, [Fact|Facts], Proof, InvariantConjunction) :-
            SU = (succeeds Atom),
            Atom =.. [P|Args],

            copy_term(Fact, FactCopy),
            FactCopy = lemma(Name, all _Vars: (succeeds LemmaAtom => Invariant), _PartialProof),
            ByLemma = (succeeds LemmaAtom => Invariant by lemma(Name)),
            LemmaAtom =.. [FactPred|FactArgs],

            ( ( P = FactPred,
                length(Args, ArgsLength),
                length(FactArgs, FactArgsLength),
                FactArgsLength = ArgsLength,
                unifiable(Args, FactArgs, Unifier) )
            ->  (
                Proof = [ByLemma],
                InvariantConjunction = Invariant,
                apply_unification(Unifier)
            )
            ;   match_succeed_clause_with_fact(SU, Facts, Proof, InvariantConjunction) ).

            apply_unification([]).
            apply_unification([Var=Value|Unifier]) :-
                % log__info('unifier', [Var=Value|Unifier]),
                Var = Value,
                apply_unification(Unifier).

/*
?- build_lemma(revers,2,L),write(L),fail.

lemma(revers21,
  all[x1,x2]:(succeeds revers(?x1,?x2)=>gr(?x2)&gr(?x1)\/ ~gr(?x2)& ~gr(?x1)),
  induction([all[x1,x2]:(succeeds revers(?x1,?x2)=>gr(?x2)&gr(?x1)\/ ~gr(?x2)& ~gr(?x1))],
    [
      step(
        [], 
        [],
        ff by gap,
        gr([])&gr([])\/ ~gr([])& ~gr([])),
      step(
        [x3,x4,x5,x6],
        [gr(?x6)&gr(?x4)\/ ~gr(?x6)& ~gr(?x4),succeeds revers(?x4,?x6),succeeds appen(?x6,[?x3],?x5)],
        ff by gap,
        gr(?x5)&gr([?x3|?x4])\/ ~gr(?x5)& ~gr([?x3|?x4]))
    ]
  )
)
false.


?- build_lemma(appen,3,L),numbervars(L,0,_),write(L),fail.
    
lemma(appen33,
  all[x1,x2,x3]:
    (succeeds appen(?x1,?x2,?x3) => 
     gr(?x3)&gr(?x2)&gr(?x1)\/ ~gr(?x3)& ~gr(?x2)&gr(?x1)\/ ~gr(?x3)&gr(?x2)& ~gr(?x1)\/ ~gr(?x3)& ~gr(?x2)& ~gr(?x1)),
  induction(
    [all[x1,x2,x3]:
      (succeeds appen(?x1,?x2,?x3) =>
      gr(?x3)&gr(?x2)&gr(?x1)\/ ~gr(?x3)& ~gr(?x2)&gr(?x1)\/ ~gr(?x3)&gr(?x2)& ~gr(?x1)\/ ~gr(?x3)& ~gr(?x2)& ~gr(?x1))],
    [
     step(
      [x4],
      [],
      ff by gap,
      gr(?x4)&gr(?x4)&gr([])\/ ~gr(?x4)& ~gr(?x4)&gr([])\/ ~gr(?x4)&gr(?x4)& ~gr([])\/ ~gr(?x4)& ~gr(?x4)& ~gr([])),
    
     step(
      [x5,x6,x7,x8],
      [gr(?x8)&gr(?x7)&gr(?x6)\/ ~gr(?x8)& ~gr(?x7)&gr(?x6)\/ ~gr(?x8)&gr(?x7)& ~gr(?x6)\/ ~gr(?x8)& ~gr(?x7)& ~gr(?x6),
       succeeds appen(?x6,?x7,?x8)],
      ff by gap,
      gr([?x5|?x8])&gr(?x7)&gr([?x5|?x6])\/ ~gr([?x5|?x8])& ~gr(?x7)&gr([?x5|?x6])\/ 
      ~gr([?x5|?x8])&gr(?x7)& ~gr([?x5|?x6])\/ ~gr([?x5|?x8])& ~gr(?x7)& ~gr([?x5|?x6]))
    ]
  )
)
false.

*/
  
 
/*
:- initialize.
:- compile_gr(F).    
:- needs_gr(F).
...    
:- bye.
    
*/
 
  
