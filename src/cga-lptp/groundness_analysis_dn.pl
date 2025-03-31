:- module(groundness_analysis_dn, [
  load_op/0,
  groundness_analysis/4,
  % groundness_analysis_lptp/2,
  groundness_analysis_dn_lptp/2
]).

% From LPTP
:- op(980, xfy, by).	
:- op(970, xfy, :).
:- op(960, yfx, <=>).	
:- op(950, xfy, =>).
:- op(940, yfx, \/).
:- op(930, yfx, &).
:- op(900, fy,  ~).
:- op(900, fy, succeeds).		
:- op(900, fy, fails).		
:- op(800, fy, all).
:- op(800, fy, ex).		
:- op(100, fy, ?).

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
%:- use_module(ax4_ax5).

:- use_module('../prover/mod_lptp').
:- use_module('../prover/prover').
:- use_module('../prover/prover_alt').
:- use_module('../prover/prover_dslplm').
:- use_module('../prover/dn_prover').

load_op :- 
  op(980, xfy, by), op(970, xfy, :), op(950, xfy, =>), op(940, yfx, \/),
  op(930, yfx, &), op(900, fy,  ~), op(800, fy,  all), op(900, fy,  succeeds),
  op(900, fy,  fails), op(800, fy,  all),op(800,fy,ex), op(100, fy,  ?).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% groundness_analysis(+FileName,-Clauses,-Sccs,-RelsGroundness) 

groundness_analysis(FileName,Clauses,Sccs,RelsGroundness) :-
    %trace,  
    file_clauses(FileName,Clauses),
    %
    prologs_flatprologs(Clauses,FPClauses),
    %write_list(FPClauses),
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
    TimeOut = 3600,
    tp(SccsClsB,bool_op,no_widening,BaseBool,[star-union],TimeOut),
    assoc_to_list(BaseBool,RelsInterArgsBool), 
    %write_list(RelsInterArgsBool),
    rias_groundness(RelsInterArgsBool,RelsGroundness),
    %write_list(RelsGroundness),
    true.
    
rias_groundness([],[]).
rias_groundness([P/N-(Vars-BoolF-_X-_Y)|Rias],[P/N-Vars-BoolF|RGs]) :-
    rias_groundness(Rias,RGs).

% groundness_analysis('Filex/apprev.pl',Cs,Ss,Rs).
% Cs = [app([], _A, _A), (app([_B|_C], _D, [_B|_E]):-app(_C, _D, _E)), rev([], []), 
%      (rev([_F|_G], _H):-rev(_G, _I), app(_I, [_F], _H))],
% Ss = [[app/3], [rev/2]],
% Rs = [app/3-[_J, _K, _L]-(_L=:=_K*_J), rev/2-[_M, _N]-(_N=:=_M)*1].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% groundness_analysis_lptp(+FileName,-Lemmas)

groundness_analysis_dn_lptp(FileName,Lemmas) :-
    groundness_analysis_lptp(FileName,Lemmas).

groundness_analysis_lptp(FileName,Lemmas) :-
%  print_red('% Boolean fixpoint computation:'), nl,
%  time(groundness_analysis(FileName,Clauses0,Sccs,RelsInterArgsBool)),
  groundness_analysis(FileName,Clauses0,Sccs,RelsInterArgsBool),
  % write_list(RelsInterArgsBool),
  append(Sccs,PIs),
  reverse(Clauses0,Clauses),

  %
%  print_red('% Conversion to LPTP:'), nl,
  % time(build_lemmas(PIs,Clauses,RelsInterArgsBool,Lemmas)).
  % Added facts lists as as 4th argument
  build_lemmas(PIs,Clauses,RelsInterArgsBool,[],Lemmas).
%  time(build_lemmas(PIs,Clauses,RelsInterArgsBool,[],Lemmas)).

% groundness_analysis_lptp('Filex/apprev.pl',L),write_lemmas(user,L),fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_red(Text) :- format('\e[31m~w\e[0m', [Text]). % from ChatGPT!
% groundness_analysis:print_red('Red'),nl.
       
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% write_lemmas(+Stream,+Ls)

write_lemmas(Stream,[]) :- nl(Stream).
write_lemmas(Stream,[L|Ls]) :- nl(Stream),write_lemma(Stream,L),write_lemmas(Stream,Ls).
 
  write_lemma(Stream,L) :- write(Stream,(:-)),write(Stream,' '),write(Stream,L),writeln(Stream,'.').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Génération de l'invariant de clôture pour P/N 
% sous forme de DNF de gr(Term) et ~gr(Term), syntaxe LPTP
%
% groundness_invariant(+P,+N,+Rias,-LptpFormula)

groundness_invariant(P,N,Rias,LPTPFormula) :-
  member(P/N-Vars-Cs,Rias), !,
  groundness_invariant_aux(Cs,P,Vars,LPTPFormula).

  groundness_invariant_aux(F,P,Vars,all Vars : succeeds H => ff) :- F == 0, !, H =.. [P|Vars].
  groundness_invariant_aux(F,P,Vars,all Vars : succeeds H => tt) :- F == 1, !, H =.. [P|Vars].
  groundness_invariant_aux(Cs,P,Vars,LPTPFormula) :-
    findall(Vars,(sat(Cs),labeling(Vars)),Model),  % complexité exponentielle en N !
    model_formula(Model,P,Vars,LPTPFormula).

model_formula([S|Solns],P,Vars,L) :-
  H =.. [P|Vars],
  sols_vars_dnf([S|Solns],Vars,DNF),
  gen_formula(DNF,H,Vars,L).
      
  gen_formula(gr(Var),H,Vars,all Vars : (succeeds H => gr(Var))).
  gen_formula(~ F,H,Vars,all Vars : (succeeds H => ~ F)).
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
        sol_vars_cond1(0,X,gr(X) => ff).

/*
        
?- groundness_analysis:groundness_invariant(p,3,[p/3-[X,Y,Z]-(Z=:=X*Y)],LptpF).
all[_9586,_9592,_9598]:succeeds p(_9586,_9592,_9598)=>
        gr(_9598)&gr(_9592)&gr(_9586)\/ 
        ~gr(_9598)& ~gr(_9592)&gr(_9586)\/ 
        ~gr(_9598)&gr(_9592)& ~gr(_9586)\/ 
        ~gr(_9598)& ~gr(_9592)& ~gr(_9586)


?- groundness_analysis:groundness_invariant(p,3,[p/3-[X,Y,Z]-0],LptpF).
all[_11668,_11674,_11680]:succeeds p(_11668,_11674,_11680)=>ff
      
?- groundness_analysis:groundness_invariant(p,3,[p/3-[X,Y,Z]-1],LptpF).
all[_20294,_20300,_20306]:succeeds p(_20294,_20300,_20306)=>tt

% app/3-[A,B,C]-(C=:=B*A).
% member/2-[A,B]-C^(B=:=A*C).
% rev/2-[A,B]-(B=:=A)*1.
% split/3-[A,B,C]- #(#(1,C*B),A).

*/
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% build_lemmas(+PIs,+Clauses,+Rias,-Ls) 

build_lemmas([],_,_,[]).
build_lemmas([P/N|PIs],Clauses,Rias,[L|Ls]) :-
  build_lemma(P,N,Clauses,Rias,L),
  build_lemmas(PIs,Clauses,Rias,Ls).

% /!\ with Facts
%% build_lemmas(+PIs,+Clauses,+Rias,+Facts,-Ls)
build_lemmas([],_,_,_,[]).
build_lemmas([P/N|PIs],Clauses,Rias,Facts,[L|Ls]) :-
  (     build_lemma(P,N,Clauses,Rias,Facts,Lemma,L)
  ->    true
        % writeln(built_lemma_successfully(P/N))
  ;     atom_concat(P,N,PN), gensym(PN,Lemma_Label),
        L = lemma(Lemma_Label, tt, []),
        writeln(failed_at_building_lemma_here(P/N)) ),
  Lemma = lemma(_, all _: Invariant, _PartialProof),
  (     Invariant = (fails _)
  ->    build_lemmas(PIs,Clauses,Rias,Facts,Ls)
  ;     build_lemmas(PIs,Clauses,Rias,[Lemma|Facts],Ls) ).

% construction du lemme de clôture pour P/N en syntaxe LPTP
% généré à partir de l'invariant de clôture ci-dessus. 
% La preuve du lemme démarre presque toujours par une induction au format LPTP. 
% En revanche, les preuves des cas de base et des cas inductifs
% ne sont pas présentes et remplacées par des ff by gap.
%
% build_lemma(+P,+N,+Clauses,+Rias,-LptpLemma)

build_lemma(P,N,Clauses,Rias,Llptp) :-
  groundness_invariant(P,N,Rias,Invariant),
  build_lemma_aux(Invariant,P,N,Clauses,Llptp).

% /!\ with Facts, and Lemma
% build_lemma(+P,+N,+Facts,-LptpLemma)
build_lemma(P,N,Clauses,Rias,Facts,Lemma,Llptp) :-
  groundness_invariant(P,N,Rias,Invariant),
  %trace,
  build_lemma_aux(Invariant,P,N,Clauses,Facts,Lemma,Llptp).

  %build_lemma_aux(Invariant,P,N,_Clauses,Llptp) :-
    %Invariant=(all _: (succeeds _ => ff)), !,
    %atom_concat(P,N,PN), gensym(PN,Lemma_Label),
    %L = lemma(Lemma_Label,Invariant, ff by gap),
    %lptp_syntax(L,Llptp).
  build_lemma_aux(Invariant,P,N,_Clauses,Llptp) :-
    Invariant=(all _: succeeds _ => tt), !,
    atom_concat(P,N,PN), gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, []), % to prove tt is true, the empty proof is fine!
    lptp_syntax(L,Llptp).
  build_lemma_aux(Invariant,P,N,Clauses,Llptp) :-
    Invariant=(all _: (succeeds _ => Cond )), dif(Cond,tt), !,
    atom_concat(P,N,PN), gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant,PartialProof),
    build_outer_induction(P,N,Clauses,Invariant,PartialProof),
    lptp_syntax(L,Llptp).

  % /!\ with Facts, and L(emma)
  % build_lemma_aux(+Invariant,+P,+N,-Clauses,+Facts,-L,-Llptp)
  build_lemma_aux(Invariant,P,N,_Clauses,Facts,L,Llptp) :-
    Invariant=(all _: succeeds _ => tt), !,
    atom_concat(P,N,PN), gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant, []), % to prove tt is true, the empty proof is fine!
    lptp_syntax(L,Facts,Llptp).
  build_lemma_aux(Invariant,P,N,Clauses,Facts,L,Llptp) :-
    Invariant=(all _: (succeeds _ => Cond )), dif(Cond,tt), !,
    atom_concat(P,N,PN), gensym(PN,Lemma_Label),
    L = lemma(Lemma_Label,Invariant,PartialProof),
    build_outer_induction(P,N,Clauses,Invariant,PartialProof),
    lptp_syntax(L,Facts,Llptp).

% build_outer_induction(+P,+N,+Clauses,+Invariant,-PartialProof)
build_outer_induction(P,N,Clauses,Invariant,PartialProof) :-
  %write_list(Clauses),
  PartialProof = induction([Invariant],Steps),
  get_clauses(Clauses,P,N,Lpn), 
  % Lpn = the clauses defining P/N in the same order of the original program
  % Lpn = [H1-B1s,H2,H3-B3s, ...]
  build_steps(Lpn,Invariant,Steps).
  
  % get_clauses(+Cls,+P,+N,-L)  
  get_clauses(Clauses,P,N,L) :- get_clauses(Clauses,P,N,[],L).
  
    get_clauses([],_P,_N,L1,L2) :- reverse(L1,L2).
    get_clauses([Cl|Cls],P,N,L1,L2) :-
      Cl = (H :- B), 
      functor(H,P,N), !, 
      round_list(B,Bs), 
      get_clauses(Cls,P,N,[H-Bs|L1],L2).
    get_clauses([Cl|Cls],P,N,L1,L2) :-
      Cl = H, 
      functor(H,P,N), !, 
      get_clauses(Cls,P,N,[H-[]|L1],L2).
    get_clauses([_Cl|Cls],P,N,L1,L2) :-
      get_clauses(Cls,P,N,L1,L2).
    
      round_list((A,As),[A|Bs]) :- !, round_list(As,Bs).
      round_list(true,[]) :- !.
      round_list(A,[A]).
    
  % build_steps(+Lpn,+Invariantpn,-Steps) 
  % Lpn = [H1-B1s,H2,H3-B3s, ...]
  % Invariant= all [X1,...,Xn] :succeeds p(X1,...,Xn) => DNF(X1,...,Xn)

  build_steps([],_,[]).
  build_steps([Cl|Cls],Invariant,[Step|Steps]) :-
    copy_term(Invariant,Invariantc),
    build_step(Cl,Invariantc,Step),
    build_steps(Cls,Invariant,Steps).
        
    build_step(H-Bs,Inv,step(Vars,Hyp,ff by gap,DNF)) :-
      copy_term(Inv,Invc),
      Invc = (all _Vars: (succeeds H => DNF)),
      functor(H,P,N),
      term_variables(H-Bs,Vars),
      build_step_aux(Bs,P,N,Inv,Hyps,SUs),
      append(Hyps,SUs,Hyp),  % normalize here? 
      %writeln(H-Bs-step(Vars,Hyp,ff by gap,DNF)),
      %trace,
      %collect_gr_from_hyps(Hyp,G1s), 
      %collect_gr_from_formula(DNF,G2s),
      %append(G1s,G2s,Grs),
      %get_inferences_from_ax4_ax5(Grs,Inferred_Equiv),
      %append(Hyps,Inferred_Equiv,Hyp_with_Equiv),
      %writeln(H-Bs-step(Vars,Hyp_with_Equiv,ff by gap,DNF)),
      true.
      
      % build_step_aux(+Bs,+P,+N,+Inv,Hyps,SUs)      
      build_step_aux([],_P,_N,_Inv,[],[]).
      build_step_aux([Atom|Bs],P,N,Inv,Hyps,[Atom|SUs]) :-
        functor(Atom,=,2), !,
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).
      build_step_aux([Atom|Bs],P,N,Inv,[DNF|Hyps],[succeeds Atom|SUs]) :-
        functor(Atom,P,N), !,
        copy_term(Inv,(all _VarsInvc: (succeeds Atom => DNF))),
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).
      build_step_aux([Atom|Bs],P,N,Inv,Hyps,[succeeds Atom|SUs]) :-
        functor(Atom,Q,M), dif(P/N,Q/M),
        build_step_aux(Bs,P,N,Inv,Hyps,SUs).

/*
      % collect_gr_from_hyps(+Hs,-Grs)
      collect_gr_from_hyps([],[]).
      collect_gr_from_hyps([H|Hs],Grs) :- collect_gr_from_formula(H,G),collect_gr_from_hyps(Hs,Gs),append(G,Gs,Grs).
      
      % collect_gr_from_formula(+CompoundTerm,-Grs)
      collect_gr_from_formula(gr(T),[gr(T)]).
      collect_gr_from_formula(tt,[]).
      collect_gr_from_formula(ff,[]).
      collect_gr_from_formula(~ F, Grs) :- collect_gr_from_formula(F, Grs).
      collect_gr_from_formula(succeeds _, []).
      collect_gr_from_formula(A => B, L) :- collect_gr_from_formula(A,L1),collect_gr_from_formula(B,L2), append(L1,L2,L).
      collect_gr_from_formula(A <=> B, L) :-  collect_gr_from_formula(A,L1),collect_gr_from_formula(B,L2), append(L1,L2,L).
      collect_gr_from_formula(A & As,L) :- collect_gr_from_formula(A,L1),collect_gr_from_formula(As,L2), append(L1,L2,L).
      collect_gr_from_formula(A \/ As,L) :- collect_gr_from_formula(A,L1),collect_gr_from_formula(As,L2), append(L1,L2,L).
      collect_gr_from_formula(all _:F,L) :- collect_gr_from_formula(F,L).
      collect_gr_from_formula(ex _:F,L) :- collect_gr_from_formula(F,L).
*/      

          
% lptp_syntax(+L,-Llptp)
lptp_syntax(L,Llptp) :-
  term_variables(L,Vars), 
  lptp_vars(Vars),
  remove_qm(L,Llptp).  

% /!\ with Facts
% lptp_syntax(+L,+Facts,-Llptp)
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

remove_qm(lemma(Name,all Vars1:F,ff by gap),lemma(Name,all Vars2:F,ff by gap)) :- !, 
  remove_qm_vars(Vars1,Vars2).
remove_qm(lemma(Name,all Vars1:F,[]),lemma(Name,all Vars2:F,[])) :- !, 
  remove_qm_vars(Vars1,Vars2).

% ==== REPLACED
%remove_qm(lemma(Name,all Vars1:F,induction([all Vars1:F],Steps1)),
%          lemma(Name,all Vars2:F,induction([all Vars2:F],Steps2))) :- !,
%  remove_qm_vars(Vars1,Vars2),
%  remove_qm_steps(Steps1,Steps2).
% ==== START
remove_qm(lemma(Name,all Vars1:F,induction([all Vars1:F],Steps1)),Facts,
          lemma(Name,all Vars2:G,induction([all Vars2:G],Steps2))) :-
  copy_term(Vars1,Vars1Copy),
  copy_term(F,G),
  remove_qm_vars(Vars1Copy,Vars2),
  copy_term(Steps1,Steps1Copy),
  remove_qm_steps(Steps1Copy,Facts,Steps2).
% ==== END

  remove_qm_vars([],[]).
  remove_qm_vars([?X|Xs],[X|Ys]) :- remove_qm_vars(Xs,Ys).
  
  remove_qm_steps([],[]).
  remove_qm_steps([step(Vars,Hs,Deriv,Conc)|Ss],[step(VarsNoQM,Hs,Deriv,Conc)|SNQMs]) :-
    remove_qm_vars(Vars,VarsNoQM),
    remove_qm_steps(Ss,SNQMs).

% changes from here

  remove_qm_steps([],_Facts,[]).
  remove_qm_steps([step(Vars,Hs,Deriv,Conc)|Ss],Facts,[step(VarsNoQM,Hs,Derivation,Conc)|SNQMs]) :-
    remove_qm_vars(Vars,VarsNoQM),

    log__info('Hs', Hs),

    invariant_from_facts_and_hypothesis(Hs, Facts, Proofs, DNF),

    log__info('DNF', DNF),
    log__info('Form', DNF => Conc),
    log__info('Proofs', Proofs),
    log__info('VarsNoQM', VarsNoQM),

%    (   bb_get(prover, alt)
%    -> ( once((   DNF = []
%            -> (
%                log__info(proving_base_case, [Conc]),
%                once(proof([], Conc, DerivationCases))
%            )
%            ; (
%                log__info(proving_induction_step, []),
%                log__info(to_show, [DNF => Conc]),
%                once(prover_dslplm:prove(
%                    [],
%                    DNF => Conc,
%                    DerivationCases
%                ))
%            )
%        ))
%        ->  true
%        ;   DerivationCases = [ff by gap],
%            (   DNF = []
%            ->  log__info(cannot_derive_base_case, [])
%            ;   log__info(cannot_derive_induction_step, []) )
%    )
%    ;  bb_get(prover, levy)
%    -> (
%        DNF = []
%        -> (
%            log__info(proving_base_case, [Conc]),
%            dn_prover:expand_gr(Conc, ExpandedConc),
%            log__info(expanded_conclusion, [ExpandedConc]),
%            once(prover_dslplm:prove([], ExpandedConc, DerivationCases))
%        )
%        ; (
%            log__info(proving_induction_step, []),
%            log__info(to_show, [DNF => Conc]),
%            dn_prover:expand_gr(DNF => Conc, ExpandedForm),
%            once(prover_dslplm:prove(
%                [],
%                ExpandedForm,
%                DerivationCases
%            ))
%        )
%    )
%    ;
%        Deriv = ff by gap,
%        DerivationCases = Deriv
%%        (   DNF = []
%%        ->  once(derive_groundness_property(Conc, VarsNoQM, DerivationCases))
%%        ;   once(derive_groundness_property( DNF  => Conc, VarsNoQM, DerivationCases))
%%        ;   DerivationCases = Deriv )
%    ),


    % Huth & Ryan
%    Deriv = (ff by gap),
%    (   DNF = []
%    ->  once(derive_groundness_property(Conc, VarsNoQM, DerivationCases))
%    ;   once(derive_groundness_property( DNF  => Conc, VarsNoQM, DerivationCases))
%    ;   DerivationCases = Deriv ),
%

    % ff by gap left as is
    Deriv = (ff by gap),
%    (   DNF = []
%    ->  once(derive_groundness_property(Conc, VarsNoQM, DerivationCases))
%    ;   once(derive_groundness_property( DNF  => Conc, VarsNoQM, DerivationCases))
    DerivationCases = [Deriv],

%    dn_prover:expand_gr(Conc, ExpandedConc),

    % Levy
%    Deriv = (ff by gap),
%    (   DNF = []
%    ->  once(dn_prover:proof([], ExpandedConc, DerivationCases))
%    ;
%        dn_prover:expand_gr(DNF, ExpandedDNF),
%        once(dn_prover:proof([ExpandedDNF], ExpandedConc, DerivationCases))
%    ;   DerivationCases = [Deriv] ),
%
%    Deriv = (ff by gap),
%    (   DNF = []
%    ->  once(prover_alt:proof([], ExpandedConc, DerivationCases))
%    ;
%        dn_prover:expand_gr(DNF, ExpandedDNF),
%        writeln(dnf(DNF)),
%        writeln(expanded_dnf(ExpandedDNF)),
%        once(prover_alt:proof(ExpandedDNF, ExpandedConc, DerivationCases))
%    ;   DerivationCases = [Deriv] ),
%
%    (   DNF = []
%    ->  once(prover_dslplm:prove([], ExpandedConc, DerivationCases))
%    ;
%        prover_dslplm:expand_gr(DNF, ExpandedDNF),
%        once(prover_dslplm:prove([ExpandedDNF], ExpandedConc, DerivationCases))
%    ;   DerivationCases = [Deriv] ),

    %DerivationCases = Deriv

    % writeq(Proofs), nl,
    % writeq(DerivationCases), nl,

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
                    Form = ( Left \/ Right ),
                    matching_dnf(Left),
                    matching_dnf(Right)
                ).

                matching_conjunction(~ gr(_A)).
                matching_conjunction(gr(_B)).
                matching_conjunction(Form) :-
                    Form = ( Left & Right ),
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
?- build_lemmas([p/1],[p(a),(p(X) :- p(X))], [p/1-[Var]-0],L),writeln(L),fail.
[lemma(p11,all([x1]):(succeeds(p(?(x1)))=>ff),by(ff,gap))]
false.

?- build_lemmas([p/1],[p(a),(p(X) :- p(X))], [p/1-[Var]-1],L),writeln(L),fail.
[lemma(p12,all([x1]):(succeeds(p(?(x1)))=>tt),[])]
false.

?- build_lemmas([p/1],[p(a),(p(X) :- p(X))], [p/1-[Var]-Var],L),writeln(L),fail.
[lemma(p134,all[x1]:succeeds p(?x1)=>gr(?x1),
    induction([all[x1]:succeeds p(?x1)=>gr(?x1)],
    [step([],[],ff by gap,gr(a)),
     step([x2],[gr(?x2),succeeds p(?x2)],ff by gap,gr(?x2))]))]
false.
*/

   
/* Structure minimale d'un fichier .pr
:- initialize.
:- compile_gr(F).    
:- needs_gr(F).
...    
:- bye.
    
*/
    

