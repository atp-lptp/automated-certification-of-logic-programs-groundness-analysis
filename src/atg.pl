
atg__axiom_2_5(Form, FormL2) :-
	Form = [gr,[n(_,_)|TermL]],
	obj__pure_termL(TermL),
	eq__add_free_boundL(TermL,[],[],XL),
	cmp__map_gr(XL,[],FormL),
	tac__add(m,Form,FormL,FormL2).

atg__autoground(pending,_,_,Form,Form) :-
	db__flag(autoground),
	Form = [gr|_],
	ctl__warning([autoground,tactic,pending]).
atg__autoground(check,V,Gamma,Form,Form2) :-
	db__flag(autoground),
	Form = [gr|_],
	(
		atg__expand(Gamma,[],Gamma2),
		atg__simplifyL(Gamma2,Gamma2,[],Gamma3),
		pr__derivable_once(V,Gamma3,Form)
	)
	->	ctl__message([autoground,tactic,succesfully,checked]),
		atg__suggest(Gamma3),
		Form2 = Form
	;	ctl__warning([autoground,tactic,fails]),
		Form2 = [].

atg__equiv_to_impl(Form, FormL) :-
	Form = [<=>,Form1,Form2],
	FormL = [Form,[=>,Form1,Form2],[=>,Form2,Form1]].

atg__expand([], FormL, FormL).
atg__expand([Form|FormL], Form1L, Form3L) :-
	(
		atg__match_fact_assumption(Form, ExpandedForm)
	->  atg__expand(FormL, ExpandedForm, FormL2)
	;   atg__axiom_2_5(Form, ExpandedForm)
	->	atg__expand(FormL, ExpandedForm, FormL2)
	; 	atg__equiv_to_impl(Form, ExpandedForm)
	->  atg__expand(FormL, ExpandedForm, FormL2)
	;	atg__expand(FormL, [Form], FormL2)
	),
	lst__append_set(Form1L, FormL2, Form3L).

atg__include(_, [], _).
atg__include(Prefix, Form, FormL) :-
	Form = [Prefix|_]
	->	FormL = [Form]
	; 	FormL = [].

atg__includeL(_, [], FormL, FormL).
atg__includeL(Prefix, [Form|FormL], Acc, Form2L) :-
	atg__include(Prefix, Form, Form1L),
	lst__append_set(Form1L, Acc, NextAcc),
	atg__includeL(Prefix, FormL, NextAcc, Form2L).

atg__expand(FormL, Form3L) :-
	atg__expand(FormL, [], ExpandedFormL),

	(
		FormL = ExpandedFormL
	->
		Form3L = FormL
	;
		atg__expand(ExpandedFormL, Form3L)
	).

atg__elim_imply(Form,Gamma,ImplyElim) :-
	Form = ['=>'|_],
	atg__match_conclusion(Form,Gamma,ImplyElim).

atg__elim_and(Form,AndElim) :-
	Form = ['&'|AndElim].

atg__simplify(Assumption,Gamma,AssumptionL) :-
	(
		atg__elim_imply(Assumption,Gamma,ImplyElim)
	->	AssumptionL = [ImplyElim]
	;	atg__elim_and(Assumption,AndElim)
	->	AssumptionL = AndElim
	; 	AssumptionL = []
	),
	( \+ lst__list_form(AssumptionL)
	-> log__info("ERROR", AssumptionL)
	; true ).

atg__non_empty_list(Form) :-
	lst__list_form(Form),
	\+ Form = [].

atg__empty_list(Form) :-
	lst__list_form(Form),
	Form = [].

atg__conjunctions_left(Gamma) :-
	once(atg__includeL('&', Gamma, [], Conjunctions)),
	atg__non_empty_list(Conjunctions).

atg__simplifyL([],_Gamma,AssumptionL,AssumptionL).
atg__simplifyL([Assumption|AssumptionL],Gamma,In,AssumptionL4) :-
	atg__simplify(Assumption,Gamma,AssumptionL1),
	lst__append_set(AssumptionL1, In, AssumptionL2),

	(
		(
			atg__empty_list(AssumptionL),
			atg__conjunctions_left(AssumptionL2)
		)
		->
			lst__append_set(Gamma, AssumptionL2, Gamma2),
			atg__simplifyL(AssumptionL2, Gamma2, [], AssumptionL3),
			lst__append_set(Gamma2, AssumptionL3, AssumptionL4)
		;
			atg__simplifyL(AssumptionL,Gamma,AssumptionL2,AssumptionL4)
	).

atg__suggest(Deriv) :-
	current_prolog_flag(test_environment, true)
	-> 	true
	;
		once(i2e__derivation(Deriv,X)),
		nl, write('======'), nl,
		Left = 0,
		prt__text_width(Right),
		prt__write(X,Left,Right), nl,
		write('======'), nl
	.

atg__match_conclusion([=>,Form1,Form2],Gamma,Form2) :-
	Form1 = [gr|_],
	pr__derivable_once([],Gamma,Form1),
	once(ai__backward_add(Form2,[=>,Form1,Form2],[],Gamma,d,[],0)).

atg__match_fact_assumption(Assumption,Deriv4) :-
	Assumption = [succeeds|_],
	tac__db_select(X,@(all,BV,[=>,Form2,Form3])),
	pr__match_assumption([Assumption],Form2,BV,[],Sub),
	eq__apply_plain(Form3,Sub,Form4),
	\+ lst__member_con(Form4,[Assumption]),
	atg__expand([Form4], [], ExpandedForm4),
	lst__append_set([by(Form4,X)],ExpandedForm4,Deriv3),
	lst__append_set([Assumption],Deriv3,Deriv4).

atg__match_fact_assumptionL([],Deriv,Deriv).
atg__match_fact_assumptionL([Assumption|AssumptionL],Deriv2,DerivOut) :-
	( atg__match_fact_assumption(Assumption,Deriv1)
	-> atg__match_fact_assumptionL(AssumptionL,Deriv1,Deriv3)
	; atg__match_fact_assumptionL(AssumptionL,[Assumption],Deriv3)
	),
	lst__append_set(Deriv3,Deriv2,DerivOut).

atg__tear_down :-
	abolish(db__theorem/2),
	abolish(db__lemma/2),
	abolish(db__corollary/2),
	abolish(db__axiom/2),
	abolish(db__pred/2),
	abolish(db__fun/3),
	abolish(db__clauses/2),
	abolish(db__depends/2),
	assert(db__theorem('DUMMY',[&])),
	assert(db__lemma('DUMMY',[&])),
	assert(db__corollary('DUMMY',[&])),
	assert(db__axiom('DUMMY',[&])),
	assert(db__pred([d('DUMMY',0)],[&])),
	assert(db__fun([f('DUMMY',0)],[&],[&])),
	assert(db__clauses(n(fail,0),[])),
	assert(db__depends('DUMMY',[])).
