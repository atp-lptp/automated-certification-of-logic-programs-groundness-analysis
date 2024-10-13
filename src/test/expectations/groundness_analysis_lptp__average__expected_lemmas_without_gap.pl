[lemma(p21,
  all [x1,x2]: 
   (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],
     [gr(0) & gr(0),
      gr(0) & gr(0) \/ ~ gr(0) & ~ gr(0)],
     gr(0) & gr(0) \/ ~ gr(0) & ~ gr(0)),
    step([x3],[],
     [cases(gr(?x3),
       [gr([?x3]) <=> gr(?x3) by lemma(axiom_2_5_single_element_list),
        gr(?x3) => gr(s(?x3)),
        assume(~ gr([?x3]),
         contra(gr(s(?x3)),
          [gr(s(?x3)),
           gr([?x3]),
           ff]),
         ~ gr(s(?x3))),
        gr(?x3) & gr(s(?x3)),
        gr(?x3) & gr(s(?x3)) \/ ~ gr(?x3) & ~ gr(s(?x3))],
       ~ gr(?x3),
       [~ gr([?x3]) <=> ~ gr(?x3) by 
         lemma(axiom_2_5_single_element_list_de_morgan),
        gr(?x3) => gr(s(?x3)),
        assume(~ gr([?x3]),
         contra(gr(s(?x3)),
          [gr(s(?x3)),
           gr([?x3]),
           ff]),
         ~ gr(s(?x3))),
        ~ gr(?x3) & ~ gr(s(?x3)),
        gr(?x3) & gr(s(?x3)) \/ ~ gr(?x3) & ~ gr(s(?x3))],
       gr(?x3) & gr(s(?x3)) \/ ~ gr(?x3) & ~ gr(s(?x3)))],
     gr(?x3) & gr(s(?x3)) \/ ~ gr(?x3) & ~ gr(s(?x3)))])),
 lemma(eq21,
  all [x1,x2]: 
   (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([x3],[],
     [cases(gr(?x3),
       [gr(?x3) & gr(?x3),
        gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3)],
       ~ gr(?x3),
       [~ gr(?x3) & ~ gr(?x3),
        gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3)],
       gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3))],
     gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3))])),
 lemma(average31,
  all [x1,x2,x3]: 
   (succeeds average(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds average(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1))],
   [step([x4],
     [succeeds !,
      succeeds eq(?x4,0)],
     [succeeds eq(?x4,0) => gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4) by 
       lemma(eq21),
      cases(gr(?x4),
       [gr(0) & gr(?x4),
        gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4),
        gr(?x4) & gr(0),
        gr(?x4) & gr(0) & gr(0),
        assume(gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4),[],
         gr(?x4) & gr(0) & gr(0))],
       ~ gr(?x4),
       [contra(gr(0) & gr(?x4),[]),
        ~ (gr(0) & gr(?x4)),
        contra(~ gr(0) & ~ gr(?x4),
         [gr(0),
          ~ gr(0),
          ff]),
        ~ (~ gr(0) & ~ gr(?x4)),
        contra(gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4),
         cases(
          [case(~ gr(0) & ~ gr(?x4),
            [~ gr(0) & ~ gr(?x4),
             ~ (~ gr(0) & ~ gr(?x4)),
             ff]),
           case(gr(0) & gr(?x4),
            [gr(0) & gr(?x4),
             ~ (gr(0) & gr(?x4)),
             ff])],
          ff)),
        ~ (gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4)),
        assume(gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4),[],
         gr(?x4) & gr(0) & gr(0))],
       gr(0) & gr(?x4) \/ ~ gr(0) & ~ gr(?x4) => gr(?x4) & gr(0) & gr(0))],
     gr(?x4) & gr(0) & gr(0)),
    step([x5],
     [succeeds !,
      succeeds eq(?x5,0)],
     [succeeds eq(?x5,0) => gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5) by 
       lemma(eq21),
      cases(gr(?x5),
       [gr(0) & gr(?x5),
        gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5),
        gr([0]) <=> gr(0) by lemma(axiom_2_5_single_element_list),
        gr(0) => gr(s(0)),
        assume(~ gr([0]),
         contra(gr(s(0)),
          [gr(s(0)),
           gr([0]),
           ff]),
         ~ gr(s(0))),
        gr(?x5) & gr(s(0)),
        gr(?x5) & gr(s(0)) & gr(0),
        assume(gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5),[],
         gr(?x5) & gr(s(0)) & gr(0))],
       ~ gr(?x5),
       [contra(gr(0) & gr(?x5),[]),
        ~ (gr(0) & gr(?x5)),
        contra(~ gr(0) & ~ gr(?x5),
         [gr(0),
          ~ gr(0),
          ff]),
        ~ (~ gr(0) & ~ gr(?x5)),
        contra(gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5),
         cases(
          [case(~ gr(0) & ~ gr(?x5),
            [~ gr(0) & ~ gr(?x5),
             ~ (~ gr(0) & ~ gr(?x5)),
             ff]),
           case(gr(0) & gr(?x5),
            [gr(0) & gr(?x5),
             ~ (gr(0) & gr(?x5)),
             ff])],
          ff)),
        ~ (gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5)),
        assume(gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5),[],
         gr(?x5) & gr(s(0)) & gr(0))],
       gr(0) & gr(?x5) \/ ~ gr(0) & ~ gr(?x5) => gr(?x5) & gr(s(0)) & gr(0))],
     gr(?x5) & gr(s(0)) & gr(0)),
    step([x6],
     [succeeds !,
      succeeds eq(?x6,s(0))],
     [succeeds eq(?x6,s(0)) => gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6) by
       lemma(eq21),
      cases(gr(?x6),
       [gr([0]) <=> gr(0) by lemma(axiom_2_5_single_element_list),
        gr(0) => gr(s(0)),
        assume(~ gr([0]),
         contra(gr(s(0)),
          [gr(s(0)),
           gr([0]),
           ff]),
         ~ gr(s(0))),
        gr(s(0)) & gr(?x6),
        gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6),
        gr([0]) <=> gr(0) by lemma(axiom_2_5_single_element_list),
        gr(0) => gr(s(0)),
        assume(~ gr([0]),
         contra(gr(s(0)),
          [gr(s(0)),
           gr([0]),
           ff]),
         ~ gr(s(0))),
        gr(s(0)) & gr([]),
        gr([s(0)]) => gr(s(0)) & gr([]),
        assume(~ (gr(s(0)) & gr([])),
         contra(gr([s(0)]),
          [gr(s(0)) & gr([]),
           ff]),
         ~ gr([s(0)])),
        gr([s(0)]) <=> gr(s(0)) & gr([]) by lemma(axiom_2_5),
        gr(s(0)) => gr(s(s(0))),
        assume(~ gr([s(0)]),
         contra(gr(s(s(0))),
          [gr(s(s(0))),
           gr([s(0)]),
           ff]),
         ~ gr(s(s(0)))),
        gr(?x6) & gr(s(s(0))),
        gr(?x6) & gr(s(s(0))) & gr(0),
        assume(gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6),[],
         gr(?x6) & gr(s(s(0))) & gr(0))],
       ~ gr(?x6),
       [contra(gr(s(0)) & gr(?x6),[]),
        ~ (gr(s(0)) & gr(?x6)),
        gr([0]) <=> gr(0) by lemma(axiom_2_5_single_element_list),
        gr(0) => gr(s(0)),
        assume(~ gr([0]),
         contra(gr(s(0)),
          [gr(s(0)),
           gr([0]),
           ff]),
         ~ gr(s(0))),
        contra(~ gr(s(0)) & ~ gr(?x6),
         [gr(s(0)),
          ~ gr(s(0)),
          ff]),
        ~ (~ gr(s(0)) & ~ gr(?x6)),
        contra(gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6),
         cases(
          [case(~ gr(s(0)) & ~ gr(?x6),
            [~ gr(s(0)) & ~ gr(?x6),
             ~ (~ gr(s(0)) & ~ gr(?x6)),
             ff]),
           case(gr(s(0)) & gr(?x6),
            [gr(s(0)) & gr(?x6),
             ~ (gr(s(0)) & gr(?x6)),
             ff])],
          ff)),
        ~ (gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6)),
        assume(gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6),[],
         gr(?x6) & gr(s(s(0))) & gr(0))],
       gr(s(0)) & gr(?x6) \/ ~ gr(s(0)) & ~ gr(?x6) => gr(?x6) & 
        gr(s(s(0))) & gr(0))],
     gr(?x6) & gr(s(s(0))) & gr(0)),
    step([x7,x8,x9,x10],
     [gr(?x9) & gr(s(?x8)) & gr(?x10),
      succeeds p(?x7,?x10),
      succeeds average(?x10,s(?x8),?x9)],
     [succeeds p(?x7,?x10) => gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7) by
       lemma(p21),
      cases(gr(?x7),
       cases(gr(?x8),
        cases(gr(?x9),
         cases(gr(?x10),
          [gr([?x8]) <=> gr(?x8) by lemma(axiom_2_5_single_element_list),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           gr(?x9) & gr(s(?x8)),
           gr(?x9) & gr(s(?x8)) & gr(?x10),
           gr(?x10) & gr(?x7),
           gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
           gr(?x9) & gr(s(?x8)) & gr(?x10) &
           (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           gr(?x9) & gr(?x8),
           gr(?x9) & gr(?x8) & gr(?x7),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x10) & gr(?x7),[gr(?x10),~ gr(?x10),ff]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x10) & ~ gr(?x7),[]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         ~ gr(?x9),
         cases(gr(?x10),
          [contra(gr(?x9) & gr(s(?x8)),[gr(?x9),~ gr(?x9),ff]),
           ~ (gr(?x9) & gr(s(?x8))),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10),
            [gr(?x9) & gr(s(?x8)),
             ~ (gr(?x9) & gr(s(?x8))),
             ff]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x10) & gr(?x7),[gr(?x10),~ gr(?x10),ff]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x10) & ~ gr(?x7),[]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         gr(?x9) & gr(s(?x8)) & gr(?x10) &
         (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & 
          gr(?x8) & gr(?x7)),
        ~ gr(?x8),
        cases(gr(?x9),
         cases(gr(?x10),
          [~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           contra(gr(?x9) & gr(s(?x8)),
            [gr(s(?x8)),
             ~ gr(s(?x8)),
             ff]),
           ~ (gr(?x9) & gr(s(?x8))),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10),
            [gr(?x9) & gr(s(?x8)),
             ~ (gr(?x9) & gr(s(?x8))),
             ff]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x10) & gr(?x7),[gr(?x10),~ gr(?x10),ff]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x10) & ~ gr(?x7),[]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         ~ gr(?x9),
         cases(gr(?x10),
          [~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           contra(gr(?x9) & gr(s(?x8)),
            [gr(s(?x8)),
             ~ gr(s(?x8)),
             ff]),
           ~ (gr(?x9) & gr(s(?x8))),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10),
            [gr(?x9) & gr(s(?x8)),
             ~ (gr(?x9) & gr(s(?x8))),
             ff]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x10) & gr(?x7),[gr(?x10),~ gr(?x10),ff]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x10) & ~ gr(?x7),[]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         gr(?x9) & gr(s(?x8)) & gr(?x10) &
         (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & 
          gr(?x8) & gr(?x7)),
        gr(?x9) & gr(s(?x8)) & gr(?x10) &
        (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & gr(?x8) &
         gr(?x7)),
       ~ gr(?x7),
       cases(gr(?x8),
        cases(gr(?x9),
         cases(gr(?x10),
          [contra(gr(?x10) & gr(?x7),[]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x10),[]),
           ~ ~ gr(?x10),
           contra(~ gr(?x10) & ~ gr(?x7),
            [gr(?x10),
             ~ gr(?x10),
             ff]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x9) & gr(s(?x8)) & gr(?x10),[]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         ~ gr(?x9),
         cases(gr(?x10),
          [contra(gr(?x10) & gr(?x7),[]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x10),[]),
           ~ ~ gr(?x10),
           contra(~ gr(?x10) & ~ gr(?x7),
            [gr(?x10),
             ~ gr(?x10),
             ff]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x9) & gr(s(?x8)) & gr(?x10),[]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         gr(?x9) & gr(s(?x8)) & gr(?x10) &
         (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & 
          gr(?x8) & gr(?x7)),
        ~ gr(?x8),
        cases(gr(?x9),
         cases(gr(?x10),
          [contra(gr(?x10) & gr(?x7),[]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x10),[]),
           ~ ~ gr(?x10),
           contra(~ gr(?x10) & ~ gr(?x7),
            [gr(?x10),
             ~ gr(?x10),
             ff]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x9) & gr(s(?x8)) & gr(?x10),[]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         ~ gr(?x9),
         cases(gr(?x10),
          [contra(gr(?x10) & gr(?x7),[]),
           ~ (gr(?x10) & gr(?x7)),
           contra(~ gr(?x10),[]),
           ~ ~ gr(?x10),
           contra(~ gr(?x10) & ~ gr(?x7),
            [gr(?x10),
             ~ gr(?x10),
             ff]),
           ~ (~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7),
            cases(
             [case(~ gr(?x10) & ~ gr(?x7),
               [~ gr(?x10) & ~ gr(?x7),
                ~ (~ gr(?x10) & ~ gr(?x7)),
                ff]),
              case(gr(?x10) & gr(?x7),
               [gr(?x10) & gr(?x7),
                ~ (gr(?x10) & gr(?x7)),
                ff])],
             ff)),
           ~ (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          ~ gr(?x10),
          [contra(gr(?x9) & gr(s(?x8)) & gr(?x10),[]),
           ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
           contra(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),
            [gr(?x9) & gr(s(?x8)) & gr(?x10),
             ~ (gr(?x9) & gr(s(?x8)) & gr(?x10)),
             ff]),
           ~ 
           (gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7))),
           assume(gr(?x9) & gr(s(?x8)) & gr(?x10) &
            (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)),[],
            gr(?x9) & gr(?x8) & gr(?x7))],
          gr(?x9) & gr(s(?x8)) & gr(?x10) &
          (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) &
           gr(?x8) & gr(?x7)),
         gr(?x9) & gr(s(?x8)) & gr(?x10) &
         (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & 
          gr(?x8) & gr(?x7)),
        gr(?x9) & gr(s(?x8)) & gr(?x10) &
        (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & gr(?x8) &
         gr(?x7)),
       gr(?x9) & gr(s(?x8)) & gr(?x10) &
       (gr(?x10) & gr(?x7) \/ ~ gr(?x10) & ~ gr(?x7)) => gr(?x9) & gr(?x8) &
        gr(?x7))],
     gr(?x9) & gr(?x8) & gr(?x7)),
    step([x11,x12,x13,x14,x15,x16,x17],
     [gr(?x17) & gr(?x16) & gr(s(?x11)),
      succeeds p(?x12,?x14),
      succeeds p(?x14,?x15),
      succeeds p(?x15,?x16),
      succeeds average(s(?x11),?x16,?x17),
      succeeds p(?x13,?x17)],
     [succeeds p(?x12,?x14) => gr(?x14) & gr(?x12) \/
       ~ gr(?x14) & ~ gr(?x12) by lemma(p21),
      succeeds p(?x14,?x15) => gr(?x15) & gr(?x14) \/
       ~ gr(?x15) & ~ gr(?x14) by lemma(p21),
      succeeds p(?x15,?x16) => gr(?x16) & gr(?x15) \/
       ~ gr(?x16) & ~ gr(?x15) by lemma(p21),
      succeeds p(?x13,?x17) => gr(?x17) & gr(?x13) \/
       ~ gr(?x17) & ~ gr(?x13) by lemma(p21),
      cases(gr(?x11),
       cases(gr(?x12),
        cases(gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [gr(?x17) & gr(?x16),
              gr([?x11]) <=> gr(?x11) by 
               lemma(axiom_2_5_single_element_list),
              gr(?x11) => gr(s(?x11)),
              assume(~ gr([?x11]),
               contra(gr(s(?x11)),
                [gr(s(?x11)),
                 gr([?x11]),
                 ff]),
               ~ gr(s(?x11))),
              gr(?x17) & gr(?x16) & gr(s(?x11)),
              gr(?x14) & gr(?x12),
              gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
              gr(?x15) & gr(?x14),
              gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
              gr(?x16) & gr(?x15),
              gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
              gr(?x17) & gr(?x13),
              gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
              (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              gr(?x17) & gr(?x16) & gr(s(?x11)) &
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              gr(?x13) & gr(?x12),
              gr(?x13) & gr(?x12) & gr(?x11),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x14) & gr(?x12),[gr(?x14),~ gr(?x14),ff]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x12),[]),
              ~ ~ gr(?x12),
              contra(~ gr(?x14) & ~ gr(?x12),[]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         ~ gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x16),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x16)),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(?x17) & gr(?x16),
                ~ (gr(?x17) & gr(?x16)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x14) & gr(?x12),[gr(?x14),~ gr(?x14),ff]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x12),[]),
              ~ ~ gr(?x12),
              contra(~ gr(?x14) & ~ gr(?x12),[]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         gr(?x17) & gr(?x16) & gr(s(?x11)) &
         ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
          ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
           ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
            (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
          gr(?x12) & gr(?x11)),
        ~ gr(?x12),
        cases(gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x14) & gr(?x12),[]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x14) & ~ gr(?x12),
               [gr(?x14),
                ~ gr(?x14),
                ff]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x16),[]),
              ~ (gr(?x17) & gr(?x16)),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(?x17) & gr(?x16),
                ~ (gr(?x17) & gr(?x16)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         ~ gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x14) & gr(?x12),[]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x14) & ~ gr(?x12),
               [gr(?x14),
                ~ gr(?x14),
                ff]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x16),[]),
              ~ (gr(?x17) & gr(?x16)),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(?x17) & gr(?x16),
                ~ (gr(?x17) & gr(?x16)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         gr(?x17) & gr(?x16) & gr(s(?x11)) &
         ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
          ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
           ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
            (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
          gr(?x12) & gr(?x11)),
        gr(?x17) & gr(?x16) & gr(s(?x11)) &
        ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
         ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
          ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
           (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
         gr(?x12) & gr(?x11)),
       ~ gr(?x11),
       cases(gr(?x12),
        cases(gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [~ gr([?x11]) <=> ~ gr(?x11) by 
               lemma(axiom_2_5_single_element_list_de_morgan),
              gr(?x11) => gr(s(?x11)),
              assume(~ gr([?x11]),
               contra(gr(s(?x11)),
                [gr(s(?x11)),
                 gr([?x11]),
                 ff]),
               ~ gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(s(?x11)),
                ~ gr(s(?x11)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x14) & gr(?x12),[gr(?x14),~ gr(?x14),ff]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x12),[]),
              ~ ~ gr(?x12),
              contra(~ gr(?x14) & ~ gr(?x12),[]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         ~ gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [~ gr([?x11]) <=> ~ gr(?x11) by 
               lemma(axiom_2_5_single_element_list_de_morgan),
              gr(?x11) => gr(s(?x11)),
              assume(~ gr([?x11]),
               contra(gr(s(?x11)),
                [gr(s(?x11)),
                 gr([?x11]),
                 ff]),
               ~ gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(s(?x11)),
                ~ gr(s(?x11)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x14) & gr(?x12),[gr(?x14),~ gr(?x14),ff]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x12),[]),
              ~ ~ gr(?x12),
              contra(~ gr(?x14) & ~ gr(?x12),[]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         gr(?x17) & gr(?x16) & gr(s(?x11)) &
         ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
          ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
           ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
            (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
          gr(?x12) & gr(?x11)),
        ~ gr(?x12),
        cases(gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x14) & gr(?x12),[]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x14) & ~ gr(?x12),
               [gr(?x14),
                ~ gr(?x14),
                ff]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [~ gr([?x11]) <=> ~ gr(?x11) by 
               lemma(axiom_2_5_single_element_list_de_morgan),
              gr(?x11) => gr(s(?x11)),
              assume(~ gr([?x11]),
               contra(gr(s(?x11)),
                [gr(s(?x11)),
                 gr([?x11]),
                 ff]),
               ~ gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(s(?x11)),
                ~ gr(s(?x11)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x17) & gr(?x13),[gr(?x17),~ gr(?x17),ff]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x13),[]),
              ~ ~ gr(?x13),
              contra(~ gr(?x17) & ~ gr(?x13),[]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         ~ gr(?x13),
         cases(gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x14) & gr(?x12),[]),
              ~ (gr(?x14) & gr(?x12)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x14) & ~ gr(?x12),
               [gr(?x14),
                ~ gr(?x14),
                ff]),
              ~ (~ gr(?x14) & ~ gr(?x12)),
              contra(gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
               cases(
                [case(~ gr(?x14) & ~ gr(?x12),
                  [~ gr(?x14) & ~ gr(?x12),
                   ~ (~ gr(?x14) & ~ gr(?x12)),
                   ff]),
                 case(gr(?x14) & gr(?x12),
                  [gr(?x14) & gr(?x12),
                   ~ (gr(?x14) & gr(?x12)),
                   ff])],
                ff)),
              ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
               [gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12),
                ~ (gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)),
                ff]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[gr(?x15),~ gr(?x15),ff]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x14),[]),
              ~ ~ gr(?x14),
              contra(~ gr(?x15) & ~ gr(?x14),[]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          ~ gr(?x14),
          cases(gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x15) & gr(?x14),[]),
              ~ (gr(?x15) & gr(?x14)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x15) & ~ gr(?x14),
               [gr(?x15),
                ~ gr(?x15),
                ff]),
              ~ (~ gr(?x15) & ~ gr(?x14)),
              contra(gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
               cases(
                [case(~ gr(?x15) & ~ gr(?x14),
                  [~ gr(?x15) & ~ gr(?x14),
                   ~ (~ gr(?x15) & ~ gr(?x14)),
                   ff]),
                 case(gr(?x15) & gr(?x14),
                  [gr(?x15) & gr(?x14),
                   ~ (gr(?x15) & gr(?x14)),
                   ff])],
                ff)),
              ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
               [gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14),
                ~ (gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)),
                ff]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[gr(?x16),~ gr(?x16),ff]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x15),[]),
              ~ ~ gr(?x15),
              contra(~ gr(?x16) & ~ gr(?x15),[]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           ~ gr(?x15),
           cases(gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [contra(gr(?x16) & gr(?x15),[]),
              ~ (gr(?x16) & gr(?x15)),
              contra(~ gr(?x16),[]),
              ~ ~ gr(?x16),
              contra(~ gr(?x16) & ~ gr(?x15),
               [gr(?x16),
                ~ gr(?x16),
                ff]),
              ~ (~ gr(?x16) & ~ gr(?x15)),
              contra(gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
               cases(
                [case(~ gr(?x16) & ~ gr(?x15),
                  [~ gr(?x16) & ~ gr(?x15),
                   ~ (~ gr(?x16) & ~ gr(?x15)),
                   ff]),
                 case(gr(?x16) & gr(?x15),
                  [gr(?x16) & gr(?x15),
                   ~ (gr(?x16) & gr(?x15)),
                   ff])],
                ff)),
              ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
               [gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15),
                ~ (gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)),
                ff]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            ~ gr(?x16),
            cases(gr(?x17),
             [contra(gr(?x17) & gr(?x13),[]),
              ~ (gr(?x17) & gr(?x13)),
              contra(~ gr(?x17),[]),
              ~ ~ gr(?x17),
              contra(~ gr(?x17) & ~ gr(?x13),
               [gr(?x17),
                ~ gr(?x17),
                ff]),
              ~ (~ gr(?x17) & ~ gr(?x13)),
              contra(gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13),
               cases(
                [case(~ gr(?x17) & ~ gr(?x13),
                  [~ gr(?x17) & ~ gr(?x13),
                   ~ (~ gr(?x17) & ~ gr(?x13)),
                   ff]),
                 case(gr(?x17) & gr(?x13),
                  [gr(?x17) & gr(?x13),
                   ~ (gr(?x17) & gr(?x13)),
                   ff])],
                ff)),
              ~ (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),
              contra((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)),[]),
              ~ 
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),
              contra((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))),[]),
              ~ 
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),
              contra((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))),[]),
              ~ 
              ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
               ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                 (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             ~ gr(?x17),
             [~ gr([?x11]) <=> ~ gr(?x11) by 
               lemma(axiom_2_5_single_element_list_de_morgan),
              gr(?x11) => gr(s(?x11)),
              assume(~ gr([?x11]),
               contra(gr(s(?x11)),
                [gr(s(?x11)),
                 gr([?x11]),
                 ff]),
               ~ gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)),
               [gr(s(?x11)),
                ~ gr(s(?x11)),
                ff]),
              ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
              contra(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),
               [gr(?x17) & gr(?x16) & gr(s(?x11)),
                ~ (gr(?x17) & gr(?x16) & gr(s(?x11))),
                ff]),
              ~ 
              (gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13)))))),
              assume(gr(?x17) & gr(?x16) & gr(s(?x11)) &
               ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
                ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
                 ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                  (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))),[],
               gr(?x13) & gr(?x12) & gr(?x11))],
             gr(?x17) & gr(?x16) & gr(s(?x11)) &
             ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
              ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
               ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
                (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
              gr(?x13) & gr(?x12) & gr(?x11)),
            gr(?x17) & gr(?x16) & gr(s(?x11)) &
            ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
             ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
              ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
               (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
             gr(?x13) & gr(?x12) & gr(?x11)),
           gr(?x17) & gr(?x16) & gr(s(?x11)) &
           ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
            ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
             ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
              (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
            gr(?x13) & gr(?x12) & gr(?x11)),
          gr(?x17) & gr(?x16) & gr(s(?x11)) &
          ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
           ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
            ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
             (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => 
           gr(?x13) & gr(?x12) & gr(?x11)),
         gr(?x17) & gr(?x16) & gr(s(?x11)) &
         ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
          ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
           ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
            (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
          gr(?x12) & gr(?x11)),
        gr(?x17) & gr(?x16) & gr(s(?x11)) &
        ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
         ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
          ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
           (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
         gr(?x12) & gr(?x11)),
       gr(?x17) & gr(?x16) & gr(s(?x11)) &
       ((gr(?x14) & gr(?x12) \/ ~ gr(?x14) & ~ gr(?x12)) &
        ((gr(?x15) & gr(?x14) \/ ~ gr(?x15) & ~ gr(?x14)) &
         ((gr(?x16) & gr(?x15) \/ ~ gr(?x16) & ~ gr(?x15)) &
          (gr(?x17) & gr(?x13) \/ ~ gr(?x17) & ~ gr(?x13))))) => gr(?x13) &
        gr(?x12) & gr(?x11))],
     gr(?x13) & gr(?x12) & gr(?x11))]))].