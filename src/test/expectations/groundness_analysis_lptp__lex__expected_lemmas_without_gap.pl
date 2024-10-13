[lemma(inf221,
  all [x1,x2]: 
   (succeeds inf2(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds inf2(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1))],
   [step([x3],[],
     [cases(gr(?x3),
       [gr([?x3]) <=> gr(?x3) by lemma(axiom_2_5_single_element_list),
        gr(?x3) => gr(s(?x3)),
        assume(~ gr([?x3]),
         contra(gr(s(?x3)),
          [gr(s(?x3)),
           gr([?x3]),
           ff]),
         ~ gr(s(?x3))),
        gr(s(?x3)) & gr(0),
        gr(s(?x3)) & gr(0) \/ ~ gr(s(?x3)) & gr(0)],
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
        ~ gr(s(?x3)) & gr(0),
        gr(s(?x3)) & gr(0) \/ ~ gr(s(?x3)) & gr(0)],
       gr(s(?x3)) & gr(0) \/ ~ gr(s(?x3)) & gr(0))],
     gr(s(?x3)) & gr(0) \/ ~ gr(s(?x3)) & gr(0)),
    step([x4,x5],
     [gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
      succeeds inf2(?x4,?x5)],
     [cases(gr(?x4),
       cases(gr(?x5),
        [gr(?x5) & gr(?x4),
         gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
         gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
         gr(?x5) => gr(s(?x5)),
         assume(~ gr([?x5]),
          contra(gr(s(?x5)),
           [gr(s(?x5)),
            gr([?x5]),
            ff]),
          ~ gr(s(?x5))),
         gr([?x4]) <=> gr(?x4) by lemma(axiom_2_5_single_element_list),
         gr(?x4) => gr(s(?x4)),
         assume(~ gr([?x4]),
          contra(gr(s(?x4)),
           [gr(s(?x4)),
            gr([?x4]),
            ff]),
          ~ gr(s(?x4))),
         gr(s(?x5)) & gr(s(?x4)),
         gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)),
         assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),[],
          gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))],
        ~ gr(?x5),
        [~ gr(?x5) & gr(?x4),
         gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
         ~ gr([?x5]) <=> ~ gr(?x5) by 
          lemma(axiom_2_5_single_element_list_de_morgan),
         gr(?x5) => gr(s(?x5)),
         assume(~ gr([?x5]),
          contra(gr(s(?x5)),
           [gr(s(?x5)),
            gr([?x5]),
            ff]),
          ~ gr(s(?x5))),
         gr([?x4]) <=> gr(?x4) by lemma(axiom_2_5_single_element_list),
         gr(?x4) => gr(s(?x4)),
         assume(~ gr([?x4]),
          contra(gr(s(?x4)),
           [gr(s(?x4)),
            gr([?x4]),
            ff]),
          ~ gr(s(?x4))),
         ~ gr(s(?x5)) & gr(s(?x4)),
         gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)),
         assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),[],
          gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))],
        gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4) => gr(s(?x5)) & gr(s(?x4)) \/
         ~ gr(s(?x5)) & gr(s(?x4))),
       ~ gr(?x4),
       cases(gr(?x5),
        [contra(gr(?x5) & gr(?x4),[]),
         ~ (gr(?x5) & gr(?x4)),
         contra(~ gr(?x5) & gr(?x4),[]),
         ~ (~ gr(?x5) & gr(?x4)),
         contra(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
          cases(
           [case(~ gr(?x5) & gr(?x4),
             [~ gr(?x5) & gr(?x4),
              ~ (~ gr(?x5) & gr(?x4)),
              ff]),
            case(gr(?x5) & gr(?x4),
             [gr(?x5) & gr(?x4),
              ~ (gr(?x5) & gr(?x4)),
              ff])],
           ff)),
         ~ (gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4)),
         assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),[],
          gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))],
        ~ gr(?x5),
        [contra(gr(?x5) & gr(?x4),[]),
         ~ (gr(?x5) & gr(?x4)),
         contra(~ gr(?x5) & gr(?x4),[]),
         ~ (~ gr(?x5) & gr(?x4)),
         contra(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
          cases(
           [case(~ gr(?x5) & gr(?x4),
             [~ gr(?x5) & gr(?x4),
              ~ (~ gr(?x5) & gr(?x4)),
              ff]),
            case(gr(?x5) & gr(?x4),
             [gr(?x5) & gr(?x4),
              ~ (gr(?x5) & gr(?x4)),
              ff])],
           ff)),
         ~ (gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4)),
         assume(gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),[],
          gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))],
        gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4) => gr(s(?x5)) & gr(s(?x4)) \/
         ~ gr(s(?x5)) & gr(s(?x4))),
       gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4) => gr(s(?x5)) & gr(s(?x4)) \/
        ~ gr(s(?x5)) & gr(s(?x4)))],
     gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))])),
 lemma(p21,
  all [x1,x2]: (fails p(?x1,?x2)),
  ff by gap),
 lemma(inf421,
  all [x1,x2]: 
   (succeeds inf4(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1) \/
     gr(?x2) & ~ gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds inf4(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1) \/
       gr(?x2) & ~ gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([x3,x4],
     [succeeds inf2(?x3,?x4)],
     [succeeds inf2(?x3,?x4) => gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3) by
       lemma(inf221),
      cases(gr(?x3),
       cases(gr(?x4),
        [gr(?x4) & gr(?x3),
         gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),
         gr([?x4]) <=> gr(?x4) by lemma(axiom_2_5_single_element_list),
         gr(0) & gr([?x4]),
         gr([0,?x4]) => gr(0) & gr([?x4]),
         assume(~ (gr(0) & gr([?x4])),
          contra(gr([0,?x4]),
           [gr(0) & gr([?x4]),
            ff]),
          ~ gr([0,?x4])),
         gr([0,?x4]) <=> gr(0) & gr([?x4]) by lemma(axiom_2_5),
         gr(0) & gr(?x4) => gr(f(0,?x4)),
         assume(~ gr([0,?x4]),
          contra(gr(f(0,?x4)),
           [gr(f(0,?x4)),
            gr([0,?x4]),
            ff]),
          ~ gr(f(0,?x4))),
         gr([?x3]) <=> gr(?x3) by lemma(axiom_2_5_single_element_list),
         gr(0) & gr([?x3]),
         gr([0,?x3]) => gr(0) & gr([?x3]),
         assume(~ (gr(0) & gr([?x3])),
          contra(gr([0,?x3]),
           [gr(0) & gr([?x3]),
            ff]),
          ~ gr([0,?x3])),
         gr([0,?x3]) <=> gr(0) & gr([?x3]) by lemma(axiom_2_5),
         gr(0) & gr(?x3) => gr(f(0,?x3)),
         assume(~ gr([0,?x3]),
          contra(gr(f(0,?x3)),
           [gr(f(0,?x3)),
            gr([0,?x3]),
            ff]),
          ~ gr(f(0,?x3))),
         gr(f(0,?x4)) & gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)),
         assume(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),[],
          gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
          gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)))],
        ~ gr(?x4),
        [~ gr(?x4) & gr(?x3),
         gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),
         ~ gr([?x4]) <=> ~ gr(?x4) by 
          lemma(axiom_2_5_single_element_list_de_morgan),
         ~ gr(0) \/ ~ gr([?x4]),
         ~ gr([0,?x4]) <=> ~ gr(0) \/ ~ gr([?x4]) by 
          lemma(axiom_2_5_de_morgan),
         gr(0) & gr(?x4) => gr(f(0,?x4)),
         assume(~ gr([0,?x4]),
          contra(gr(f(0,?x4)),
           [gr(f(0,?x4)),
            gr([0,?x4]),
            ff]),
          ~ gr(f(0,?x4))),
         gr([?x3]) <=> gr(?x3) by lemma(axiom_2_5_single_element_list),
         gr(0) & gr([?x3]),
         gr([0,?x3]) => gr(0) & gr([?x3]),
         assume(~ (gr(0) & gr([?x3])),
          contra(gr([0,?x3]),
           [gr(0) & gr([?x3]),
            ff]),
          ~ gr([0,?x3])),
         gr([0,?x3]) <=> gr(0) & gr([?x3]) by lemma(axiom_2_5),
         gr(0) & gr(?x3) => gr(f(0,?x3)),
         assume(~ gr([0,?x3]),
          contra(gr(f(0,?x3)),
           [gr(f(0,?x3)),
            gr([0,?x3]),
            ff]),
          ~ gr(f(0,?x3))),
         ~ gr(f(0,?x4)) & gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)),
         gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)),
         assume(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),[],
          gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
          gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)))],
        gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3) => gr(f(0,?x4)) &
         gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3))),
       ~ gr(?x3),
       cases(gr(?x4),
        [contra(gr(?x4) & gr(?x3),[]),
         ~ (gr(?x4) & gr(?x3)),
         contra(~ gr(?x4) & gr(?x3),[]),
         ~ (~ gr(?x4) & gr(?x3)),
         contra(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),
          cases(
           [case(~ gr(?x4) & gr(?x3),
             [~ gr(?x4) & gr(?x3),
              ~ (~ gr(?x4) & gr(?x3)),
              ff]),
            case(gr(?x4) & gr(?x3),
             [gr(?x4) & gr(?x3),
              ~ (gr(?x4) & gr(?x3)),
              ff])],
           ff)),
         ~ (gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3)),
         assume(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),[],
          gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
          gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)))],
        ~ gr(?x4),
        [contra(gr(?x4) & gr(?x3),[]),
         ~ (gr(?x4) & gr(?x3)),
         contra(~ gr(?x4) & gr(?x3),[]),
         ~ (~ gr(?x4) & gr(?x3)),
         contra(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),
          cases(
           [case(~ gr(?x4) & gr(?x3),
             [~ gr(?x4) & gr(?x3),
              ~ (~ gr(?x4) & gr(?x3)),
              ff]),
            case(gr(?x4) & gr(?x3),
             [gr(?x4) & gr(?x3),
              ~ (gr(?x4) & gr(?x3)),
              ff])],
           ff)),
         ~ (gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3)),
         assume(gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3),[],
          gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
          gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)))],
        gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3) => gr(f(0,?x4)) &
         gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
         gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3))),
       gr(?x4) & gr(?x3) \/ ~ gr(?x4) & gr(?x3) => gr(f(0,?x4)) &
        gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
        gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3)))],
     gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
     gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3))),
    step([x5,x6,x7],[],
     [cases(gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         [gr([?x6]) <=> gr(?x6) by lemma(axiom_2_5_single_element_list),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          gr([?x7]) <=> gr(?x7) by lemma(axiom_2_5_single_element_list),
          gr(s(?x6)) & gr([?x7]),
          gr([s(?x6),?x7]) => gr(s(?x6)) & gr([?x7]),
          assume(~ (gr(s(?x6)) & gr([?x7])),
           contra(gr([s(?x6),?x7]),
            [gr(s(?x6)) & gr([?x7]),
             ff]),
           ~ gr([s(?x6),?x7])),
          gr([s(?x6),?x7]) <=> gr(s(?x6)) & gr([?x7]) by lemma(axiom_2_5),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(0) & gr([?x5]),
          gr([0,?x5]) => gr(0) & gr([?x5]),
          assume(~ (gr(0) & gr([?x5])),
           contra(gr([0,?x5]),
            [gr(0) & gr([?x5]),
             ff]),
           ~ gr([0,?x5])),
          gr([0,?x5]) <=> gr(0) & gr([?x5]) by lemma(axiom_2_5),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         ~ gr(?x7),
         [~ gr([?x7]) <=> ~ gr(?x7) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(0) & gr([?x5]),
          gr([0,?x5]) => gr(0) & gr([?x5]),
          assume(~ (gr(0) & gr([?x5])),
           contra(gr([0,?x5]),
            [gr(0) & gr([?x5]),
             ff]),
           ~ gr([0,?x5])),
          gr([0,?x5]) <=> gr(0) & gr([?x5]) by lemma(axiom_2_5),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         [~ gr([?x6]) <=> ~ gr(?x6) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(0) & gr([?x5]),
          gr([0,?x5]) => gr(0) & gr([?x5]),
          assume(~ (gr(0) & gr([?x5])),
           contra(gr([0,?x5]),
            [gr(0) & gr([?x5]),
             ff]),
           ~ gr([0,?x5])),
          gr([0,?x5]) <=> gr(0) & gr([?x5]) by lemma(axiom_2_5),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         ~ gr(?x7),
         [~ gr([?x6]) <=> ~ gr(?x6) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(0) & gr([?x5]),
          gr([0,?x5]) => gr(0) & gr([?x5]),
          assume(~ (gr(0) & gr([?x5])),
           contra(gr([0,?x5]),
            [gr(0) & gr([?x5]),
             ff]),
           ~ gr([0,?x5])),
          gr([0,?x5]) <=> gr(0) & gr([?x5]) by lemma(axiom_2_5),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
        gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
        ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
        gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
        ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
       ~ gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         [gr([?x6]) <=> gr(?x6) by lemma(axiom_2_5_single_element_list),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          gr([?x7]) <=> gr(?x7) by lemma(axiom_2_5_single_element_list),
          gr(s(?x6)) & gr([?x7]),
          gr([s(?x6),?x7]) => gr(s(?x6)) & gr([?x7]),
          assume(~ (gr(s(?x6)) & gr([?x7])),
           contra(gr([s(?x6),?x7]),
            [gr(s(?x6)) & gr([?x7]),
             ff]),
           ~ gr([s(?x6),?x7])),
          gr([s(?x6),?x7]) <=> gr(s(?x6)) & gr([?x7]) by lemma(axiom_2_5),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          ~ gr([?x5]) <=> ~ gr(?x5) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(0) \/ ~ gr([?x5]),
          ~ gr([0,?x5]) <=> ~ gr(0) \/ ~ gr([?x5]) by 
           lemma(axiom_2_5_de_morgan),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         ~ gr(?x7),
         [~ gr([?x7]) <=> ~ gr(?x7) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          ~ gr([?x5]) <=> ~ gr(?x5) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(0) \/ ~ gr([?x5]),
          ~ gr([0,?x5]) <=> ~ gr(0) \/ ~ gr([?x5]) by 
           lemma(axiom_2_5_de_morgan),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         [~ gr([?x6]) <=> ~ gr(?x6) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          ~ gr([?x5]) <=> ~ gr(?x5) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(0) \/ ~ gr([?x5]),
          ~ gr([0,?x5]) <=> ~ gr(0) \/ ~ gr([?x5]) by 
           lemma(axiom_2_5_de_morgan),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         ~ gr(?x7),
         [~ gr([?x6]) <=> ~ gr(?x6) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          gr(?x6) => gr(s(?x6)),
          assume(~ gr([?x6]),
           contra(gr(s(?x6)),
            [gr(s(?x6)),
             gr([?x6]),
             ff]),
           ~ gr(s(?x6))),
          ~ gr(s(?x6)) \/ ~ gr([?x7]),
          ~ gr([s(?x6),?x7]) <=> ~ gr(s(?x6)) \/ ~ gr([?x7]) by 
           lemma(axiom_2_5_de_morgan),
          gr(s(?x6)) & gr(?x7) => gr(f(s(?x6),?x7)),
          assume(~ gr([s(?x6),?x7]),
           contra(gr(f(s(?x6),?x7)),
            [gr(f(s(?x6),?x7)),
             gr([s(?x6),?x7]),
             ff]),
           ~ gr(f(s(?x6),?x7))),
          ~ gr([?x5]) <=> ~ gr(?x5) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          ~ gr(0) \/ ~ gr([?x5]),
          ~ gr([0,?x5]) <=> ~ gr(0) \/ ~ gr([?x5]) by 
           lemma(axiom_2_5_de_morgan),
          gr(0) & gr(?x5) => gr(f(0,?x5)),
          assume(~ gr([0,?x5]),
           contra(gr(f(0,?x5)),
            [gr(f(0,?x5)),
             gr([0,?x5]),
             ff]),
           ~ gr(f(0,?x5))),
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)),
          gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
          gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
          ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))],
         gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
         gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
         ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
        gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
        ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
        gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
        ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
       gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
       ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
       gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
       ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)))],
     gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/ ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
     gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
     ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
    step([x8,x9,x10,x11],
     [gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
      ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
      gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
      ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
      succeeds inf4(f(?x8,?x9),f(?x10,?x11))],
     [cases(gr(?x8),
       cases(gr(?x9),
        cases(gr(?x10),
         cases(gr(?x11),
          [gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(?x10) & gr([?x11]),
           gr([?x10,?x11]) => gr(?x10) & gr([?x11]),
           assume(~ (gr(?x10) & gr([?x11])),
            contra(gr([?x10,?x11]),
             [gr(?x10) & gr([?x11]),
              ff]),
            ~ gr([?x10,?x11])),
           gr([?x10,?x11]) <=> gr(?x10) & gr([?x11]) by lemma(axiom_2_5),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(?x8) & gr([?x9]),
           gr([?x8,?x9]) => gr(?x8) & gr([?x9]),
           assume(~ (gr(?x8) & gr([?x9])),
            contra(gr([?x8,?x9]),
             [gr(?x8) & gr([?x9]),
              ff]),
            ~ gr([?x8,?x9])),
           gr([?x8,?x9]) <=> gr(?x8) & gr([?x9]) by lemma(axiom_2_5),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr([?x10]) <=> gr(?x10) by lemma(axiom_2_5_single_element_list),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(s(?x10)) & gr([?x11]),
           gr([s(?x10),?x11]) => gr(s(?x10)) & gr([?x11]),
           assume(~ (gr(s(?x10)) & gr([?x11])),
            contra(gr([s(?x10),?x11]),
             [gr(s(?x10)) & gr([?x11]),
              ff]),
            ~ gr([s(?x10),?x11])),
           gr([s(?x10),?x11]) <=> gr(s(?x10)) & gr([?x11]) by 
            lemma(axiom_2_5),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           gr([?x8]) <=> gr(?x8) by lemma(axiom_2_5_single_element_list),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(s(?x8)) & gr([?x9]),
           gr([s(?x8),?x9]) => gr(s(?x8)) & gr([?x9]),
           assume(~ (gr(s(?x8)) & gr([?x9])),
            contra(gr([s(?x8),?x9]),
             [gr(s(?x8)) & gr([?x9]),
              ff]),
            ~ gr([s(?x8),?x9])),
           gr([s(?x8),?x9]) <=> gr(s(?x8)) & gr([?x9]) by lemma(axiom_2_5),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(?x8) & gr([?x9]),
           gr([?x8,?x9]) => gr(?x8) & gr([?x9]),
           assume(~ (gr(?x8) & gr([?x9])),
            contra(gr([?x8,?x9]),
             [gr(?x8) & gr([?x9]),
              ff]),
            ~ gr([?x8,?x9])),
           gr([?x8,?x9]) <=> gr(?x8) & gr([?x9]) by lemma(axiom_2_5),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           gr([?x8]) <=> gr(?x8) by lemma(axiom_2_5_single_element_list),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(s(?x8)) & gr([?x9]),
           gr([s(?x8),?x9]) => gr(s(?x8)) & gr([?x9]),
           assume(~ (gr(s(?x8)) & gr([?x9])),
            contra(gr([s(?x8),?x9]),
             [gr(s(?x8)) & gr([?x9]),
              ff]),
            ~ gr([s(?x8),?x9])),
           gr([s(?x8),?x9]) <=> gr(s(?x8)) & gr([?x9]) by lemma(axiom_2_5),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         ~ gr(?x10),
         cases(gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(?x8) & gr([?x9]),
           gr([?x8,?x9]) => gr(?x8) & gr([?x9]),
           assume(~ (gr(?x8) & gr([?x9])),
            contra(gr([?x8,?x9]),
             [gr(?x8) & gr([?x9]),
              ff]),
            ~ gr([?x8,?x9])),
           gr([?x8,?x9]) <=> gr(?x8) & gr([?x9]) by lemma(axiom_2_5),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           gr([?x8]) <=> gr(?x8) by lemma(axiom_2_5_single_element_list),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(s(?x8)) & gr([?x9]),
           gr([s(?x8),?x9]) => gr(s(?x8)) & gr([?x9]),
           assume(~ (gr(s(?x8)) & gr([?x9])),
            contra(gr([s(?x8),?x9]),
             [gr(s(?x8)) & gr([?x9]),
              ff]),
            ~ gr([s(?x8),?x9])),
           gr([s(?x8),?x9]) <=> gr(s(?x8)) & gr([?x9]) by lemma(axiom_2_5),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(?x8) & gr([?x9]),
           gr([?x8,?x9]) => gr(?x8) & gr([?x9]),
           assume(~ (gr(?x8) & gr([?x9])),
            contra(gr([?x8,?x9]),
             [gr(?x8) & gr([?x9]),
              ff]),
            ~ gr([?x8,?x9])),
           gr([?x8,?x9]) <=> gr(?x8) & gr([?x9]) by lemma(axiom_2_5),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           gr([?x8]) <=> gr(?x8) by lemma(axiom_2_5_single_element_list),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           gr([?x9]) <=> gr(?x9) by lemma(axiom_2_5_single_element_list),
           gr(s(?x8)) & gr([?x9]),
           gr([s(?x8),?x9]) => gr(s(?x8)) & gr([?x9]),
           assume(~ (gr(s(?x8)) & gr([?x9])),
            contra(gr([s(?x8),?x9]),
             [gr(s(?x8)) & gr([?x9]),
              ff]),
            ~ gr([s(?x8),?x9])),
           gr([s(?x8),?x9]) <=> gr(s(?x8)) & gr([?x9]) by lemma(axiom_2_5),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
          gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
          gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
          ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
        ~ gr(?x9),
        cases(gr(?x10),
         cases(gr(?x11),
          [gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(?x10) & gr([?x11]),
           gr([?x10,?x11]) => gr(?x10) & gr([?x11]),
           assume(~ (gr(?x10) & gr([?x11])),
            contra(gr([?x10,?x11]),
             [gr(?x10) & gr([?x11]),
              ff]),
            ~ gr([?x10,?x11])),
           gr([?x10,?x11]) <=> gr(?x10) & gr([?x11]) by lemma(axiom_2_5),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr([?x10]) <=> gr(?x10) by lemma(axiom_2_5_single_element_list),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(s(?x10)) & gr([?x11]),
           gr([s(?x10),?x11]) => gr(s(?x10)) & gr([?x11]),
           assume(~ (gr(s(?x10)) & gr([?x11])),
            contra(gr([s(?x10),?x11]),
             [gr(s(?x10)) & gr([?x11]),
              ff]),
            ~ gr([s(?x10),?x11])),
           gr([s(?x10),?x11]) <=> gr(s(?x10)) & gr([?x11]) by 
            lemma(axiom_2_5),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         ~ gr(?x10),
         cases(gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x9]) <=> ~ gr(?x9) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
          gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
          gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
          ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
        gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
        ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
        gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
        ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
         gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
         gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
         ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
       ~ gr(?x8),
       cases(gr(?x9),
        cases(gr(?x10),
         cases(gr(?x11),
          [gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(?x10) & gr([?x11]),
           gr([?x10,?x11]) => gr(?x10) & gr([?x11]),
           assume(~ (gr(?x10) & gr([?x11])),
            contra(gr([?x10,?x11]),
             [gr(?x10) & gr([?x11]),
              ff]),
            ~ gr([?x10,?x11])),
           gr([?x10,?x11]) <=> gr(?x10) & gr([?x11]) by lemma(axiom_2_5),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr([?x10]) <=> gr(?x10) by lemma(axiom_2_5_single_element_list),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(s(?x10)) & gr([?x11]),
           gr([s(?x10),?x11]) => gr(s(?x10)) & gr([?x11]),
           assume(~ (gr(s(?x10)) & gr([?x11])),
            contra(gr([s(?x10),?x11]),
             [gr(s(?x10)) & gr([?x11]),
              ff]),
            ~ gr([s(?x10),?x11])),
           gr([s(?x10),?x11]) <=> gr(s(?x10)) & gr([?x11]) by 
            lemma(axiom_2_5),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         ~ gr(?x10),
         cases(gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
          gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
          gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
          ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
        ~ gr(?x9),
        cases(gr(?x10),
         cases(gr(?x11),
          [gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(?x10) & gr([?x11]),
           gr([?x10,?x11]) => gr(?x10) & gr([?x11]),
           assume(~ (gr(?x10) & gr([?x11])),
            contra(gr([?x10,?x11]),
             [gr(?x10) & gr([?x11]),
              ff]),
            ~ gr([?x10,?x11])),
           gr([?x10,?x11]) <=> gr(?x10) & gr([?x11]) by lemma(axiom_2_5),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr([?x10]) <=> gr(?x10) by lemma(axiom_2_5_single_element_list),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           gr([?x11]) <=> gr(?x11) by lemma(axiom_2_5_single_element_list),
           gr(s(?x10)) & gr([?x11]),
           gr([s(?x10),?x11]) => gr(s(?x10)) & gr([?x11]),
           assume(~ (gr(s(?x10)) & gr([?x11])),
            contra(gr([s(?x10),?x11]),
             [gr(s(?x10)) & gr([?x11]),
              ff]),
            ~ gr([s(?x10),?x11])),
           gr([s(?x10),?x11]) <=> gr(s(?x10)) & gr([?x11]) by 
            lemma(axiom_2_5),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x11]) <=> ~ gr(?x11) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         ~ gr(?x10),
         cases(gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          ~ gr(?x11),
          [~ gr(?x10) \/ ~ gr([?x11]),
           ~ gr([?x10,?x11]) <=> ~ gr(?x10) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x10) & gr(?x11) => gr(f(?x10,?x11)),
           assume(~ gr([?x10,?x11]),
            contra(gr(f(?x10,?x11)),
             [gr(f(?x10,?x11)),
              gr([?x10,?x11]),
              ff]),
            ~ gr(f(?x10,?x11))),
           ~ gr(?x8) \/ ~ gr([?x9]),
           ~ gr([?x8,?x9]) <=> ~ gr(?x8) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(?x8) & gr(?x9) => gr(f(?x8,?x9)),
           assume(~ gr([?x8,?x9]),
            contra(gr(f(?x8,?x9)),
             [gr(f(?x8,?x9)),
              gr([?x8,?x9]),
              ff]),
            ~ gr(f(?x8,?x9))),
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
           gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
           ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
           ~ gr([?x10]) <=> ~ gr(?x10) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x10) => gr(s(?x10)),
           assume(~ gr([?x10]),
            contra(gr(s(?x10)),
             [gr(s(?x10)),
              gr([?x10]),
              ff]),
            ~ gr(s(?x10))),
           ~ gr(s(?x10)) \/ ~ gr([?x11]),
           ~ gr([s(?x10),?x11]) <=> ~ gr(s(?x10)) \/ ~ gr([?x11]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x10)) & gr(?x11) => gr(f(s(?x10),?x11)),
           assume(~ gr([s(?x10),?x11]),
            contra(gr(f(s(?x10),?x11)),
             [gr(f(s(?x10),?x11)),
              gr([s(?x10),?x11]),
              ff]),
            ~ gr(f(s(?x10),?x11))),
           ~ gr([?x8]) <=> ~ gr(?x8) by 
            lemma(axiom_2_5_single_element_list_de_morgan),
           gr(?x8) => gr(s(?x8)),
           assume(~ gr([?x8]),
            contra(gr(s(?x8)),
             [gr(s(?x8)),
              gr([?x8]),
              ff]),
            ~ gr(s(?x8))),
           ~ gr(s(?x8)) \/ ~ gr([?x9]),
           ~ gr([s(?x8),?x9]) <=> ~ gr(s(?x8)) \/ ~ gr([?x9]) by 
            lemma(axiom_2_5_de_morgan),
           gr(s(?x8)) & gr(?x9) => gr(f(s(?x8),?x9)),
           assume(~ gr([s(?x8),?x9]),
            contra(gr(f(s(?x8),?x9)),
             [gr(f(s(?x8),?x9)),
              gr([s(?x8),?x9]),
              ff]),
            ~ gr(f(s(?x8),?x9))),
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)),
           assume(gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
            gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
            ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),[],
            gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
            gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
            ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
          gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
          gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
          ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
           gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
           gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
           ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
         gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
         gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
         ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
          gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
          gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
          ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
        gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
        ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
        gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
        ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
         gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
         gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
         ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9))),
       gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
       ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
       gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
       ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) => gr(f(s(?x10),?x11)) &
        gr(f(s(?x8),?x9)) \/ ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
        gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
        ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))],
     gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
     ~ gr(f(s(?x10),?x11)) & gr(f(s(?x8),?x9)) \/
     gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)) \/
     ~ gr(f(s(?x10),?x11)) & ~ gr(f(s(?x8),?x9)))])),
 lemma(add31,
  all [x1,x2,x3]: 
   (succeeds add(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds add(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4],[],
     [cases(gr(?x4),
       [gr(?x4) & gr(?x4),
        gr(?x4) & gr(?x4) & gr(0),
        gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)],
       ~ gr(?x4),
       [~ gr(?x4) & ~ gr(?x4),
        ~ gr(?x4) & ~ gr(?x4) & gr(0),
        gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)],
       gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0))],
     gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7],
     [gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
      succeeds add(?x5,?x6,?x7)],
     [cases(gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         [gr(?x7) & gr(?x6),
          gr(?x7) & gr(?x6) & gr(?x5),
          gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
          gr([?x7]) <=> gr(?x7) by lemma(axiom_2_5_single_element_list),
          gr(?x7) => gr(s(?x7)),
          assume(~ gr([?x7]),
           contra(gr(s(?x7)),
            [gr(s(?x7)),
             gr([?x7]),
             ff]),
           ~ gr(s(?x7))),
          gr(s(?x7)) & gr(?x6),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(?x5) => gr(s(?x5)),
          assume(~ gr([?x5]),
           contra(gr(s(?x5)),
            [gr(s(?x5)),
             gr([?x5]),
             ff]),
           ~ gr(s(?x5))),
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)),
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         ~ gr(?x7),
         [contra(gr(?x7) & gr(?x6),[gr(?x7),~ gr(?x7),ff]),
          ~ (gr(?x7) & gr(?x6)),
          contra(gr(?x7) & gr(?x6) & gr(?x5),
           [gr(?x7) & gr(?x6),
            ~ (gr(?x7) & gr(?x6)),
            ff]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x6),[]),
          ~ ~ gr(?x6),
          contra(~ gr(?x7) & ~ gr(?x6),[]),
          ~ (~ gr(?x7) & ~ gr(?x6)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           [~ gr(?x7) & ~ gr(?x6),
            ~ (~ gr(?x7) & ~ gr(?x6)),
            ff]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         [contra(gr(?x7) & gr(?x6),[]),
          ~ (gr(?x7) & gr(?x6)),
          contra(gr(?x7) & gr(?x6) & gr(?x5),
           [gr(?x7) & gr(?x6),
            ~ (gr(?x7) & gr(?x6)),
            ff]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x7),[]),
          ~ ~ gr(?x7),
          contra(~ gr(?x7) & ~ gr(?x6),
           [gr(?x7),
            ~ gr(?x7),
            ff]),
          ~ (~ gr(?x7) & ~ gr(?x6)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           [~ gr(?x7) & ~ gr(?x6),
            ~ (~ gr(?x7) & ~ gr(?x6)),
            ff]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         ~ gr(?x7),
         [~ gr(?x7) & ~ gr(?x6),
          ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
          gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
          ~ gr([?x7]) <=> ~ gr(?x7) by 
           lemma(axiom_2_5_single_element_list_de_morgan),
          gr(?x7) => gr(s(?x7)),
          assume(~ gr([?x7]),
           contra(gr(s(?x7)),
            [gr(s(?x7)),
             gr([?x7]),
             ff]),
           ~ gr(s(?x7))),
          ~ gr(s(?x7)) & ~ gr(?x6),
          gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
          gr(?x5) => gr(s(?x5)),
          assume(~ gr([?x5]),
           contra(gr(s(?x5)),
            [gr(s(?x5)),
             gr([?x5]),
             ff]),
           ~ gr(s(?x5))),
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)),
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
        gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
         gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
         ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
       ~ gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         [contra(gr(?x7) & gr(?x6) & gr(?x5),[]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),[]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         ~ gr(?x7),
         [contra(gr(?x7) & gr(?x6) & gr(?x5),[]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),[]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         [contra(gr(?x7) & gr(?x6) & gr(?x5),[]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),[]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         ~ gr(?x7),
         [contra(gr(?x7) & gr(?x6) & gr(?x5),[]),
          ~ (gr(?x7) & gr(?x6) & gr(?x5)),
          contra(~ gr(?x7) & ~ gr(?x6) & gr(?x5),[]),
          ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          contra(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
           cases(
            [case(~ gr(?x7) & ~ gr(?x6) & gr(?x5),
              [~ gr(?x7) & ~ gr(?x6) & gr(?x5),
               ~ (~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
               ff]),
             case(gr(?x7) & gr(?x6) & gr(?x5),
              [gr(?x7) & gr(?x6) & gr(?x5),
               ~ (gr(?x7) & gr(?x6) & gr(?x5)),
               ff])],
            ff)),
          ~ 
          (gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5)),
          assume(gr(?x7) & gr(?x6) & gr(?x5) \/
           ~ gr(?x7) & ~ gr(?x6) & gr(?x5),[],
           gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
           ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
         gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
          gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
          ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
        gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
         gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
         ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5))),
       gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5) => 
        gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
        ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))],
     gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
     ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))]))].