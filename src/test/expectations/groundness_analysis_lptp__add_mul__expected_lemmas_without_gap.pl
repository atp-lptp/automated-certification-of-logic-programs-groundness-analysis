[lemma(add31,
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
     ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))])),
 lemma(mul31,
  all [x1,x2,x3]: 
   (succeeds mul(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds mul(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4],[],
     [cases(gr(?x4),
       [gr(0) & gr(?x4),
        gr(0) & gr(?x4) & gr(0),
        gr(0) & gr(?x4) & gr(0) \/ gr(0) & ~ gr(?x4) & gr(0)],
       ~ gr(?x4),
       [gr(0) & ~ gr(?x4),
        gr(0) & ~ gr(?x4) & gr(0),
        gr(0) & gr(?x4) & gr(0) \/ gr(0) & ~ gr(?x4) & gr(0)],
       gr(0) & gr(?x4) & gr(0) \/ gr(0) & ~ gr(?x4) & gr(0))],
     gr(0) & gr(?x4) & gr(0) \/ gr(0) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7,x8],
     [gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
      succeeds mul(?x5,?x6,?x8),
      succeeds add(?x6,?x8,?x7)],
     [succeeds add(?x6,?x8,?x7) => gr(?x7) & gr(?x8) & gr(?x6) \/
       ~ gr(?x7) & ~ gr(?x8) & gr(?x6) by lemma(add31),
      cases(gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         cases(gr(?x8),
          [gr(?x8) & gr(?x6),
           gr(?x8) & gr(?x6) & gr(?x5),
           gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
           gr(?x7) & gr(?x8),
           gr(?x7) & gr(?x8) & gr(?x6),
           gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
           (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           gr(?x7) & gr(?x6),
           gr([?x5]) <=> gr(?x5) by lemma(axiom_2_5_single_element_list),
           gr(?x5) => gr(s(?x5)),
           assume(~ gr([?x5]),
            contra(gr(s(?x5)),
             [gr(s(?x5)),
              gr([?x5]),
              ff]),
            ~ gr(s(?x5))),
           gr(?x7) & gr(?x6) & gr(s(?x5)),
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5)),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8),[]),
           ~ (gr(?x7) & gr(?x8)),
           contra(gr(?x7) & gr(?x8) & gr(?x6),
            [gr(?x7) & gr(?x8),
             ~ (gr(?x7) & gr(?x8)),
             ff]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x7) & ~ gr(?x8),
            [gr(?x7),
             ~ gr(?x7),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            [~ gr(?x7) & ~ gr(?x8),
             ~ (~ gr(?x7) & ~ gr(?x8)),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         ~ gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8),[gr(?x7),~ gr(?x7),ff]),
           ~ (gr(?x7) & gr(?x8)),
           contra(gr(?x7) & gr(?x8) & gr(?x6),
            [gr(?x7) & gr(?x8),
             ~ (gr(?x7) & gr(?x8)),
             ff]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x8),[]),
           ~ ~ gr(?x8),
           contra(~ gr(?x7) & ~ gr(?x8),[]),
           ~ (~ gr(?x7) & ~ gr(?x8)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            [~ gr(?x7) & ~ gr(?x8),
             ~ (~ gr(?x7) & ~ gr(?x8)),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x8) & gr(?x6),[gr(?x8),~ gr(?x8),ff]),
           ~ (gr(?x8) & gr(?x6)),
           contra(gr(?x8) & gr(?x6) & gr(?x5),
            [gr(?x8) & gr(?x6),
             ~ (gr(?x8) & gr(?x6)),
             ff]),
           ~ (gr(?x8) & gr(?x6) & gr(?x5)),
           contra(~ gr(?x6),[]),
           ~ ~ gr(?x6),
           contra(gr(?x8) & ~ gr(?x6),[]),
           ~ (gr(?x8) & ~ gr(?x6)),
           contra(gr(?x8) & ~ gr(?x6) & gr(?x5),
            [gr(?x8) & ~ gr(?x6),
             ~ (gr(?x8) & ~ gr(?x6)),
             ff]),
           ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(gr(?x8) & gr(?x6) & gr(?x5) \/
            gr(?x8) & ~ gr(?x6) & gr(?x5),
            cases(
             [case(gr(?x8) & ~ gr(?x6) & gr(?x5),
               [gr(?x8) & ~ gr(?x6) & gr(?x5),
                ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
                ff]),
              case(gr(?x8) & gr(?x6) & gr(?x5),
               [gr(?x8) & gr(?x6) & gr(?x5),
                ~ (gr(?x8) & gr(?x6) & gr(?x5)),
                ff])],
             ff)),
           ~ (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
            [gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
             ~ 
             (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
             ff]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
         (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
          gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & 
          gr(s(?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         ~ gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
         (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
          gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & 
          gr(s(?x5))),
        (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
        (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
         gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
       ~ gr(?x5),
       cases(gr(?x6),
        cases(gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x8) & gr(?x6) & gr(?x5),[]),
           ~ (gr(?x8) & gr(?x6) & gr(?x5)),
           contra(gr(?x8) & ~ gr(?x6) & gr(?x5),[]),
           ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(gr(?x8) & gr(?x6) & gr(?x5) \/
            gr(?x8) & ~ gr(?x6) & gr(?x5),
            cases(
             [case(gr(?x8) & ~ gr(?x6) & gr(?x5),
               [gr(?x8) & ~ gr(?x6) & gr(?x5),
                ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
                ff]),
              case(gr(?x8) & gr(?x6) & gr(?x5),
               [gr(?x8) & gr(?x6) & gr(?x5),
                ~ (gr(?x8) & gr(?x6) & gr(?x5)),
                ff])],
             ff)),
           ~ (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
            [gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
             ~ 
             (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
             ff]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8),[]),
           ~ (gr(?x7) & gr(?x8)),
           contra(gr(?x7) & gr(?x8) & gr(?x6),
            [gr(?x7) & gr(?x8),
             ~ (gr(?x7) & gr(?x8)),
             ff]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7),[]),
           ~ ~ gr(?x7),
           contra(~ gr(?x7) & ~ gr(?x8),
            [gr(?x7),
             ~ gr(?x7),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            [~ gr(?x7) & ~ gr(?x8),
             ~ (~ gr(?x7) & ~ gr(?x8)),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         ~ gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8),[gr(?x7),~ gr(?x7),ff]),
           ~ (gr(?x7) & gr(?x8)),
           contra(gr(?x7) & gr(?x8) & gr(?x6),
            [gr(?x7) & gr(?x8),
             ~ (gr(?x7) & gr(?x8)),
             ff]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x8),[]),
           ~ ~ gr(?x8),
           contra(~ gr(?x7) & ~ gr(?x8),[]),
           ~ (~ gr(?x7) & ~ gr(?x8)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            [~ gr(?x7) & ~ gr(?x8),
             ~ (~ gr(?x7) & ~ gr(?x8)),
             ff]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x8) & gr(?x6) & gr(?x5),[]),
           ~ (gr(?x8) & gr(?x6) & gr(?x5)),
           contra(gr(?x8) & ~ gr(?x6) & gr(?x5),[]),
           ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(gr(?x8) & gr(?x6) & gr(?x5) \/
            gr(?x8) & ~ gr(?x6) & gr(?x5),
            cases(
             [case(gr(?x8) & ~ gr(?x6) & gr(?x5),
               [gr(?x8) & ~ gr(?x6) & gr(?x5),
                ~ (gr(?x8) & ~ gr(?x6) & gr(?x5)),
                ff]),
              case(gr(?x8) & gr(?x6) & gr(?x5),
               [gr(?x8) & gr(?x6) & gr(?x5),
                ~ (gr(?x8) & gr(?x6) & gr(?x5)),
                ff])],
             ff)),
           ~ (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
            [gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
             ~ 
             (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)),
             ff]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
         (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
          gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & 
          gr(s(?x5))),
        ~ gr(?x6),
        cases(gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         ~ gr(?x7),
         cases(gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          ~ gr(?x8),
          [contra(gr(?x7) & gr(?x8) & gr(?x6),[]),
           ~ (gr(?x7) & gr(?x8) & gr(?x6)),
           contra(~ gr(?x7) & ~ gr(?x8) & gr(?x6),[]),
           ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(gr(?x7) & gr(?x8) & gr(?x6) \/
            ~ gr(?x7) & ~ gr(?x8) & gr(?x6),
            cases(
             [case(~ gr(?x7) & ~ gr(?x8) & gr(?x6),
               [~ gr(?x7) & ~ gr(?x8) & gr(?x6),
                ~ (~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
                ff]),
              case(gr(?x7) & gr(?x8) & gr(?x6),
               [gr(?x7) & gr(?x8) & gr(?x6),
                ~ (gr(?x7) & gr(?x8) & gr(?x6)),
                ff])],
             ff)),
           ~ 
           (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),
           contra(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[]),
           ~ 
           ((gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6))),
           assume(
            (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
            (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)),[],
            gr(?x7) & gr(?x6) & gr(s(?x5)) \/
            gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
          (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
          (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
           gr(?x7) & gr(?x6) & gr(s(?x5)) \/
           gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
         (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
         (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
          gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & 
          gr(s(?x5))),
        (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
        (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) =>
         gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & gr(s(?x5))),
       (gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5)) &
       (gr(?x7) & gr(?x8) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x8) & gr(?x6)) => 
        gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & gr(s(?x5)))],
     gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & gr(s(?x5)))]))].