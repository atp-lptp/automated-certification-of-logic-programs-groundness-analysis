[cases(gr(?x5),
  cases(gr(?x6),
   cases(gr(?x7),
    cases(gr(?x8),
     [gr(?x8) & gr(?x7),
      gr(?x8) & gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      gr(?x5) & gr(?x8),
      gr([?x5|?x8]) => gr(?x5) & gr(?x8),
      assume(~ (gr(?x5) & gr(?x8)),
       contra(gr([?x5|?x8]),
        [gr(?x5) & gr(?x8),
         ff]),
       ~ gr([?x5|?x8])),
      gr([?x5|?x8]) <=> gr(?x5) & gr(?x8) by lemma(axiom_2_5),
      gr([?x5|?x8]) & gr(?x7),
      gr(?x5) & gr(?x6),
      gr([?x5|?x6]) => gr(?x5) & gr(?x6),
      assume(~ (gr(?x5) & gr(?x6)),
       contra(gr([?x5|?x6]),
        [gr(?x5) & gr(?x6),
         ff]),
       ~ gr([?x5|?x6])),
      gr([?x5|?x6]) <=> gr(?x5) & gr(?x6) by lemma(axiom_2_5),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [contra(gr(?x8) & gr(?x7),[gr(?x8),~ gr(?x8),ff]),
      ~ (gr(?x8) & gr(?x7)),
      contra(gr(?x8) & gr(?x7) & gr(?x6),
       [gr(?x8) & gr(?x7),
        ~ (gr(?x8) & gr(?x7)),
        ff]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x7),[]),
      ~ ~ gr(?x7),
      contra(~ gr(?x8) & ~ gr(?x7),[]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    ~ gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7),[]),
      ~ (gr(?x8) & gr(?x7)),
      contra(gr(?x8) & gr(?x7) & gr(?x6),
       [gr(?x8) & gr(?x7),
        ~ (gr(?x8) & gr(?x7)),
        ff]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & ~ gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & ~ gr(?x7),
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7),
      gr(?x5) & gr(?x6),
      gr([?x5|?x6]) => gr(?x5) & gr(?x6),
      assume(~ (gr(?x5) & gr(?x6)),
       contra(gr([?x5|?x6]),
        [gr(?x5) & gr(?x6),
         ff]),
       ~ gr([?x5|?x6])),
      gr([?x5|?x6]) <=> gr(?x5) & gr(?x6) by lemma(axiom_2_5),
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
    ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
     gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
   ~ gr(?x6),
   cases(gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7) & gr(?x6),[]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & gr(?x7)),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & gr(?x7),
        ~ (~ gr(?x8) & gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x7),[]),
      ~ ~ gr(?x7),
      contra(~ gr(?x8) & ~ gr(?x7),[]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & gr(?x7),
      ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    ~ gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7) & gr(?x6),[]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x8) & gr(?x7),[]),
      ~ (~ gr(?x8) & gr(?x7)),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & gr(?x7),
        ~ (~ gr(?x8) & gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & ~ gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & ~ gr(?x7),
      ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
    ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
     gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
   gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
   ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) => 
    gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
  ~ gr(?x5),
  cases(gr(?x6),
   cases(gr(?x7),
    cases(gr(?x8),
     [gr(?x8) & gr(?x7),
      gr(?x8) & gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [contra(gr(?x8) & gr(?x7),[gr(?x8),~ gr(?x8),ff]),
      ~ (gr(?x8) & gr(?x7)),
      contra(gr(?x8) & gr(?x7) & gr(?x6),
       [gr(?x8) & gr(?x7),
        ~ (gr(?x8) & gr(?x7)),
        ff]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x7),[]),
      ~ ~ gr(?x7),
      contra(~ gr(?x8) & ~ gr(?x7),[]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    ~ gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7),[]),
      ~ (gr(?x8) & gr(?x7)),
      contra(gr(?x8) & gr(?x7) & gr(?x6),
       [gr(?x8) & gr(?x7),
        ~ (gr(?x8) & gr(?x7)),
        ff]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & ~ gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x6),[]),
      ~ ~ gr(?x6),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & ~ gr(?x7),
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
    ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
     gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
   ~ gr(?x6),
   cases(gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7) & gr(?x6),[]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & gr(?x7)),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & gr(?x7),
        ~ (~ gr(?x8) & gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x7),[]),
      ~ ~ gr(?x7),
      contra(~ gr(?x8) & ~ gr(?x7),[]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & gr(?x7),
      ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    ~ gr(?x7),
    cases(gr(?x8),
     [contra(gr(?x8) & gr(?x7) & gr(?x6),[]),
      ~ (gr(?x8) & gr(?x7) & gr(?x6)),
      contra(~ gr(?x8) & gr(?x7),[]),
      ~ (~ gr(?x8) & gr(?x7)),
      contra(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & gr(?x7),
        ~ (~ gr(?x8) & gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
      contra(~ gr(?x8) & ~ gr(?x7) & gr(?x6),[]),
      ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
      contra(~ gr(?x8),[]),
      ~ ~ gr(?x8),
      contra(~ gr(?x8) & ~ gr(?x7),
       [gr(?x8),
        ~ gr(?x8),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7)),
      contra(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       [~ gr(?x8) & ~ gr(?x7),
        ~ (~ gr(?x8) & ~ gr(?x7)),
        ff]),
      ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      contra(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
       cases(
        [case(~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
           ff]),
         case(~ gr(?x8) & ~ gr(?x7) & gr(?x6),
          [~ gr(?x8) & ~ gr(?x7) & gr(?x6),
           ~ (~ gr(?x8) & ~ gr(?x7) & gr(?x6)),
           ff]),
         case(~ gr(?x8) & gr(?x7) & ~ gr(?x6),
          [~ gr(?x8) & gr(?x7) & ~ gr(?x6),
           ~ (~ gr(?x8) & gr(?x7) & ~ gr(?x6)),
           ff]),
         case(gr(?x8) & gr(?x7) & gr(?x6),
          [gr(?x8) & gr(?x7) & gr(?x6),
           ~ (gr(?x8) & gr(?x7) & gr(?x6)),
           ff])],
        ff)),
      ~ 
      (gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6)),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     ~ gr(?x8),
     [~ gr(?x8) & ~ gr(?x7),
      ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      ~ gr(?x5) \/ ~ gr(?x8),
      ~ gr([?x5|?x8]) <=> ~ gr(?x5) \/ ~ gr(?x8) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7),
      ~ gr(?x5) \/ ~ gr(?x6),
      ~ gr([?x5|?x6]) <=> ~ gr(?x5) \/ ~ gr(?x6) by 
       lemma(axiom_2_5_de_morgan),
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]),
      assume(gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
       ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),[],
       gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
       ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))],
     gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
      gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
      ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
    gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
    ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) =>
     gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
   gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
   ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) => 
    gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
    ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6])),
  gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
  ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) => 
   gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
   ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
   ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
   ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))].
