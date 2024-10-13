[lemma(add32,
  all [x1,x2,x3]: 
   (succeeds add(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds add(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4],[],
     ff by gap,
     gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7],
     [gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
      succeeds add(?x5,?x6,?x7)],
     ff by gap,
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
     ff by gap,
     gr(0) & gr(?x4) & gr(0) \/ gr(0) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7,x8],
     [gr(?x8) & gr(?x6) & gr(?x5) \/ gr(?x8) & ~ gr(?x6) & gr(?x5),
      succeeds mul(?x5,?x6,?x8),
      succeeds add(?x6,?x8,?x7)],
     ff by gap,
     gr(?x7) & gr(?x6) & gr(s(?x5)) \/ gr(?x7) & ~ gr(?x6) & gr(s(?x5)))]))].