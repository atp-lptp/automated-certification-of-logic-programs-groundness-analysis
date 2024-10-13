[lemma(plus31,
  all [x1,x2,x3]: 
   (succeeds plus(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds plus(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4],[],
     ff by gap,
     gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7],
     [gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
      succeeds plus(?x5,?x6,?x7)],
     ff by gap,
     gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
     ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))])),
 lemma(gcd31,
  all [x1,x2,x3]: 
   (succeeds gcd(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds gcd(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4,x5,x6],
     [succeeds ?x4 @=< ?x5,
      succeeds gcd_leq(?x4,?x5,?x6)],
     ff by gap,
     gr(?x6) & gr(?x5) & gr(?x4) \/ ~ gr(?x6) & gr(?x5) & ~ gr(?x4) \/
     ~ gr(?x6) & ~ gr(?x5) & gr(?x4)),
    step([x7,x8,x9],
     [succeeds \+ ?x7 @=< ?x8,
      succeeds gcd_leq(?x8,?x7,?x9)],
     ff by gap,
     gr(?x9) & gr(?x8) & gr(?x7) \/ ~ gr(?x9) & gr(?x8) & ~ gr(?x7) \/
     ~ gr(?x9) & ~ gr(?x8) & gr(?x7))])),
 lemma(gcd_leq31,
  all [x1,x2,x3]: 
   (succeeds gcd_leq(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds gcd_leq(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4,x5,x6],
     [?x4 = 0,
      ?x6 = ?x5],
     ff by gap,
     gr(?x6) & gr(?x5) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & gr(?x4)),
    step([x7,x8,x9,x10],
     [succeeds \+ ?x7 = 0,
      succeeds plus(?x7,?x10,?x8),
      succeeds gcd(?x7,?x10,?x9)],
     ff by gap,
     gr(?x9) & gr(?x8) & gr(?x7) \/ ~ gr(?x9) & ~ gr(?x8) & gr(?x7))]))]