[lemma(expr31,
  all [x1,x2,x3]: 
   (succeeds expr(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds expr(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x4,x5,x6,x7,x8],
     [succeeds term(?x7,?x5,?x8),
      succeeds exprr(?x7,?x4,?x8,?x6)],
     ff by gap,
     gr(?x6) & gr(?x5) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & gr(?x4) \/
     gr(?x6) & ~ gr(?x5) & ~ gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & ~ gr(?x4))])),
 lemma(exprr41,
  all [x1,x2,x3,x4]: 
   (succeeds exprr(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) & 
     gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3,x4]: 
     (succeeds exprr(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
       gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x5,x6,x7,x8,x9,x10,x11,x12],
     [gr(?x8) & gr(?x12) & gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)),
      ?x7 = [aop(?x9)|?x10],
      succeeds term(?x11,?x10,?x12),
      succeeds exprr(bin(?x9,?x5,?x11),?x6,?x12,?x8)],
     ff by gap,
     gr(?x8) & gr(?x7) & gr(?x6) & gr(?x5) \/
     gr(?x8) & gr(?x7) & ~ gr(?x6) & ~ gr(?x5) \/
     gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & gr(?x5) \/
     gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) & gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x5)),
    step([x13,x14,x15],
     [?x15 = ?x14],
     ff by gap,
     gr(?x15) & gr(?x14) & gr(?x13) & gr(?x13) \/
     gr(?x15) & gr(?x14) & ~ gr(?x13) & ~ gr(?x13) \/
     gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & gr(?x13) \/
     gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & ~ gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & gr(?x13) & gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & ~ gr(?x13))])),
 lemma(factor31,
  all [x1,x2,x3]: 
   (succeeds factor(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds factor(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x4,x5,x6,x7,x8],
     [?x5 = [leftpar|?x7],
      succeeds expr(?x4,?x7,?x8),
      ?x8 = [rightpar|?x6]],
     ff by gap,
     gr(?x6) & gr(?x5) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & gr(?x4) \/
     gr(?x6) & ~ gr(?x5) & ~ gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & ~ gr(?x4)),
    step([x9,x10,x11],
     [?x10 = [id(?x9)|?x11]],
     ff by gap,
     gr(?x11) & gr(?x10) & gr(var(?x9)) \/
     ~ gr(?x11) & ~ gr(?x10) & gr(var(?x9)) \/
     gr(?x11) & ~ gr(?x10) & ~ gr(var(?x9)) \/
     ~ gr(?x11) & ~ gr(?x10) & ~ gr(var(?x9))),
    step([x12,x13,x14],
     [?x13 = [num(?x12)|?x14]],
     ff by gap,
     gr(?x14) & gr(?x13) & gr(con(?x12)) \/
     ~ gr(?x14) & ~ gr(?x13) & gr(con(?x12)) \/
     gr(?x14) & ~ gr(?x13) & ~ gr(con(?x12)) \/
     ~ gr(?x14) & ~ gr(?x13) & ~ gr(con(?x12)))])),
 lemma(term31,
  all [x1,x2,x3]: 
   (succeeds term(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds term(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x4,x5,x6,x7,x8],
     [succeeds factor(?x7,?x5,?x8),
      succeeds termr(?x7,?x4,?x8,?x6)],
     ff by gap,
     gr(?x6) & gr(?x5) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & gr(?x4) \/
     gr(?x6) & ~ gr(?x5) & ~ gr(?x4) \/ ~ gr(?x6) & ~ gr(?x5) & ~ gr(?x4))])),
 lemma(termr41,
  all [x1,x2,x3,x4]: 
   (succeeds termr(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) & 
     gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3,x4]: 
     (succeeds termr(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
       gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x5,x6,x7,x8,x9,x10,x11,x12],
     [gr(?x8) & gr(?x12) & gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & gr(bin(?x9,?x5,?x11)) \/
      ~ gr(?x8) & ~ gr(?x12) & ~ gr(?x6) & ~ gr(bin(?x9,?x5,?x11)),
      ?x7 = [mop(?x9)|?x10],
      succeeds factor(?x11,?x10,?x12),
      succeeds termr(bin(?x9,?x5,?x11),?x6,?x12,?x8)],
     ff by gap,
     gr(?x8) & gr(?x7) & gr(?x6) & gr(?x5) \/
     gr(?x8) & gr(?x7) & ~ gr(?x6) & ~ gr(?x5) \/
     gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & gr(?x5) \/
     gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) & gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x5)),
    step([x13,x14,x15],
     [?x15 = ?x14],
     ff by gap,
     gr(?x15) & gr(?x14) & gr(?x13) & gr(?x13) \/
     gr(?x15) & gr(?x14) & ~ gr(?x13) & ~ gr(?x13) \/
     gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & gr(?x13) \/
     gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & ~ gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & gr(?x13) & gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & gr(?x13) \/
     ~ gr(?x15) & ~ gr(?x14) & ~ gr(?x13) & ~ gr(?x13))]))].