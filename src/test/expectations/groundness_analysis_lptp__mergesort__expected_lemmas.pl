[lemma(lesseq21,
  all [x1,x2]: 
   (succeeds lesseq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds lesseq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1))],
   [step([x3],[],ff by gap,gr(?x3) & gr(0) \/ ~ gr(?x3) & gr(0)),
    step([x4,x5],
     [gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
      succeeds lesseq(?x4,?x5)],
     ff by gap,
     gr(s(?x5)) & gr(s(?x4)) \/ ~ gr(s(?x5)) & gr(s(?x4)))])),
 lemma(greater21,
  all [x1,x2]: 
   (succeeds greater(?x1,?x2) => gr(?x2) & gr(?x1) \/ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds greater(?x1,?x2) => gr(?x2) & gr(?x1) \/ gr(?x2) & ~ gr(?x1))],
   [step([x3],[],ff by gap,gr(0) & gr(s(?x3)) \/ gr(0) & ~ gr(s(?x3))),
    step([x4,x5],
     [gr(?x5) & gr(?x4) \/ gr(?x5) & ~ gr(?x4),
      succeeds greater(?x4,?x5)],
     ff by gap,
     gr(s(?x5)) & gr(s(?x4)) \/ gr(s(?x5)) & ~ gr(s(?x4)))])),
 lemma(split31,
  all [x1,x2,x3]: 
   (succeeds split(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds split(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],
     ff by gap,
     gr([]) & gr([]) & gr([]) \/ gr([]) & ~ gr([]) & ~ gr([]) \/ ~ gr([]) & gr([]) & ~ gr([]) \/
     ~ gr([]) & ~ gr([]) & ~ gr([])),
    step([x4,x5,x6,x7],
     [gr(?x6) & gr(?x7) & gr(?x5) \/ gr(?x6) & ~ gr(?x7) & ~ gr(?x5) \/
      ~ gr(?x6) & gr(?x7) & ~ gr(?x5) \/ ~ gr(?x6) & ~ gr(?x7) & ~ gr(?x5),
      succeeds split(?x5,?x7,?x6)],
     ff by gap,
     gr(?x7) & gr([?x4|?x6]) & gr([?x4|?x5]) \/
     gr(?x7) & ~ gr([?x4|?x6]) & ~ gr([?x4|?x5]) \/
     ~ gr(?x7) & gr([?x4|?x6]) & ~ gr([?x4|?x5]) \/
     ~ gr(?x7) & ~ gr([?x4|?x6]) & ~ gr([?x4|?x5]))])),
 lemma(merge31,
  all [x1,x2,x3]: 
   (succeeds merge(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds merge(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1))],
   [step([x4],[],
     ff by gap,
     gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
     ~ gr(?x4) & ~ gr(?x4) & gr([])),
    step([x5],[],
     ff by gap,
     gr(?x5) & gr([]) & gr(?x5) \/ ~ gr(?x5) & gr([]) & ~ gr(?x5) \/
     ~ gr(?x5) & ~ gr([]) & gr(?x5)),
    step([x6,x7,x8,x9,x10],
     [gr(?x10) & gr([?x8|?x9]) & gr(?x7) \/
      ~ gr(?x10) & gr([?x8|?x9]) & ~ gr(?x7) \/
      ~ gr(?x10) & ~ gr([?x8|?x9]) & gr(?x7),
      succeeds lesseq(?x6,?x8),
      succeeds merge(?x7,[?x8|?x9],?x10)],
     ff by gap,
     gr([?x6|?x10]) & gr([?x8|?x9]) & gr([?x6|?x7]) \/
     ~ gr([?x6|?x10]) & gr([?x8|?x9]) & ~ gr([?x6|?x7]) \/
     ~ gr([?x6|?x10]) & ~ gr([?x8|?x9]) & gr([?x6|?x7])),
    step([x11,x12,x13,x14,x15],
     [gr(?x15) & gr(?x14) & gr([?x11|?x12]) \/
      ~ gr(?x15) & gr(?x14) & ~ gr([?x11|?x12]) \/
      ~ gr(?x15) & ~ gr(?x14) & gr([?x11|?x12]),
      succeeds greater(?x11,?x13),
      succeeds merge([?x11|?x12],?x14,?x15)],
     ff by gap,
     gr([?x13|?x15]) & gr([?x13|?x14]) & gr([?x11|?x12]) \/
     ~ gr([?x13|?x15]) & gr([?x13|?x14]) & ~ gr([?x11|?x12]) \/
     ~ gr([?x13|?x15]) & ~ gr([?x13|?x14]) & gr([?x11|?x12]))])),
 lemma(mergesort21,
  all [x1,x2]: 
   (succeeds mergesort(?x1,?x2) => gr(?x2) & gr(?x1) \/
     ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds mergesort(?x1,?x2) => gr(?x2) & gr(?x1) \/
       ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],ff by gap,gr([]) & gr([]) \/ ~ gr([]) & ~ gr([])),
    step([x3],[],
     ff by gap,
     gr([?x3]) & gr([?x3]) \/ ~ gr([?x3]) & ~ gr([?x3])),
    step([x4,x5,x6,x7,x8,x9,x10,x11,x12],
     [gr(?x11) & gr(?x9) \/ ~ gr(?x11) & ~ gr(?x9),
      gr(?x12) & gr(?x10) \/ ~ gr(?x12) & ~ gr(?x10),
      ?x4 = [?x6,?x7|?x8],
      succeeds split(?x4,?x9,?x10),
      succeeds mergesort(?x9,?x11),
      succeeds mergesort(?x10,?x12),
      succeeds merge(?x11,?x12,?x5)],
     ff by gap,
     gr(?x5) & gr(?x4) \/ ~ gr(?x5) & ~ gr(?x4))]))].