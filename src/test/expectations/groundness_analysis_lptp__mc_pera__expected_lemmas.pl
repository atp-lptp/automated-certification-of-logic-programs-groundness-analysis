[lemma(app31,
  all [x1,x2,x3]: 
   (succeeds app(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds app(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x4],[],
     ff by gap,
     gr(?x4) & gr(?x4) & gr([]) \/ ~ gr(?x4) & gr(?x4) & ~ gr([]) \/
     ~ gr(?x4) & ~ gr(?x4) & gr([]) \/ ~ gr(?x4) & ~ gr(?x4) & ~ gr([])),
    step([x5,x6,x7,x8],
     [gr(?x8) & gr(?x7) & gr(?x6) \/ ~ gr(?x8) & gr(?x7) & ~ gr(?x6) \/
      ~ gr(?x8) & ~ gr(?x7) & gr(?x6) \/ ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6),
      succeeds app(?x6,?x7,?x8)],
     ff by gap,
     gr([?x5|?x8]) & gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & gr(?x7) & ~ gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & gr([?x5|?x6]) \/
     ~ gr([?x5|?x8]) & ~ gr(?x7) & ~ gr([?x5|?x6]))])),
 lemma(rev21,
  all [x1,x2]: 
   (succeeds rev(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds rev(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],ff by gap,gr([]) & gr([]) \/ ~ gr([]) & ~ gr([])),
    step([x3,x4,x5,x6],
     [gr(?x6) & gr(?x4) \/ ~ gr(?x6) & ~ gr(?x4),
      succeeds rev(?x4,?x6),
      succeeds app(?x6,[?x3],?x5)],
     ff by gap,
     gr(?x5) & gr([?x3|?x4]) \/ ~ gr(?x5) & ~ gr([?x3|?x4]))])),
 lemma(eq21,
  all [x1,x2]: 
   (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([x3],[],ff by gap,gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3))])),
 lemma(p22,
  all [x1,x2]: 
   (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],ff by gap,gr([]) & gr([]) \/ ~ gr([]) & ~ gr([])),
    step([x3,x4,x5,x6,x7],
     [gr(?x7) & gr(?x6) \/ ~ gr(?x7) & ~ gr(?x6),
      succeeds eq(?x3,?x4),
      succeeds rev(?x4,[?x5|?x6]),
      succeeds p(?x6,?x7)],
     ff by gap,
     gr(?x4) & gr(?x3) \/ ~ gr(?x4) & ~ gr(?x3))]))].