[lemma(p22,
  all [x1,x2]: 
   (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([],[],ff by gap,gr(0) & gr(0) \/ ~ gr(0) & ~ gr(0)),
    step([x3],[],
     ff by gap,
     gr(?x3) & gr(s(?x3)) \/ ~ gr(?x3) & ~ gr(s(?x3)))])),
 lemma(eq22,
  all [x1,x2]: 
   (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds eq(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([x3],[],ff by gap,gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3))])),
 lemma(average31,
  all [x1,x2,x3]: 
   (succeeds average(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds average(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1))],
   [step([x4],
     [succeeds !,
      succeeds eq(?x4,0)],
     ff by gap,
     gr(?x4) & gr(0) & gr(0)),
    step([x5],
     [succeeds !,
      succeeds eq(?x5,0)],
     ff by gap,
     gr(?x5) & gr(s(0)) & gr(0)),
    step([x6],
     [succeeds !,
      succeeds eq(?x6,s(0))],
     ff by gap,
     gr(?x6) & gr(s(s(0))) & gr(0)),
    step([x7,x8,x9,x10],
     [gr(?x9) & gr(s(?x8)) & gr(?x10),
      succeeds p(?x7,?x10),
      succeeds average(?x10,s(?x8),?x9)],
     ff by gap,
     gr(?x9) & gr(?x8) & gr(?x7)),
    step([x11,x12,x13,x14,x15,x16,x17],
     [gr(?x17) & gr(?x16) & gr(s(?x11)),
      succeeds p(?x12,?x14),
      succeeds p(?x14,?x15),
      succeeds p(?x15,?x16),
      succeeds average(s(?x11),?x16,?x17),
      succeeds p(?x13,?x17)],
     ff by gap,
     gr(?x13) & gr(?x12) & gr(?x11))]))].