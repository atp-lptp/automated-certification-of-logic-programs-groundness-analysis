[lemma(inf221,
  all [x1,x2]: 
   (succeeds inf2(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds inf2(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1))],
   [step([x3],[],ff by gap,gr(s(?x3)) & gr(0) \/ ~ gr(s(?x3)) & gr(0)),
    step([x4,x5],
     [gr(?x5) & gr(?x4) \/ ~ gr(?x5) & gr(?x4),
      succeeds inf2(?x4,?x5)],
     ff by gap,
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
     ff by gap,
     gr(f(0,?x4)) & gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & gr(f(0,?x3)) \/
     gr(f(0,?x4)) & ~ gr(f(0,?x3)) \/ ~ gr(f(0,?x4)) & ~ gr(f(0,?x3))),
    step([x5,x6,x7],[],
     ff by gap,
     gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/ ~ gr(f(s(?x6),?x7)) & gr(f(0,?x5)) \/
     gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5)) \/
     ~ gr(f(s(?x6),?x7)) & ~ gr(f(0,?x5))),
    step([x8,x9,x10,x11],
     [gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
      ~ gr(f(?x10,?x11)) & gr(f(?x8,?x9)) \/
      gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)) \/
      ~ gr(f(?x10,?x11)) & ~ gr(f(?x8,?x9)),
      succeeds inf4(f(?x8,?x9),f(?x10,?x11))],
     ff by gap,
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
     ff by gap,
     gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)),
    step([x5,x6,x7],
     [gr(?x7) & gr(?x6) & gr(?x5) \/ ~ gr(?x7) & ~ gr(?x6) & gr(?x5),
      succeeds add(?x5,?x6,?x7)],
     ff by gap,
     gr(s(?x7)) & gr(?x6) & gr(s(?x5)) \/
     ~ gr(s(?x7)) & ~ gr(?x6) & gr(s(?x5)))]))].