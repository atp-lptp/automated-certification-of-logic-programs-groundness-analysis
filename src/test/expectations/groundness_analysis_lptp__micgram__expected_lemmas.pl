[lemma(ident21,
  all [x1,x2]: 
   (succeeds ident(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds ident(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & ~ gr(?x1))],
   [step([x3,x4],
     [?x3 = [97|?x4]],
     ff by gap,
     gr(?x4) & gr(?x3) \/ ~ gr(?x4) & ~ gr(?x3))])),
 lemma(q51,
  all [x1,x2,x3,x4,x5]: 
   (succeeds q(?x1,?x2,?x3,?x4,?x5) => gr(?x5) & gr(?x4) & gr(?x3) & 
     gr(?x2) & gr(?x1) \/
     gr(?x5) & gr(?x4) & ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x5) & gr(?x4) & gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x5) & gr(?x4) & ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
     gr(?x5) & ~ gr(?x4) & gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     gr(?x5) & ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x5) & ~ gr(?x4) & gr(?x3) & ~ gr(?x2) & gr(?x1) \/
     ~ gr(?x5) & ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3,x4,x5]: 
     (succeeds q(?x1,?x2,?x3,?x4,?x5) => gr(?x5) & gr(?x4) & gr(?x3) &
       gr(?x2) & gr(?x1) \/
       gr(?x5) & gr(?x4) & ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x5) & gr(?x4) & gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x5) & gr(?x4) & ~ gr(?x3) & gr(?x2) & ~ gr(?x1) \/
       gr(?x5) & ~ gr(?x4) & gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       gr(?x5) & ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x5) & ~ gr(?x4) & gr(?x3) & ~ gr(?x2) & gr(?x1) \/
       ~ gr(?x5) & ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x6,x7,x8],[],
     ff by gap,
     gr(?x8) & gr(?x7) & gr(?x6) & gr(?x7) & gr(?x6) \/
     gr(?x8) & gr(?x7) & ~ gr(?x6) & gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & gr(?x7) & gr(?x6) & gr(?x7) & gr(?x6) \/
     ~ gr(?x8) & gr(?x7) & ~ gr(?x6) & gr(?x7) & ~ gr(?x6) \/
     gr(?x8) & ~ gr(?x7) & gr(?x6) & ~ gr(?x7) & gr(?x6) \/
     gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x7) & ~ gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) & ~ gr(?x7) & gr(?x6) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x7) & ~ gr(?x6))])),
 lemma(p22,
  all [x1,x2]: 
   (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1) \/
     ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2]: 
     (succeeds p(?x1,?x2) => gr(?x2) & gr(?x1) \/ ~ gr(?x2) & gr(?x1) \/
       ~ gr(?x2) & ~ gr(?x1))],
   [step([x3],[],
     ff by gap,
     gr(?x3) & gr(?x3) \/ ~ gr(?x3) & gr(?x3) \/ ~ gr(?x3) & ~ gr(?x3)),
    step([x4],
     [succeeds ident(4,?x4)],
     ff by gap,
     gr(?x4) & gr(2) \/ ~ gr(?x4) & gr(2) \/ ~ gr(?x4) & ~ gr(2)),
    step([x5,x6],
     [succeeds ident(5,?x6),
      succeeds ident(6,?x5)],
     ff by gap,
     gr(?x5) & gr(3) \/ ~ gr(?x5) & gr(3) \/ ~ gr(?x5) & ~ gr(3)),
    step([x7,x8],
     [?x8 = ?x7,
      succeeds ident(?x8,?x8)],
     ff by gap,
     gr(?x7) & gr(4) \/ ~ gr(?x7) & gr(4) \/ ~ gr(?x7) & ~ gr(4))]))].