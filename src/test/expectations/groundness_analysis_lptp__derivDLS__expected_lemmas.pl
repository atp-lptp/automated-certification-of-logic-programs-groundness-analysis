[lemma(deriv31,
  all [x1,x2,x3]: 
   (succeeds deriv(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
     gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3]: 
     (succeeds deriv(?x1,?x2,?x3) => gr(?x3) & gr(?x2) & gr(?x1) \/
       gr(?x3) & gr(?x2) & ~ gr(?x1) \/ ~ gr(?x3) & gr(?x2) & ~ gr(?x1))],
   [step([],[],
     ff by gap,
     gr(1) & gr(t) & gr(d(t)) \/ gr(1) & gr(t) & ~ gr(d(t)) \/
     ~ gr(1) & gr(t) & ~ gr(d(t))),
    step([x4],
     [succeeds atom(?x4)],
     ff by gap,
     gr(0) & gr(t) & gr(d(?x4)) \/ gr(0) & gr(t) & ~ gr(d(?x4)) \/
     ~ gr(0) & gr(t) & ~ gr(d(?x4))),
    step([x5,x6,x7,x8],
     [gr(?x7) & gr(t) & gr(d(?x5)) \/ gr(?x7) & gr(t) & ~ gr(d(?x5)) \/
      ~ gr(?x7) & gr(t) & ~ gr(d(?x5)),
      gr(?x8) & gr(t) & gr(d(?x6)) \/ gr(?x8) & gr(t) & ~ gr(d(?x6)) \/
      ~ gr(?x8) & gr(t) & ~ gr(d(?x6)),
      succeeds deriv(d(?x5),t,?x7),
      succeeds deriv(d(?x6),t,?x8)],
     ff by gap,
     gr(?x7 + ?x8) & gr(t) & gr(d(?x5 + ?x6)) \/
     gr(?x7 + ?x8) & gr(t) & ~ gr(d(?x5 + ?x6)) \/
     ~ gr(?x7 + ?x8) & gr(t) & ~ gr(d(?x5 + ?x6))),
    step([x9,x10,x11,x12],
     [gr(?x12) & gr(t) & gr(d(?x9)) \/ gr(?x12) & gr(t) & ~ gr(d(?x9)) \/
      ~ gr(?x12) & gr(t) & ~ gr(d(?x9)),
      gr(?x11) & gr(t) & gr(d(?x10)) \/ gr(?x11) & gr(t) & ~ gr(d(?x10)) \/
      ~ gr(?x11) & gr(t) & ~ gr(d(?x10)),
      succeeds deriv(d(?x9),t,?x12),
      succeeds deriv(d(?x10),t,?x11)],
     ff by gap,
     gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & gr(d(?x9 * ?x10)) \/
     gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & ~ gr(d(?x9 * ?x10)) \/
     ~ gr(?x9 * ?x11 + ?x10 * ?x12) & gr(t) & ~ gr(d(?x9 * ?x10))),
    step([x13,x14,x15],
     [gr(?x15) & gr(t) & gr(d(?x13)) \/ gr(?x15) & gr(t) & ~ gr(d(?x13)) \/
      ~ gr(?x15) & gr(t) & ~ gr(d(?x13)),
      gr(?x14) & gr(t) & gr(d(?x15)) \/ gr(?x14) & gr(t) & ~ gr(d(?x15)) \/
      ~ gr(?x14) & gr(t) & ~ gr(d(?x15)),
      succeeds deriv(d(?x13),t,?x15),
      succeeds deriv(d(?x15),t,?x14)],
     ff by gap,
     gr(?x14) & gr(t) & gr(d(d(?x13))) \/
     gr(?x14) & gr(t) & ~ gr(d(d(?x13))) \/
     ~ gr(?x14) & gr(t) & ~ gr(d(d(?x13))))]))].