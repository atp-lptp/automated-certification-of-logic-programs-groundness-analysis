
[lemma(expr_bl41,
  all [x1,x2,x3,x4]:
   (succeeds expr_bl(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
     gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3,x4]:
     (succeeds expr_bl(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
       gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x5,x6],[],
     ff by gap,
     gr(?x6) & gr(?x6) & gr(?x5) & gr(?x5) \/
     gr(?x6) & gr(?x6) & ~ gr(?x5) & ~ gr(?x5) \/
     ~ gr(?x6) & ~ gr(?x6) & gr(?x5) & gr(?x5) \/
     ~ gr(?x6) & ~ gr(?x6) & ~ gr(?x5) & ~ gr(?x5)),
    step([x7,x8,x9,x10,x11,x12],
     [succeeds expr_bl2(?x7,?x11,?x9,?x12),
      succeeds expr_bl2(?x11,?x8,?x12,?x10)],
     ff by gap,
     gr(?x10) & gr(l(?x9)) & gr(?x8) & gr([op|?x7]) \/
     gr(?x10) & gr(l(?x9)) & ~ gr(?x8) & ~ gr([op|?x7]) \/
     ~ gr(?x10) & ~ gr(l(?x9)) & gr(?x8) & gr([op|?x7]) \/
     ~ gr(?x10) & ~ gr(l(?x9)) & ~ gr(?x8) & ~ gr([op|?x7]))])),
 lemma(expr_bl241,
  all [x1,x2,x3,x4]:
   (succeeds expr_bl2(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
     gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
     ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1)),
  induction(
   [all [x1,x2,x3,x4]:
     (succeeds expr_bl2(?x1,?x2,?x3,?x4) => gr(?x4) & gr(?x3) & gr(?x2) &
       gr(?x1) \/ gr(?x4) & gr(?x3) & ~ gr(?x2) & ~ gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & gr(?x2) & gr(?x1) \/
       ~ gr(?x4) & ~ gr(?x3) & ~ gr(?x2) & ~ gr(?x1))],
   [step([x5,x6,x7,x8],
     [succeeds expr_bl(?x5,?x6,?x7,?x8)],
     ff by gap,
     gr(?x8) & gr(?x7) & gr(?x6) & gr(?x5) \/
     gr(?x8) & gr(?x7) & ~ gr(?x6) & ~ gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & gr(?x6) & gr(?x5) \/
     ~ gr(?x8) & ~ gr(?x7) & ~ gr(?x6) & ~ gr(?x5))]))].
