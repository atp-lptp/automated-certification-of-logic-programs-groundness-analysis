[cases(gr(?x4),
  [gr(?x4) & gr(?x4),
   gr(?x4) & gr(?x4) & gr(0),
   gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)],
  ~ gr(?x4),
  [~ gr(?x4) & ~ gr(?x4),
   ~ gr(?x4) & ~ gr(?x4) & gr(0),
   gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0)],
  gr(?x4) & gr(?x4) & gr(0) \/ ~ gr(?x4) & ~ gr(?x4) & gr(0))].
