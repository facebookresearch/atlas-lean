# Ho Pre Equivalence Edge Lifting of strict lift

Strict simplex-level lifts of equivalence edges give the homotopy
category lifting property: if every equivalence edge of
`(ihom A).obj C` out of a restricted vertex is the strict image
`(e'.map ((pre i).app C)).edge = e.edge` of an equivalence edge `e'` of
`(ihom B).obj C` with strict target restriction, then
`SSet.HoPreEquivalenceEdgeLifting i C` holds, hence (for `C` a
quasicategory) precomposition with `i` induces an isofibration on
homotopy categories. This is the form in which a proof of
TODO(T26-A) by horn filling in `C` produces its lifts (the general case
is now proved, by shuffle-derived prism extension, in
`DwyerKanFinal.lean`).
