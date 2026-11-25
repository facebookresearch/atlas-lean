# Rank One zero Class eq boundary

Rank-one zero-class boundary converse for continuous degree-one cohomology.

Given a homogeneous degree-one element `y` with rank-one cocycle morphism
`z = ofHom ((toSpanSingleton k y).comp uliftDown)`, a cycle proof `hz`, and a zero-class
hypothesis `hzero` for the lifted cycle under `homologyπ 1`, there is an
explicit degree-zero rank-one morphism `w` with `z = w ≫ d 0 1`.

Reuses `HomologicalComplex.homologyIsCokernel 0 1`,
`TopModuleCat.isColimitCoker` with `TopModuleCat.cokerπ`,
`CategoryTheory.IsColimit.comp_coconePointUniqueUpToIso_hom`,
`HomologicalComplex.liftCycles` with `K.toCycles` and `K.homologyπ`,
`Submodule.Quotient.mk_eq_zero`, `HomologicalComplex.liftCycles_i`,
`HomologicalComplex.toCycles_i`, and
`ContinuousLinearMap.toSpanSingleton` round-trip facts. The rank-one domain is
the universe-raised `TopModuleCat.of k (ULift k)`.

Nonclaims: no Kummer, motivic, etale, or comparison statement; rank-one
domain only; no higher-weight statement.
