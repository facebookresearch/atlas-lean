/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineIsometry.Contexts

set_option linter.unusedSectionVars false

open AffineIsometryBuilding DVRContext


/-- A periodic lattice chain in the alternating-form setting (type $\tilde C_n$):
an $\mathbb{Z}$-indexed family of $\mathfrak{o}$-lattices ascending, periodic
with period $2n$ up to scaling by $\pi$, with the prescribed
isotropy/duality relations under the alternating form. -/
structure PeriodicChainAlternating (ctx : AlternatingBuildingContext) where
  chain : ℤ → OLattice ctx.C
  primitive_at_zero : ∀ v ∈ (chain 0).carrier, ∀ w ∈ (chain 0).carrier,
    ctx.C.isInO (ctx.form v w)
  ascending : ∀ i : ℤ,
    latticeContained ctx.C (chain i) (chain (i + 1))
  periodic : ∀ i : ℤ, ∀ v ∈ (chain (i + 2 * ↑ctx.wittIndex)).carrier,
    ctx.C.oscal ctx.C.uniformizer v ∈ (chain i).carrier
  duality : ∀ (j : ℕ), 1 ≤ j → j ≤ ctx.wittIndex - 1 →
    ∀ v ∈ (chain (↑ctx.wittIndex + ↑j)).carrier,
    ∀ w ∈ (chain (↑ctx.wittIndex - ↑j)).carrier,
      ctx.C.isInMaxIdeal (ctx.form v w)
  flag_isotropic : ∀ (i : ℕ), 1 ≤ i → i ≤ ctx.wittIndex →
    formValuesInMaxIdeal ctx.C ctx.form (chain ↑i)

/-- A periodic lattice chain for the double oriflamme building (type
$\tilde D_n$): two unimodular lattices at level $0$ and at the top level
$N$, with intermediate lattices in between. -/
structure PeriodicChainDoubleOriflamme (ctx : DoubleOriflammeContext) where
  lat0_1 : OLattice ctx.C
  lat0_2 : OLattice ctx.C
  latN_1 : OLattice ctx.C
  latN_2 : OLattice ctx.C
  chain_mid : ∀ (i : ℕ), 2 ≤ i → i ≤ ctx.halfDim - 2 → OLattice ctx.C
  prim0_1 : ∀ v ∈ lat0_1.carrier, ∀ w ∈ lat0_1.carrier,
    ctx.C.isInO (ctx.form v w)
  prim0_2 : ∀ v ∈ lat0_2.carrier, ∀ w ∈ lat0_2.carrier,
    ctx.C.isInO (ctx.form v w)
  contain_01 : ∀ (i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ ctx.halfDim - 2),
    latticeContained ctx.C lat0_1 (chain_mid i h1 h2)
  contain_02 : ∀ (i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ ctx.halfDim - 2),
    latticeContained ctx.C lat0_2 (chain_mid i h1 h2)
  lat0_distinct : lat0_1.carrier ≠ lat0_2.carrier
  latN_distinct : latN_1.carrier ≠ latN_2.carrier

/-- A periodic lattice chain for the single oriflamme building (type
$\tilde B_n$): two unimodular lattices at level $0$ and a chain of
intermediate lattices indexed by $2 \le i \le n$. -/
structure PeriodicChainSingleOriflamme (ctx : SingleOriflammeContext) where
  lat0_1 : OLattice ctx.C
  lat0_2 : OLattice ctx.C
  chain : ∀ (i : ℕ), 2 ≤ i → i ≤ ctx.wittIndex → OLattice ctx.C
  prim0_1 : ∀ v ∈ lat0_1.carrier, ∀ w ∈ lat0_1.carrier,
    ctx.C.isInO (ctx.form v w)
  prim0_2 : ∀ v ∈ lat0_2.carrier, ∀ w ∈ lat0_2.carrier,
    ctx.C.isInO (ctx.form v w)
  contain_01 : ∀ (i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ ctx.wittIndex),
    latticeContained ctx.C lat0_1 (chain i h1 h2)
  lat0_distinct : lat0_1.carrier ≠ lat0_2.carrier


/-- A maximal simplex (chamber) of the alternating-form building: an
$(n+1)$-tuple of $\mathfrak{o}$-lattices with $\Lambda_0$ primitive (form
integral) and each $\Lambda_i$ contained in $\Lambda_0$ but with prescribed
scaling and isotropy properties. -/
structure MaxSimplexAlternating (ctx : AlternatingBuildingContext) where
  lats : Fin (ctx.wittIndex + 1) → OLattice ctx.C
  prim : ∀ v ∈ (lats 0).carrier, ∀ w ∈ (lats 0).carrier,
    ctx.C.isInO (ctx.form v w)
  contain : ∀ i : Fin (ctx.wittIndex + 1), 0 < i.val →
    latticeContained ctx.C (lats 0) (lats i)
  scale_contain : ∀ i : Fin (ctx.wittIndex + 1), 0 < i.val →
    ∀ v ∈ (lats i).carrier, ctx.C.oscal ctx.C.uniformizer v ∈ (lats 0).carrier
  iso : ∀ i : Fin (ctx.wittIndex + 1), 0 < i.val →
    formValuesInMaxIdeal ctx.C ctx.form (lats i)

/-- A maximal simplex in the double oriflamme building, consisting of a pair of
primitive lattices at level $0$, intermediate lattices for $2 \le i \le N-2$,
and a pair of top-level lattices. -/
structure MaxSimplexDoubleOriflamme (ctx : DoubleOriflammeContext) where
  lat0_1 : OLattice ctx.C
  lat0_2 : OLattice ctx.C
  lat_mid : ∀ (i : ℕ), 2 ≤ i → i ≤ ctx.halfDim - 2 → OLattice ctx.C
  latN_1 : OLattice ctx.C
  latN_2 : OLattice ctx.C
  prim_1 : ∀ v ∈ lat0_1.carrier, ∀ w ∈ lat0_1.carrier,
    ctx.C.isInO (ctx.form v w)
  prim_2 : ∀ v ∈ lat0_2.carrier, ∀ w ∈ lat0_2.carrier,
    ctx.C.isInO (ctx.form v w)

/-- A maximal simplex in the single oriflamme building: a pair of primitive
lattices $\Lambda_0^{(1)}, \Lambda_0^{(2)}$ at level $0$ together with the
remainder of the lattice chain. -/
structure MaxSimplexSingleOriflamme (ctx : SingleOriflammeContext) where
  lat0_1 : OLattice ctx.C
  lat0_2 : OLattice ctx.C
  lat_rest : ∀ (i : ℕ), 2 ≤ i → i ≤ ctx.wittIndex → OLattice ctx.C
  prim_1 : ∀ v ∈ lat0_1.carrier, ∀ w ∈ lat0_1.carrier,
    ctx.C.isInO (ctx.form v w)
  prim_2 : ∀ v ∈ lat0_2.carrier, ∀ w ∈ lat0_2.carrier,
    ctx.C.isInO (ctx.form v w)
