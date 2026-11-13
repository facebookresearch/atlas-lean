/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.WeierstrassP
import Atlas.EllipticCurves.code.EllipticFunction

open Complex PeriodPair

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass `℘`-function for a lattice `L` is periodic with respect to `L`: shifting the
input by any lattice element leaves the value unchanged. -/
theorem weierstrassPFun_periodic :
    L.IsLatticePeriodic L.weierstrassPFun := by
  intro ω hω z
  show L.weierstrassP (z + ω) = L.weierstrassP z
  exact L.weierstrassP_add_coe z ⟨ω, hω⟩

/-- The derivative `℘'` of the Weierstrass `℘`-function is also `L`-periodic. -/
theorem derivWeierstrassPFun_periodic :
    L.IsLatticePeriodic L.derivWeierstrassPFun := by
  intro ω hω z
  show L.derivWeierstrassP (z + ω) = L.derivWeierstrassP z
  exact L.derivWeierstrassP_add_coe z ⟨ω, hω⟩

/-- The Weierstrass `℘`-function is an elliptic function: meromorphic on `ℂ` and `L`-periodic. -/
theorem weierstrassPFun_isElliptic :
    L.IsEllipticFunction L.weierstrassPFun where
  meromorphic := L.weierstrassPFun_meromorphic
  periodic := L.weierstrassPFun_periodic

/-- The derivative `℘'` is an elliptic function: meromorphic on `ℂ` and `L`-periodic. -/
theorem derivWeierstrassPFun_isElliptic :
    L.IsEllipticFunction L.derivWeierstrassPFun where
  meromorphic := L.derivWeierstrassPFun_meromorphic
  periodic := L.derivWeierstrassPFun_periodic

/-- The only lattice point inside the fundamental parallelogram of `L` (as a `ZSpan`-style
fundamental domain) is the origin. -/
lemma lattice_mem_fundamentalDomain_eq_zero (z : ℂ)
    (hz_lat : z ∈ L.lattice) (hz_fd : z ∈ ZSpan.fundamentalDomain L.basis) :
    z = 0 := by
  have h1 : ZSpan.fract L.basis z = z := ZSpan.fract_eq_self.mpr hz_fd
  have h2 : ZSpan.fract L.basis (z + 0) = ZSpan.fract L.basis 0 := by
    rw [L.lattice_eq_span_range_basis] at hz_lat
    exact ZSpan.fract_zSpan_add L.basis 0 hz_lat
  simp only [add_zero] at h2
  rw [← h1, h2]
  simp [ZSpan.fract]

/-- The Weierstrass `℘`-function has a pole of multiplicity exactly `2` at the origin. -/
lemma poleMultiplicity_weierstrassP_zero :
    poleMultiplicity L.weierstrassPFun 0 = 2 := by
  unfold poleMultiplicity
  rw [show meromorphicOrderAt L.weierstrassPFun 0 = ((-2 : ℤ) : WithTop ℤ) from
    L.weierstrassPFun_order 0 L.lattice.zero_mem]
  decide

/-- The derivative `℘'` has a pole of multiplicity exactly `3` at the origin. -/
lemma poleMultiplicity_derivWeierstrassP_zero :
    poleMultiplicity L.derivWeierstrassPFun 0 = 3 := by
  unfold poleMultiplicity
  rw [show meromorphicOrderAt L.derivWeierstrassPFun 0 = ((-3 : ℤ) : WithTop ℤ) from
    L.derivWeierstrassPFun_order 0 L.lattice.zero_mem]
  decide

/-- The set of poles of the Weierstrass `℘`-function inside the fundamental parallelogram (anchored
at `0`) consists of just the origin. -/
lemma polesInFundParallelogram_weierstrassP_eq :
    L.polesInFundParallelogram L.weierstrassPFun 0 = {0} := by
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ L.weierstrassPFun z :=
      L.weierstrassPFun_analyticOnNhd z hz_not_lattice
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    show meromorphicOrderAt L.weierstrassPFun 0 < 0
    rw [L.weierstrassPFun_order 0 L.lattice.zero_mem]
    show ((-2 : ℤ) : WithTop ℤ) < (0 : ℤ)
    exact_mod_cast (show (-2 : ℤ) < 0 from by norm_num)

/-- The set of poles of `℘'` inside the fundamental parallelogram (anchored at `0`) consists of
just the origin. -/
lemma polesInFundParallelogram_derivWeierstrassP_eq :
    L.polesInFundParallelogram L.derivWeierstrassPFun 0 = {0} := by
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ L.derivWeierstrassPFun z :=
      L.derivWeierstrassPFun_analyticOnNhd z hz_not_lattice
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    show meromorphicOrderAt L.derivWeierstrassPFun 0 < 0
    rw [L.derivWeierstrassPFun_order 0 L.lattice.zero_mem]
    show ((-3 : ℤ) : WithTop ℤ) < (0 : ℤ)
    exact_mod_cast (show (-3 : ℤ) < 0 from by norm_num)

/-- The Weierstrass `℘`-function has elliptic order `2`: the sum of pole multiplicities in a
fundamental parallelogram equals `2`. -/
theorem weierstrassPFun_ellipticOrder :
    ellipticOrder L L.weierstrassPFun L.weierstrassPFun_isElliptic = 2 := by
  unfold ellipticOrder
  have h_eq := L.polesInFundParallelogram_weierstrassP_eq
  have h_fin : (polesInFundParallelogram_finite L.weierstrassPFun_isElliptic 0).toFinset =
      {(0 : ℂ)} := by
    ext x; simp [h_eq]
  rw [h_fin]
  simp [L.poleMultiplicity_weierstrassP_zero]

/-- For any constant `c`, the shifted function `z ↦ ℘(z) - c` is also an elliptic function. -/
theorem weierstrassPFun_sub_const_isElliptic (c : ℂ) :
    L.IsEllipticFunction (fun z => L.weierstrassPFun z - c) where
  meromorphic := L.weierstrassPFun_meromorphic.sub (Meromorphic.const c)
  periodic := by
    intro ω hω z
    simp only
    rw [L.weierstrassPFun_periodic ω hω z]

/-- Subtracting a constant from `℘` does not change its order at the origin: `z ↦ ℘(z) - c` still
has meromorphic order `-2` at `0`. -/
lemma weierstrassPFun_sub_const_order_zero (c : ℂ) :
    meromorphicOrderAt (fun z => L.weierstrassPFun z - c) 0 = ((-2 : ℤ) : WithTop ℤ) := by
  have h_wp := L.weierstrassPFun_order 0 L.lattice.zero_mem


  have : (fun z => L.weierstrassPFun z - c) = L.weierstrassPFun + (fun _ => -c) := by

    ext z; simp [Pi.add_apply, sub_eq_add_neg]
  rw [this, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) 0)]
  · exact h_wp
  · rw [h_wp, meromorphicOrderAt_const]
    split_ifs
    · exact WithTop.coe_lt_top _
    · exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0)

/-- For any constant `c`, the function `z ↦ ℘(z) - c` has a pole of multiplicity `2` at the
origin. -/
lemma poleMultiplicity_weierstrassP_sub_const_zero (c : ℂ) :
    poleMultiplicity (fun z => L.weierstrassPFun z - c) 0 = 2 := by
  unfold poleMultiplicity
  rw [L.weierstrassPFun_sub_const_order_zero c]
  decide

/-- The poles of `z ↦ ℘(z) - c` in the fundamental parallelogram (anchored at `0`) are exactly the
origin, just as for `℘` itself. -/
lemma polesInFundParallelogram_weierstrassP_sub_const_eq (c : ℂ) :
    L.polesInFundParallelogram (fun z => L.weierstrassPFun z - c) 0 = {0} := by
  ext z
  simp only [polesInFundParallelogram, fundamentalParallelogram_zero,
    Set.mem_sep_iff, Set.mem_singleton_iff, IsPoleAt]
  constructor
  · intro ⟨hz_mem, hz_pole⟩
    by_contra hz_ne
    have hz_not_lattice : z ∉ (L.lattice : Set ℂ) := by
      intro hz_lat
      exact hz_ne (L.lattice_mem_fundamentalDomain_eq_zero z hz_lat hz_mem)
    have h_analytic : AnalyticAt ℂ (fun z => L.weierstrassPFun z - c) z :=
      (L.weierstrassPFun_analyticOnNhd z hz_not_lattice).sub analyticAt_const
    exact not_lt.mpr h_analytic.meromorphicOrderAt_nonneg hz_pole
  · intro hz_eq
    subst hz_eq
    refine ⟨by rw [ZSpan.mem_fundamentalDomain]; intro i; simp [Set.mem_Ico], ?_⟩
    rw [L.weierstrassPFun_sub_const_order_zero c]
    exact_mod_cast (show (-2 : ℤ) < 0 from by norm_num)

/-- The elliptic order of `z ↦ ℘(z) - c` is `2` for any constant `c`: as a corollary, every value
of `℘` is attained exactly twice (with multiplicity) in each fundamental parallelogram. -/
theorem weierstrassPFun_sub_const_ellipticOrder (c : ℂ) :
    ellipticOrder L (fun z => L.weierstrassPFun z - c)
      (L.weierstrassPFun_sub_const_isElliptic c) = 2 := by
  unfold ellipticOrder
  have h_eq := L.polesInFundParallelogram_weierstrassP_sub_const_eq c
  have h_fin : (polesInFundParallelogram_finite
      (L.weierstrassPFun_sub_const_isElliptic c) 0).toFinset = {(0 : ℂ)} := by
    ext x; simp [h_eq]
  rw [h_fin]
  simp [L.poleMultiplicity_weierstrassP_sub_const_zero c]

end ComplexLattice

end
