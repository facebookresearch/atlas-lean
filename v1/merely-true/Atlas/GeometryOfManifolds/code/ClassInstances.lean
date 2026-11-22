/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.PolynomialDFS
import Atlas.GeometryOfManifolds.code.TrivialDFS
import Atlas.GeometryOfManifolds.code.TwoDimDFS
import Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
import Atlas.GeometryOfManifolds.code.MoserDarboux
import Atlas.GeometryOfManifolds.code.FourManifoldsSW
import Atlas.GeometryOfManifolds.code.ArnoldConjecture
import Atlas.GeometryOfManifolds.code.AdvancedKahler
import Atlas.GeometryOfManifolds.code.HardLefschetz
import Atlas.GeometryOfManifolds.code.PontrjaginObstructions
import Atlas.GeometryOfManifolds.code.HodgeTheory
import Atlas.GeometryOfManifolds.code.ChernClassProperties

set_option autoImplicit false
set_option maxHeartbeats 800000


/-- `HasPositivity` instance on degree-$0$ polynomial forms: a polynomial is positive iff it is a
positive real constant. -/
noncomputable instance polyHasPositivity : HasPositivity (PolyΩ 0) where
  IsPositive := fun (p : Polynomial ℝ) => ∃ r : ℝ, 0 < r ∧ p = Polynomial.C r
  pos_add := by
    intro a b ⟨ra, hra, ha⟩ ⟨rb, hrb, hb⟩
    exact ⟨ra + rb, add_pos hra hrb, by rw [ha, hb, map_add]⟩
  pos_smul_pos := by
    intro s a hs ⟨ra, hra, ha⟩
    exact ⟨s * ra, mul_pos hs hra, by rw [ha, Polynomial.smul_C, smul_eq_mul]⟩
  pos_nonzero := by
    intro a ⟨r, hr, ha⟩
    rw [ha]
    exact Polynomial.C_ne_zero.mpr (ne_of_gt hr)


/-- Model 4-dimensional Euclidean space $\mathbb{R}^4$, used as a charted space target for
4-manifolds. -/
abbrev E4Model := EuclideanSpace ℝ (Fin 4)

/-- Trivial `Has4ManifoldTopology` instance on $\mathbb{R}^4$ with all intersection-form invariants
($b_2$, signature) set to zero and Euler characteristic $2$. -/
noncomputable instance trivialHas4ManifoldTopology : Has4ManifoldTopology E4Model where
  Q := {
    b₂ := 0
    b₂_plus := 0
    b₂_minus := 0
    rank_decomp := rfl
    signature := 0
    signature_eq := by norm_num
    isEven := false
    bilinForm := fun _ _ => 0
  }
  euler := 2
  euler_eq := by norm_num


/-- Trivial symplectic manifold structure on the singleton differential-form scaffolding. -/
noncomputable def trivialSymplecticManifold : SymplecticManifold TrivialΩ TrivialVF where
  ω := PUnit.unit
  closed := Subsingleton.elim _ _
  nondegenerate := by
    intro a b _
    exact Subsingleton.elim a b


/-- Trivial $\mathrm{Spin}^{\mathbb{C}}$ structure on $\mathbb{R}^4$ with spinor bundles
$S^\pm = \mathbb{C}$ and zero curvature data; provides a concrete witness for the abstract API. -/
noncomputable def trivialSpinC : SpinCStructure E4Model PUnit PUnit where
  SectionsPlus := ℂ
  SectionsMinus := ℂ
  instACGPlus := inferInstance
  instModPlus := inferInstance
  instACGMinus := inferInstance
  instModMinus := inferInstance
  nontrivial_plus := inferInstance
  c₁_L := 0
  Q_eval := fun _ => 0
  c₁_pair := fun _ => 0
  metric_pairing := fun _ _ => 0
  γ_plus_to_minus := fun _ _ => 0
  γ_minus_to_plus := fun _ _ => 0
  γ_on_2forms := fun _ x => x
  γ_on_2forms_minus := fun _ _ => 0
  hodge_star := id
  hodge_star_invol := fun _ => rfl
  hodge_clifford_plus := fun _ _ => rfl
  hodge_clifford_minus := by intros; simp
  gamma_anticomm := by intros; simp [mul_zero, zero_smul]
  hermitianInnerPlus := fun z w => (z * starRingEnd ℂ w).re
  normSqPlus := fun z => (z * starRingEnd ℂ z).re
  normSq_nonneg := fun z => by rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]
  normSq_zero_iff := fun z => by
    constructor
    · intro h
      have h1 : (z * starRingEnd ℂ z).re = 0 := h
      rw [Complex.mul_conj] at h1
      have h2 : Complex.normSq z = 0 := by exact_mod_cast h1
      exact Complex.normSq_eq_zero.mp h2
    · intro h
      rw [h]
      simp
  hermitian_norm_compat := fun _ => rfl
  hermitian_smul_left := fun c z w => by
    show ((c • z) * starRingEnd ℂ w).re = c * (z * starRingEnd ℂ w).re
    rw [Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
