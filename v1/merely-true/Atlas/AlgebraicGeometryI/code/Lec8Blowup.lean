/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic

open scoped LinearAlgebra.Projectivization

namespace Lec8Blowup

section Definitions

variable (k : Type*) [Field k] (n : ℕ)

/-- The defining equations `x_i y_j = x_j y_i` for the blowup of
affine space at the origin (Lec 8/9, Def 20). -/
def BlowupEquations (x y : Fin n → k) : Prop :=
  ∀ i j : Fin n, x i * y j = x j * y i

/-- The blowup of `𝔸ⁿ` at the origin, as the incidence subset of
`𝔸ⁿ × ℙⁿ⁻¹` consisting of pairs `(x, ℓ)` with `x ∈ ℓ`
(Lec 8/9, Def 20). -/
def BlowupAffineOrigin : Set ((Fin n → k) × ℙ k (Fin n → k)) :=
  {p | (p.1 : Fin n → k) ∈ p.2.submodule}

/-- Projection from the blowup `Bl₀(𝔸ⁿ)` to `𝔸ⁿ` (Lec 8/9, Def 20). -/
def blowupProjection (p : BlowupAffineOrigin k n) : Fin n → k :=
  p.1.1

end Definitions

section EquationsEquiv

variable {k : Type*} [Field k] {n : ℕ}

/-- A point of projective space is the span of its chosen
representative. -/
lemma Projectivization.submodule_eq_span_rep (v : ℙ k (Fin n → k)) :
    v.submodule = k ∙ v.rep := by
  conv_lhs => rw [← Projectivization.mk_rep v]
  exact Projectivization.submodule_mk _ _

/-- For `y ≠ 0`, the blowup equations `x_i y_j = x_j y_i` hold iff
`x` lies on the line through `y` (Lec 8/9, Def 20). -/
lemma blowupEquations_iff_mem_span {x y : Fin n → k} (hy : y ≠ 0) :
    BlowupEquations k n x y ↔ x ∈ Submodule.span k {y} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    have ⟨j, hyj⟩ : ∃ j : Fin n, y j ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hy (funext hall)
    refine ⟨x j * (y j)⁻¹, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have heq := h i j
    calc x j * (y j)⁻¹ * y i = x j * y i * (y j)⁻¹ := by ring
      _ = x i * y j * (y j)⁻¹ := by rw [heq]
      _ = x i := by field_simp
  · rintro ⟨a, rfl⟩ i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- A pair `(x, ℓ)` lies on the blowup iff `x` satisfies the blowup
equations with any chosen representative of `ℓ`. -/
lemma mem_blowupAffineOrigin_iff (k : Type*) [Field k] (n : ℕ)
    (p : (Fin n → k) × ℙ k (Fin n → k)) :
    p ∈ BlowupAffineOrigin k n ↔ BlowupEquations k n p.1 p.2.rep := by
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq,
    Projectivization.submodule_eq_span_rep]
  exact (blowupEquations_iff_mem_span p.2.rep_nonzero).symm

end EquationsEquiv

section Projection

variable {k : Type*} [Field k] {n : ℕ}

/-- A nonzero vector `x` determines the unique line in `ℙⁿ⁻¹`
containing it. -/
lemma proj_unique_of_nonzero {x : Fin n → k} (hx : x ≠ 0)
    (l : ℙ k (Fin n → k)) (hmem : x ∈ l.submodule) :
    l = Projectivization.mk k x hx := by
  rw [Projectivization.submodule_eq_span_rep, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha; exact hx ha.symm
  rw [← Projectivization.mk_rep l, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 a⁻¹ (inv_ne_zero ha_ne), by
    simp only [Units.smul_def, Units.val_mk0]
    rw [← ha, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]⟩

/-- For any line `ℓ`, the point `(0, ℓ)` lies on the blowup (the
exceptional fiber). -/
lemma zero_mem_blowupAffineOrigin (l : ℙ k (Fin n → k)) :
    ((0 : Fin n → k), l) ∈ BlowupAffineOrigin k n := by
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq,
    Projectivization.submodule_eq_span_rep, Submodule.mem_span_singleton]
  exact ⟨0, by simp⟩

/-- For `x ≠ 0`, the pair `(x, [x])` lies on the blowup. -/
lemma nonzero_mem_blowupAffineOrigin {x : Fin n → k} (hx : x ≠ 0) :
    (x, Projectivization.mk k x hx) ∈ BlowupAffineOrigin k n := by
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq, Projectivization.submodule_mk]
  exact Submodule.mem_span_singleton_self x

/-- The fiber of the blowup projection over `0` is canonically the
projective space `ℙⁿ⁻¹` (exceptional divisor). -/
noncomputable def exceptionalFiberEquiv :
    {p : BlowupAffineOrigin k n // blowupProjection k n p = 0} ≃
    ℙ k (Fin n → k) where
  toFun p := p.1.1.2
  invFun l := ⟨⟨((0 : Fin n → k), l), zero_mem_blowupAffineOrigin l⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨x, l⟩, hmem⟩, hproj⟩
    simp only [blowupProjection] at hproj
    subst hproj
    simp
  right_inv := by
    intro l
    simp

/-- Away from the origin, the blowup projection is a bijection between
the open locus of the blowup and the punctured affine space. -/
noncomputable def blowupAwayEquiv :
    {p : BlowupAffineOrigin k n // p.1.1 ≠ 0} ≃
    {x : Fin n → k // x ≠ 0} where
  toFun p := ⟨p.1.1.1, p.2⟩
  invFun x :=
    ⟨⟨(x.1, Projectivization.mk k x.1 x.2), by
      simp only [BlowupAffineOrigin, Set.mem_setOf_eq, Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self x.1⟩, x.2⟩
  left_inv := by
    rintro ⟨⟨⟨x, l⟩, hmem⟩, hne⟩
    simp only [Subtype.mk.injEq]
    change x ≠ 0 at hne
    have hl : l = Projectivization.mk k x hne := proj_unique_of_nonzero hne l hmem
    ext <;> simp [hl]
  right_inv := by
    intro ⟨x, hx⟩
    simp

end Projection

end Lec8Blowup
