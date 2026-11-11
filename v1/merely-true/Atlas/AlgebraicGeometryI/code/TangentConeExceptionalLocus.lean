/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Ring

set_option synthInstance.maxHeartbeats 40000

noncomputable section

open Polynomial

namespace TangentCone

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- The `n`-th graded piece `I^n / I^{n+1}` of the associated graded ring of
`R` with respect to the ideal `I`. -/
def AssocGradedPiece (n : ℕ) : Type _ :=
  (I ^ n : Submodule R R) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1) : Submodule R R)

/-- Additive group structure on the associated graded piece `I^n / I^{n+1}`. -/
instance AssocGradedPiece.instAddCommGroup (n : ℕ) : AddCommGroup (AssocGradedPiece R I n) :=
  inferInstanceAs (AddCommGroup ((I ^ n : Submodule R R) ⧸ _))

/-- `R`-module structure on the associated graded piece `I^n / I^{n+1}`. -/
instance AssocGradedPiece.instModule (n : ℕ) : Module R (AssocGradedPiece R I n) :=
  inferInstanceAs (Module R ((I ^ n : Submodule R R) ⧸ _))

/-- The canonical projection `I^n → I^n / I^{n+1}` onto the `n`-th associated
graded piece. -/
def assocGradedProj (n : ℕ) : (I ^ n : Submodule R R) →ₗ[R] AssocGradedPiece R I n :=
  (Submodule.comap (I ^ n).subtype (I ^ (n + 1) : Submodule R R)).mkQ


/-- The associated graded ring `gr_I(R) = ⊕_n I^n / I^{n+1}`. -/
def AssocGraded := DirectSum ℕ (AssocGradedPiece R I)


/-- The augmentation ideal inside the Rees algebra of `I`, consisting of those
polynomials `f` whose coefficient in degree `n` lies in `I^{n+1}`. -/
def reesAugmentationIdeal : Ideal (reesAlgebra I) where
  carrier := { f | ∀ n, (f : R[X]).coeff n ∈ I ^ (n + 1) }
  add_mem' ha hb n := by
    simp only [Subalgebra.coe_add, coeff_add]; exact Ideal.add_mem _ (ha n) (hb n)
  zero_mem' n := by
    simp only [ZeroMemClass.coe_zero, coeff_zero]; exact (I ^ (n + 1)).zero_mem
  smul_mem' c f hf n := by
    show ((c * f : reesAlgebra I) : R[X]).coeff n ∈ I ^ (n + 1)
    simp only [Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨i, j⟩ hij
    have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
    rw [← hij', show i + j + 1 = i + (j + 1) from by ring, pow_add]
    exact Ideal.mul_mem_mul (c.2 i) (hf j)

/-- The map sending an element of the Rees algebra to its `n`-th graded
component in the associated graded ring, by taking the coefficient at `n`. -/
def reesToAssocGradedComponent (n : ℕ) (f : reesAlgebra I) :
    AssocGradedPiece R I n :=
  assocGradedProj R I n ⟨(f : Polynomial R).coeff n, f.2 n⟩

/-- A monomial `a · X^n` with `a ∈ I^n` belongs to the Rees algebra of `I`. -/
lemma monomial_mem_reesAlgebra (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    Polynomial.monomial n a ∈ reesAlgebra I := by
  intro i
  simp only [Polynomial.coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (I ^ i).zero_mem

/-- The map from the Rees algebra to the `n`-th associated graded piece is
surjective, witnessed by the monomial `a · X^n`. -/
theorem reesToAssocGraded_surjective (n : ℕ) :
    Function.Surjective (reesToAssocGradedComponent R I n) := by
  intro x
  obtain ⟨⟨a, ha⟩, hx⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨⟨Polynomial.monomial n a, monomial_mem_reesAlgebra R I n a ha⟩, ?_⟩
  simp only [reesToAssocGradedComponent, assocGradedProj, Polynomial.coeff_monomial]
  exact hx

/-- The `n`-th graded component of an element `f` of the Rees algebra vanishes
in `I^n / I^{n+1}` iff its coefficient at `n` lies in `I^{n+1}`. -/
theorem reesToAssocGraded_eq_zero_iff (n : ℕ) (f : reesAlgebra I) :
    reesToAssocGradedComponent R I n f = 0 ↔
      (f : Polynomial R).coeff n ∈ (I ^ (n + 1) : Ideal R) := by
  unfold reesToAssocGradedComponent assocGradedProj
  constructor
  · intro h
    have hmem : (⟨(↑f : Polynomial R).coeff n, f.2 n⟩ : ↥(I ^ n : Submodule R R)) ∈
        Submodule.comap (I ^ n).subtype (I ^ (n + 1) : Submodule R R) :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact hmem
  · exact fun h => (Submodule.Quotient.mk_eq_zero _).mpr h

/-- An element `f` of the Rees algebra lies in the augmentation ideal iff all
of its graded components in the associated graded ring vanish. -/
theorem mem_reesAugmentationIdeal_iff (f : reesAlgebra I) :
    f ∈ reesAugmentationIdeal R I ↔
      ∀ n, reesToAssocGradedComponent R I n f = 0 := by
  constructor
  · intro hf n; exact (reesToAssocGraded_eq_zero_iff R I n f).mpr (hf n)
  · intro hf n; exact (reesToAssocGraded_eq_zero_iff R I n f).mp (hf n)


end TangentCone
