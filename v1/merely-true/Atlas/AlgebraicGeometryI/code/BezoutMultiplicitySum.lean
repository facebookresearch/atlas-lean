/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.BezoutLight
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The projective intersection number of two homogeneous polynomials `f, g` in three variables,
defined as the `k`-dimension of the degree-`n` piece of `k[x,y,z] / (⟨f⟩ + ⟨g⟩)`. -/
noncomputable def projectiveIntersectionNumber
    (f g : MvPolynomial (Fin 3) k) (n : ℕ) : ℕ :=
  Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n)

/-- Equal ideals give equal homogeneous quotient piece dimensions. -/
lemma homogQuotPiece_ideal_eq {I J : Ideal (MvPolynomial (Fin 3) k)} (h : I = J) (n : ℕ) :
    Module.finrank k (homogQuotPiece k I n) = Module.finrank k (homogQuotPiece k J n) := by
  subst h; rfl


/-- Symmetry of the projective intersection number in its two homogeneous arguments. -/
theorem projectiveIntersectionNumber_comm
    (f g : MvPolynomial (Fin 3) k) (n : ℕ) :
    projectiveIntersectionNumber k f g n =
    projectiveIntersectionNumber k g f n := by
  unfold projectiveIntersectionNumber
  have h : Ideal.span {f} ⊔ Ideal.span {g} = Ideal.span {g} ⊔ Ideal.span {f} := by
    rw [sup_comm]
  exact homogQuotPiece_ideal_eq k h n





/-- A point of intersection of the projective varieties `V(f)` and `V(g)`, encoded as a prime
ideal of `k[x, y, z]` containing both `f` and `g`. -/
structure ProjectivePoint (k : Type*) [Field k]
    (f g : MvPolynomial (Fin 3) k) where
  P : Ideal (MvPolynomial (Fin 3) k)
  hP_prime : P.IsPrime
  hf_mem : f ∈ P
  hg_mem : g ∈ P

/-- Local intersection multiplicity at a projective intersection point `p` of `f` and `g`,
defined as the `k`-dimension of the localisation of `k[x, y, z] / (⟨f⟩ + ⟨g⟩)` at the image
of `p`. -/
noncomputable def projLocalIntersectionMultiplicity
    (f g : MvPolynomial (Fin 3) k)
    (p : ProjectivePoint k f g) : ℕ := by
  let I := Ideal.span {f} ⊔ Ideal.span {g}
  let Q := p.P.map (Ideal.Quotient.mk I)
  have hI_le_P : I ≤ p.P := by
    apply sup_le
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hf_mem)
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hg_mem)
  have hQ_prime : Q.IsPrime := by
    haveI := p.hP_prime
    apply Ideal.map_isPrime_of_surjective
    · exact Ideal.Quotient.mk_surjective
    · intro x hx
      rw [Ideal.mk_ker] at hx
      exact hI_le_P hx
  exact @Module.finrank k (@Localization.AtPrime _ _ Q hQ_prime) _ _ _




end
