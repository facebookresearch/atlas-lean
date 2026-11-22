/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Order
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Constructions

set_option maxHeartbeats 800000

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace Formalization

/-- Projective `n`-space over `k`, identified with the projectivization of `k^{n+1}`. -/
abbrev ProjectiveSpace (k : Type*) [Field k] (n : ℕ) :=
  Projectivization k (Fin (n + 1) → k)

/-- The punctured affine space `A^{n+1} \ {0}` over `k`, used as the domain of the quotient map
defining `P^n`. -/
abbrev PuncturedAffineSpace (k : Type*) [Field k] (n : ℕ) :=
  { v : Fin (n + 1) → k // v ≠ 0 }

/-- The quotient map `A^{n+1} \ {0} → P^n` sending a nonzero vector to its projective class
(Lecture 2, Definition 4). -/
def ProjectiveSpace.π (k : Type*) [Field k] (n : ℕ) :
    PuncturedAffineSpace k n → ProjectiveSpace k n :=
  Projectivization.mk' k

variable {k : Type*} [Field k] {n : ℕ}

/-- Two nonzero vectors define the same point of `P^n` iff they differ by a nonzero scalar. -/
theorem ProjectiveSpace.π_eq_iff (v w : PuncturedAffineSpace k n) :
    ProjectiveSpace.π k n v = ProjectiveSpace.π k n w ↔
    ∃ (a : kˣ), a • (w : Fin (n + 1) → k) = (v : Fin (n + 1) → k) := by
  simp only [ProjectiveSpace.π, Projectivization.mk'_eq_mk]
  exact Projectivization.mk_eq_mk_iff k _ _ v.2 w.2

/-- The quotient map `A^{n+1} \ {0} → P^n` is surjective. -/
theorem ProjectiveSpace.π_surjective : Function.Surjective (ProjectiveSpace.π k n) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

section Topology

open MvPolynomial Set

variable (k : Type*) [Field k] (n : ℕ)

/-- The vanishing locus in `A^{n+1}` of a set of polynomials: points where every polynomial in
`S` evaluates to zero. -/
def AffineSpace.zeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (Fin (n + 1) → k) :=
  { x | ∀ p ∈ S, MvPolynomial.eval x p = 0 }

/-- The set of all products `f * g` with `f ∈ S` and `g ∈ T`, used in showing the union of two
zero loci is itself a zero locus. -/
def AffineSpace.mulPairs (S T : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (MvPolynomial (Fin (n + 1)) k) :=
  { p | ∃ f ∈ S, ∃ g ∈ T, f * g = p }

/-- The Zariski topology on `A^{n+1}`, whose closed sets are the vanishing loci of sets of
polynomials. -/
instance zariskiTopologyAffine : TopologicalSpace (Fin (n + 1) → k) :=
  TopologicalSpace.ofClosed (Set.range (AffineSpace.zeroLocus k n))
    (⟨{1}, by ext x; simp [AffineSpace.zeroLocus]⟩)
    (by
      intro Zs hZs
      have hc : ∀ Z ∈ Zs, ∃ S, AffineSpace.zeroLocus k n S = Z :=
        fun Z hZ => let ⟨S, hS⟩ := hZs hZ; ⟨S, hS⟩
      classical
      choose S hS using hc
      use { p | ∃ Z, ∃ hZ : Z ∈ Zs, p ∈ S Z hZ }
      ext x
      constructor
      · intro hx
        apply mem_sInter.mpr
        intro Z hZ
        rw [← hS Z hZ]
        intro p hp
        exact hx p ⟨Z, hZ, hp⟩
      · intro hx p ⟨Z, hZ, hp⟩
        have hxZ := mem_sInter.mp hx Z hZ
        rw [← hS Z hZ] at hxZ
        exact hxZ p hp)
    (by
      rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
      refine ⟨AffineSpace.mulPairs k n S T, ?_⟩
      ext x
      simp only [AffineSpace.zeroLocus, AffineSpace.mulPairs, mem_setOf_eq, mem_union]
      constructor
      · intro hx
        by_contra hc
        push Not at hc
        obtain ⟨⟨f, hfS, hf⟩, ⟨g, hgT, hg⟩⟩ := hc
        exact absurd (show MvPolynomial.eval x (f * g) = 0 from hx _ ⟨f, hfS, g, hgT, rfl⟩)
          (by simp only [map_mul]; exact mul_ne_zero hf hg)
      · rintro (hS | hT) p ⟨f, hfS, g, hgT, rfl⟩
        · simp [map_mul, hS f hfS]
        · simp [map_mul, hT g hgT])

/-- The Zariski topology on `P^n`, defined as the quotient topology coinduced from the
Zariski topology on `A^{n+1}` via the projection `π`. -/
instance projectiveSpaceTopology : TopologicalSpace (ProjectiveSpace k n) :=
  TopologicalSpace.coinduced (Projectivization.mk' k) inferInstance

/-- A function `f : U → k` on an open subset `U ⊆ P^n` is *regular* (Lecture 2, Def 4) if locally
on the affine cone it can be written as a ratio `p/q` of polynomials with `q` non-vanishing. -/
def ProjectiveSpace.IsRegular
    (U : Set (ProjectiveSpace k n)) (f : ↥U → k) : Prop :=
  ∀ (v : PuncturedAffineSpace k n) (_ : ProjectiveSpace.π k n v ∈ U),
    ∃ (p q : MvPolynomial (Fin (n + 1)) k),
      ∃ V : Set (Fin (n + 1) → k),
        @IsOpen _ (zariskiTopologyAffine k n) V ∧
        (v : Fin (n + 1) → k) ∈ V ∧
        ∀ w ∈ V, (hw : w ≠ 0) →
          ∀ (hmem : ProjectiveSpace.π k n ⟨w, hw⟩ ∈ U),
            MvPolynomial.eval w q ≠ 0 ∧
            f ⟨ProjectiveSpace.π k n ⟨w, hw⟩, hmem⟩ =
              MvPolynomial.eval w p / MvPolynomial.eval w q

end Topology

end Formalization

end
