/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-- In a Bezout domain, an irreducible element either divides any given element or is
coprime to it. -/
theorem irreducible_dvd_or_coprime {R : Type*} [CommRing R] [IsBezout R]
    {Q : R} (hQ : Irreducible Q) (P : R) :
    Q ∣ P ∨ IsCoprime Q P :=
  (hQ.isCoprime_or_dvd P).symm.imp_left id

/-- If an irreducible element is not coprime to P in a Bezout domain, then it divides P. -/
theorem irreducible_dvd_of_not_coprime {R : Type*} [CommRing R] [IsBezout R]
    {Q P : R} (hQ : Irreducible Q) (h : ¬IsCoprime Q P) :
    Q ∣ P :=
  hQ.dvd_iff_not_isCoprime.mpr h

/-- In a Bezout domain, divisibility by an irreducible is equivalent to non-coprimality. -/
theorem irreducible_dvd_iff_not_coprime {R : Type*} [CommRing R] [IsBezout R]
    {Q P : R} (hQ : Irreducible Q) :
    Q ∣ P ↔ ¬IsCoprime Q P :=
  hQ.dvd_iff_not_isCoprime

/-- In a Bezout domain, an irreducible dividing a product divides one of the factors. -/
theorem irreducible_dvd_mul {R : Type*} [CommRing R] [IsBezout R]
    {Q a b : R} (hQ : Irreducible Q) (h : Q ∣ a * b) :
    Q ∣ a ∨ Q ∣ b := by
  by_contra hc
  push Not at hc
  have hca : IsCoprime Q a := hQ.coprime_iff_not_dvd.mpr hc.1
  exact hc.2 (hca.dvd_of_dvd_mul_left h)

open Polynomial in
/-- Degree bound: a triple product of polynomials of degree ≤ 1 has degree ≤ 3. -/
lemma natDegree_mul_three_linear_le {R : Type*} [CommRing R]
    {L₁ L₃ L₅ : Polynomial R}
    (h₁ : L₁.natDegree ≤ 1) (h₃ : L₃.natDegree ≤ 1) (h₅ : L₅.natDegree ≤ 1) :
    (L₁ * L₃ * L₅).natDegree ≤ 3 :=
  calc (L₁ * L₃ * L₅).natDegree
      ≤ (L₁ * L₃).natDegree + L₅.natDegree := Polynomial.natDegree_mul_le
    _ ≤ (L₁.natDegree + L₃.natDegree) + L₅.natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ ≤ 3 := by omega

open Polynomial in
/-- Pascal's theorem (Theorem 5.3, Lecture 5), Bezout step: if an irreducible conic Q
shares a point with two cubics F and G (so Q is not coprime to F - G), then Q divides
F - G. -/
theorem pascal_theorem {k : Type*} [Field k] (Q : Polynomial k)
    (hQ : Irreducible Q) (_hd : Q.natDegree = 2)
    (F G : Polynomial k)
    (_hF : F.natDegree ≤ 3) (_hG : G.natDegree ≤ 3)
    (h_not_coprime : ¬ IsCoprime Q (F - G)) :
    Q ∣ (F - G) :=
  (irreducible_dvd_or_coprime hQ (F - G)).resolve_right h_not_coprime

open Polynomial in
/-- After dividing F - G by the conic Q, the quotient is a polynomial of degree ≤ 1:
the Pascal line on which the three intersection points lie. -/
theorem pascal_collinearity {k : Type*} [Field k]
    {Q F G : Polynomial k}
    (hQm : Q.Monic) (hQd : Q.natDegree = 2)
    (hF : F.natDegree ≤ 3) (hG : G.natDegree ≤ 3)
    (_hdvd : Q ∣ (F - G)) :
    ((F - G) /ₘ Q).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_divByMonic _ hQm, hQd]
  have h1 : (F - G).natDegree ≤ 3 :=
    (Polynomial.natDegree_sub_le F G).trans (max_le hF hG)
  omega

open Polynomial in
/-- Full Pascal statement for hexagons: with six lines L_1,...,L_6 forming an inscribed
hexagon in the conic Q, the difference of the two cubic products is divisible by Q and
the resulting quotient is the Pascal line. -/
theorem pascal_full {k : Type*} [Field k] (Q : Polynomial k)
    (hQ : Irreducible Q) (hQm : Q.Monic) (hQd : Q.natDegree = 2)
    {L₁ L₂ L₃ L₄ L₅ L₆ : Polynomial k}
    (hL₁ : L₁.natDegree ≤ 1) (hL₂ : L₂.natDegree ≤ 1)
    (hL₃ : L₃.natDegree ≤ 1) (hL₄ : L₄.natDegree ≤ 1)
    (hL₅ : L₅.natDegree ≤ 1) (hL₆ : L₆.natDegree ≤ 1)
    (h_not_coprime : ¬ IsCoprime Q (L₁ * L₃ * L₅ - L₂ * L₄ * L₆)) :
    Q ∣ (L₁ * L₃ * L₅ - L₂ * L₄ * L₆) ∧
    ((L₁ * L₃ * L₅ - L₂ * L₄ * L₆) /ₘ Q).natDegree ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact (irreducible_dvd_or_coprime hQ _).resolve_right h_not_coprime
  · rw [Polynomial.natDegree_divByMonic _ hQm, hQd]
    have hFG : (L₁ * L₃ * L₅ - L₂ * L₄ * L₆).natDegree ≤ 3 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le (natDegree_mul_three_linear_le hL₁ hL₃ hL₅)
                (natDegree_mul_three_linear_le hL₂ hL₄ hL₆))
    omega

/-- If a ring has Krull dimension exactly 1, it satisfies `KrullDimLE 1`. -/
theorem krullDimLE_one_of_ringKrullDim_eq_one {A : Type*} [CommRing A]
    (hdim : ringKrullDim A = 1) : Ring.KrullDimLE 1 A := by
  constructor
  simp only [ringKrullDim] at hdim
  exact hdim ▸ le_refl _

/-- In a 1-dimensional domain, every nonzero prime ideal is maximal. -/
theorem dim_one_prime_is_maximal {A : Type*} [CommRing A] [IsDomain A]
    (hdim : ringKrullDim A = 1)
    {p : Ideal A} (hp : p.IsPrime) (hne : p ≠ ⊥) :
    p.IsMaximal :=
  Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
    (krullDimLE_one_of_ringKrullDim_eq_one hdim) p hne hp

/-- A proper nonzero closed subset of a Noetherian 1-dimensional affine curve is
finite (a finite set of points). -/
theorem dim_one_proper_closed_finite {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 1)
    (I : Ideal A) (hI : I ≠ ⊥) (_hI' : I ≠ ⊤) :
    Set.Finite {p : Ideal A | p.IsPrime ∧ I ≤ p} := by

  have hsub : {p : Ideal A | p.IsPrime ∧ I ≤ p} ⊆ I.minimalPrimes := by
    intro p ⟨hp, hIp⟩
    refine ⟨⟨hp, hIp⟩, fun q ⟨hq, hIq⟩ hqp => ?_⟩


    have hqne : q ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIq))

    exact (dim_one_prime_is_maximal hdim hq hqne).eq_of_le hp.ne_top hqp |>.ge

  exact (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).subset hsub

/-- Equivalence between cofinite topologies induced by an underlying type equivalence. -/
noncomputable def cofiniteEquiv (X Y : Type*) (e : X ≃ Y) :
    CofiniteTopology X ≃ CofiniteTopology Y :=
  (CofiniteTopology.of (X := X)).symm.trans (e.trans (CofiniteTopology.of (X := Y)))

/-- The cofinite equivalence map is continuous in the cofinite topologies. -/
lemma cofinite_continuous_of_equiv (X Y : Type*) (e : X ≃ Y) :
    Continuous (cofiniteEquiv X Y e) := by
  rw [continuous_def]
  intro s hs
  rw [CofiniteTopology.isOpen_iff'] at hs ⊢
  rcases hs with rfl | hfin
  · simp [Set.preimage_empty]
  · right
    rw [← Set.preimage_compl]
    exact Set.Finite.preimage ((cofiniteEquiv X Y e).injective.injOn) hfin

/-- A type equivalence promotes to a homeomorphism between cofinite topologies. -/
noncomputable def cofiniteHomeomorph (X Y : Type*) (e : X ≃ Y) :
    CofiniteTopology X ≃ₜ CofiniteTopology Y where
  toEquiv := cofiniteEquiv X Y e
  continuous_toFun := cofinite_continuous_of_equiv X Y e
  continuous_invFun := by
    show Continuous (cofiniteEquiv X Y e).invFun
    have : (cofiniteEquiv X Y e).invFun = (cofiniteEquiv Y X e.symm).toFun := by
      ext x; simp [cofiniteEquiv, CofiniteTopology.of]
    rw [this]
    exact cofinite_continuous_of_equiv Y X e.symm

