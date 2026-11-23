/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ProjectiveIntersection
import Atlas.AlgebraicGeometryI.code.ProjectiveIntersectionBound
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

noncomputable section
open Ideal

/-- Arithmetic helper in `WithBot ℕ∞`: if `a ≤ d + c` and `d + 1 < a`, then `2 ≤ c`. -/
lemma withbot_enat_le_of_nat_bound {a d : ℕ} {c : WithBot ℕ∞}
    (h : (a : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) + c)
    (hgt : d + 1 < a) :
    (2 : WithBot ℕ∞) ≤ c := by
  by_contra hlt
  push Not at hlt
  have hle : c ≤ 1 := Order.le_of_lt_succ hlt
  have ha : a ≤ d + 1 := by
    exact_mod_cast le_trans h (show (↑d : WithBot ℕ∞) + c ≤ ↑d + 1 by gcongr)
  omega

/-- Codimension bound helper: from `dim X + 1 + (dim Y + 1) ≤ (n+1) + c` and
`n ≤ dim X + dim Y`, deduce `dim X + dim Y − n + 1 ≤ c`. -/
lemma withbot_enat_codim_bound {dimX dimY n : ℕ} {c : WithBot ℕ∞}
    (h : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) + c)
    (hdim_le : n ≤ dimX + dimY) :
    ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) ≤ c := by
  by_contra hlt
  push Not at hlt
  have cast_eq : ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) =
      ((dimX + dimY - n : ℕ) : WithBot ℕ∞) + 1 := by push_cast; ring
  rw [cast_eq] at hlt
  have hle : c ≤ ((dimX + dimY - n : ℕ) : WithBot ℕ∞) :=
    ENat.WithBot.lt_add_one_iff.mp hlt
  have bound : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
      ((n + 1 : ℕ) : WithBot ℕ∞) + ((dimX + dimY - n : ℕ) : WithBot ℕ∞) :=
    le_trans h (by gcongr)
  have : dimX + 1 + (dimY + 1) ≤ n + 1 + (dimX + dimY - n) := by exact_mod_cast bound
  omega

/-- The Krull dimension of the polynomial ring in `n+1` variables over a field equals `n+1`. -/
lemma ringKrullDim_mvPolynomial_fin_succ (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) k) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin,
      ringKrullDim_eq_zero_of_field]
  simp

/-- If the quotient `R / I` has Krull dimension at least 2, then `I` is not the whole ring. -/
lemma ne_top_of_ringKrullDim_quotient_ge_two {R : Type*} [CommRing R] {I : Ideal R}
    (h : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I)) : I ≠ ⊤ := by
  intro htop
  subst htop
  haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hbot : ringKrullDim (R ⧸ (⊤ : Ideal R)) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
  rw [hbot] at h
  exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))

/-- Restatement of Serre's dimension inequality used to derive projective codimension bounds. -/
theorem projective_codim_bound {R : Type*} [CommRing R] [IsLocalRing R]
    [HasSerreDimensionInequality R]
    {𝔭 𝔮 : Ideal R} [𝔭.IsPrime] [𝔮.IsPrime] :
    ringKrullDim (R ⧸ 𝔭) + ringKrullDim (R ⧸ 𝔮) ≤
      ringKrullDim R + ringKrullDim (R ⧸ (𝔭 ⊔ 𝔮)) :=
  HasSerreDimensionInequality.dim_ineq

/-- Theorem 8.2 (intersection dimension): if `dim X + dim Y > n` in `P^n`, then the
intersection of their cones has dimension at least 2 (so the projective varieties meet). -/
theorem projective_intersection_nonempty_of_dim_condition {k : Type*} [Field k]
    (n dimX dimY : ℕ)
    {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    [𝔭.IsPrime] [𝔮.IsPrime]
    (_hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (_hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))

    (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) =
      ((dimX + 1 : ℕ) : WithBot ℕ∞))
    (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) =
      ((dimY + 1 : ℕ) : WithBot ℕ∞))

    (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤
              ringKrullDim (MvPolynomial (Fin (n + 1)) k) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))

    (hdim : n < dimX + dimY) :

    (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by

  rw [hconeX, hconeY, ringKrullDim_mvPolynomial_fin_succ] at hserre

  have hserre' : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
      ((n + 1 : ℕ) : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
    have : ((dimX + 1 : ℕ) : WithBot ℕ∞) + ((dimY + 1 : ℕ) : WithBot ℕ∞) =
           ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) := by push_cast; ring
    rwa [this] at hserre

  exact withbot_enat_le_of_nat_bound hserre' (by omega)

/-- Consequence: under the dimension hypothesis `n < dim X + dim Y`, the sum of the
two projective ideals is proper. -/
theorem projective_intersection_sup_ne_top_of_dim {k : Type*} [Field k]
    (n dimX dimY : ℕ)
    {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    [𝔭.IsPrime] [𝔮.IsPrime]
    (hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) =
      ((dimX + 1 : ℕ) : WithBot ℕ∞))
    (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) =
      ((dimY + 1 : ℕ) : WithBot ℕ∞))
    (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤
              ringKrullDim (MvPolynomial (Fin (n + 1)) k) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
    (hdim : n < dimX + dimY) :
    𝔭 ⊔ 𝔮 ≠ ⊤ :=
  ne_top_of_ringKrullDim_quotient_ge_two
    (projective_intersection_nonempty_of_dim_condition n dimX dimY hp_le hq_le
      hconeX hconeY hserre hdim)

/-- Trivial nonemptiness: two cones in affine space always contain the origin, so their
ideal sum is proper whenever both lie in the irrelevant ideal. -/
theorem cone_intersection_contains_origin {k : Type*} [Field k] {σ : Type*}
    {𝔭 𝔮 : Ideal (MvPolynomial σ k)}
    (hp : 𝔭 ≤ MvPolynomial.variablesIdeal k σ)
    (hq : 𝔮 ≤ MvPolynomial.variablesIdeal k σ) :
    𝔭 ⊔ 𝔮 ≠ ⊤ :=
  MvPolynomial.sup_ne_top_of_le_variablesIdeal hp hq

/-- Codimension bound (Goal 76): under the Serre inequality, the intersection of two
projective varieties in `P^n` of dimensions `dim X`, `dim Y` has dimension at least
`dim X + dim Y − n`. -/
theorem goal76_projective_codim_bound {k : Type*} [Field k]
    (n dimX dimY : ℕ)
    {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    [𝔭.IsPrime] [𝔮.IsPrime]
    (_hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (_hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) =
      ((dimX + 1 : ℕ) : WithBot ℕ∞))
    (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) =
      ((dimY + 1 : ℕ) : WithBot ℕ∞))
    (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤
              ringKrullDim (MvPolynomial (Fin (n + 1)) k) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
    (hdim : n ≤ dimX + dimY) :
    ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
  rw [hconeX, hconeY, ringKrullDim_mvPolynomial_fin_succ] at hserre
  have hserre' : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
      ((n + 1 : ℕ) : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
    have : ((dimX + 1 : ℕ) : WithBot ℕ∞) + ((dimY + 1 : ℕ) : WithBot ℕ∞) =
           ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) := by push_cast; ring
    rwa [this] at hserre
  exact withbot_enat_codim_bound hserre' hdim

/-- Nonemptiness (Goal 76, Thm 8.2): two projective varieties of dimensions `dim X`,
`dim Y` in `P^n` with `dim X + dim Y > n` necessarily intersect. -/
theorem goal76_projective_intersection_nonempty {k : Type*} [Field k]
    (n dimX dimY : ℕ)
    {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    [𝔭.IsPrime] [𝔮.IsPrime]
    (hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) =
      ((dimX + 1 : ℕ) : WithBot ℕ∞))
    (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) =
      ((dimY + 1 : ℕ) : WithBot ℕ∞))
    (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤
              ringKrullDim (MvPolynomial (Fin (n + 1)) k) +
              ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
    (hdim : n < dimX + dimY) :
    𝔭 ⊔ 𝔮 ≠ ⊤ :=
  projective_intersection_sup_ne_top_of_dim n dimX dimY hp_le hq_le
    hconeX hconeY hserre hdim

end
