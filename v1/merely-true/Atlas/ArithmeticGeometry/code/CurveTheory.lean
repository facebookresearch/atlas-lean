/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.MorphismsCurves
import Atlas.ArithmeticGeometry.code.RegularLocalRings

noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

lemma dvr_isInteger_or_isInteger (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  haveI : ValuationRing R := of_isDiscreteValuationRing R
  exact ValuationRing.isInteger_or_isInteger R x

theorem dvr_exists_normalizer {n : ℕ} (f : Fin (n + 1) → K) (hne : ∃ i, f i ≠ 0) :
    ∃ j, f j ≠ 0 ∧ (∀ i, IsLocalization.IsInteger R (f i * (f j)⁻¹)) := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := hne
    refine ⟨i, hi, fun j => ?_⟩
    have : j = i := Fin.ext (by omega)
    subst this; rw [mul_inv_cancel₀ hi]; exact ⟨1, map_one _⟩
  | succ n ih =>
    by_cases hlast : f (Fin.last (n + 1)) = 0
    ·
      have hne' : ∃ i : Fin (n + 1), (f ∘ Fin.castSucc) i ≠ 0 := by
        obtain ⟨i, hi⟩ := hne
        have hil : i ≠ Fin.last (n + 1) := fun h => hi (h ▸ hlast)
        exact ⟨i.castPred hil, by simp [Function.comp, Fin.castSucc_castPred i hil]; exact hi⟩
      obtain ⟨j, hj_ne, hj_int⟩ := ih (f ∘ Fin.castSucc) hne'
      simp only [Function.comp_apply] at hj_ne hj_int
      refine ⟨Fin.castSucc j, hj_ne, fun i => ?_⟩
      by_cases hi : i = Fin.last (n + 1)
      · rw [hi, hlast, zero_mul]; exact ⟨0, map_zero _⟩
      · rw [(Fin.castSucc_castPred i hi).symm]; exact hj_int _
    ·
      by_cases hne' : ∃ i : Fin (n + 1), (f ∘ Fin.castSucc) i ≠ 0
      · obtain ⟨j, hj_ne, hj_int⟩ := ih (f ∘ Fin.castSucc) hne'
        simp only [Function.comp_apply] at hj_ne hj_int

        rcases dvr_isInteger_or_isInteger (R := R)
          (f (Fin.last (n + 1)) * (f (Fin.castSucc j))⁻¹) with h | h
        ·
          refine ⟨Fin.castSucc j, hj_ne, fun i => ?_⟩
          by_cases hi : i = Fin.last (n + 1)
          · rw [hi]; exact h
          · rw [(Fin.castSucc_castPred i hi).symm]; exact hj_int _
        ·

          rw [mul_inv_rev, inv_inv] at h
          refine ⟨Fin.last (n + 1), hlast, fun i => ?_⟩
          by_cases hi : i = Fin.last (n + 1)
          · rw [hi, mul_inv_cancel₀ hlast]; exact ⟨1, map_one _⟩
          · rw [(Fin.castSucc_castPred i hi).symm]
            have hk := hj_int (i.castPred hi)
            have : f ((i.castPred hi).castSucc) * (f (Fin.last (n + 1)))⁻¹ =
              (f ((i.castPred hi).castSucc) * (f (Fin.castSucc j))⁻¹) *
              (f (Fin.castSucc j) * (f (Fin.last (n + 1)))⁻¹) := by
              rw [mul_assoc, ← mul_assoc (f (Fin.castSucc j))⁻¹,
                  inv_mul_cancel₀ hj_ne, one_mul]
            rw [this]
            exact IsLocalization.isInteger_mul hk h
      ·
        push Not at hne'
        simp only [Function.comp_apply] at hne'
        refine ⟨Fin.last (n + 1), hlast, fun i => ?_⟩
        by_cases hi : i = Fin.last (n + 1)
        · rw [hi, mul_inv_cancel₀ hlast]; exact ⟨1, map_one _⟩
        · rw [(Fin.castSucc_castPred i hi).symm, hne', zero_mul]; exact ⟨0, map_zero _⟩

end DVRNormalization

structure RationalMapToProj (K : Type*) [Field K] (n : ℕ) where
  coords : Fin (n + 1) → K
  coords_ne_zero : ∃ i, coords i ≠ 0

def RationalMapToProj.IsRegularAt {K : Type*} [Field K] {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : Type*) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] : Prop :=
  ∃ j, φ.coords j ≠ 0 ∧
    (∀ i, IsLocalization.IsInteger R (φ.coords i * (φ.coords j)⁻¹))

def RationalMapToProj.ExtendsMorphism {K : Type*} [Field K] {n : ℕ}
    (φ : RationalMapToProj K n)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] : Prop :=
  ∀ p, φ.IsRegularAt (R p)

structure MorphismToProj (K : Type*) [Field K] (n : ℕ)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] where
  toRationalMap : RationalMapToProj K n
  is_morphism : toRationalMap.ExtendsMorphism R

theorem RationalMapToProj.isRegularAt_of_isDVR {K : Type*} [Field K] {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] :
    φ.IsRegularAt R :=
  dvr_exists_normalizer φ.coords φ.coords_ne_zero

theorem SmoothProjectiveCurve.rational_map_is_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    φ.ExtendsMorphism R :=
  fun p => φ.isRegularAt_of_isDVR (R p)

def SmoothProjectiveCurve.rational_map_extends_to_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    MorphismToProj K n R :=
  ⟨φ, SmoothProjectiveCurve.rational_map_is_morphism φ R⟩

structure RationalMapToProjectiveVariety (K : Type*) [Field K] (n : ℕ)
    (V : Set (Fin (n + 1) → K)) extends RationalMapToProj K n

def RationalMapToProjectiveVariety.IsMorphism {K : Type*} [Field K] {n : ℕ}
    {V : Set (Fin (n + 1) → K)}
    (φ : RationalMapToProjectiveVariety K n V)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] : Prop :=
  φ.toRationalMapToProj.ExtendsMorphism R

theorem SmoothProjectiveCurve.rational_map_to_projective_variety_is_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    {V : Set (Fin (n + 1) → K)}
    (φ : RationalMapToProjectiveVariety K n V)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    φ.IsMorphism R :=
  SmoothProjectiveCurve.rational_map_is_morphism φ.toRationalMapToProj R

structure SmoothProjectiveCurveData (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] (n : ℕ) where
  P : Type u
  R : P → Type u
  [instCR : ∀ p, CommRing (R p)]
  [instID : ∀ p, IsDomain (R p)]
  [instDVR : ∀ p, IsDiscreteValuationRing (R p)]
  [instAlg : ∀ p, Algebra (R p) K]
  [instFR : ∀ p, IsFractionRing (R p) K]
  [instAlgKR : ∀ p, Algebra k (R p)]
  [instScalarTower : ∀ p, IsScalarTower k (R p) K]
  emb : Fin (n + 1) → K
  emb_ne_zero : ∃ i, emb i ≠ 0
  n_pos : n ≥ 1
  emb_injective : Function.Injective emb
  point_nonempty : Nonempty P
  localRing_injective : ∀ (p₁ p₂ : P),
    (algebraMap (R p₁) K).range = (algebraMap (R p₂) K).range → p₁ = p₂
  localRing_surjective : ∀ (V : ValuationSubring K)
    [IsDiscreteValuationRing V] [IsFractionRing V K],
    ∃ p, (algebraMap (R p) K).range = V.toSubring

attribute [instance] SmoothProjectiveCurveData.instCR SmoothProjectiveCurveData.instID
  SmoothProjectiveCurveData.instDVR SmoothProjectiveCurveData.instAlg
  SmoothProjectiveCurveData.instFR SmoothProjectiveCurveData.instAlgKR
  SmoothProjectiveCurveData.instScalarTower

def DVRDominates {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (φ_star : K₂ →+* K₁)
    (R₁ : Type*) [CommRing R₁] [IsDomain R₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁]
    (R₂ : Type*) [CommRing R₂] [IsDomain R₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] : Prop :=
  ∀ x : K₂, IsLocalization.IsInteger R₂ x → IsLocalization.IsInteger R₁ (φ_star x)

def IsConstantFieldHom {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂] (φ_star : K₂ →ₐ[k] K₁) : Prop :=
  ∀ x : K₂, φ_star x ∈ Set.range (algebraMap k K₁)

def IsSurjectiveOnPoints {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂]
    (φ_star : K₂ →ₐ[k] K₁)
    {P₁ : Type*} (R₁ : P₁ → Type*)
    [∀ p, CommRing (R₁ p)] [∀ p, IsDomain (R₁ p)] [∀ p, Algebra (R₁ p) K₁]
    [∀ p, IsFractionRing (R₁ p) K₁]
    {P₂ : Type*} (R₂ : P₂ → Type*)
    [∀ p, CommRing (R₂ p)] [∀ p, IsDomain (R₂ p)] [∀ p, Algebra (R₂ p) K₂]
    [∀ p, IsFractionRing (R₂ p) K₂] : Prop :=
  ∀ p₂ : P₂, ∃ p₁ : P₁, DVRDominates φ_star.toRingHom (R₁ p₁) (R₂ p₂)




structure BiratIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

structure CurveIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_regular : ∀ p, forward.IsRegularAt (C₁.R p)
  backward_regular : ∀ p, backward.IsRegularAt (C₂.R p)
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

def SmoothProjectiveCurve.birational_map_is_isomorphism
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} {C₁ : SmoothProjectiveCurveData k K₁ n₁}
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} {C₂ : SmoothProjectiveCurveData k K₂ n₂}
    (Φ : BiratIso C₁ C₂) : CurveIso C₁ C₂ :=
  { σ := Φ.σ
    forward := Φ.forward
    backward := Φ.backward
    forward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₁ _ C₁.P _ Φ.forward C₁.R _ _ _ _ _
    backward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₂ _ C₂.P _ Φ.backward C₂.R _ _ _ _ _
    forward_inverse := Φ.forward_inverse
    backward_inverse := Φ.backward_inverse }

namespace FunctionField_k

variable {k : Type*} [Field k]
variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

lemma Subfield.eq_top_of_finrank_eq_one {F : Type*} [Field F]
    (K : Subfield F) (h : Module.finrank K F = 1) : K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← Module.rank_eq_one_iff_finrank_eq_one] at h
  rw [rank_eq_one_iff] at h
  obtain ⟨v₀, hv₀_ne, hv₀_span⟩ := h
  obtain ⟨r, hr⟩ := hv₀_span x
  obtain ⟨s, hs⟩ := hv₀_span 1
  have hs_ne : (s : ↥K) ≠ 0 := by intro h0; simp [h0] at hs
  have hsv : (↑s : F) * v₀ = 1 := by change _ = _; exact hs
  have hv0_eq : v₀ = (↑s : F)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ hsv).symm
  have hx : x = (↑r : F) * (↑s : F)⁻¹ := by
    change _ = _
    calc x = r • v₀ := hr.symm
      _ = (↑r : F) * v₀ := rfl
      _ = (↑r : F) * (↑s : F)⁻¹ := by rw [hv0_eq]
  rw [hx]
  exact K.mul_mem r.2 (K.inv_mem s.2)

lemma finrank_eq_one_of_subfield_eq_top {F : Type*} [Field F]
    (K : Subfield F) (h : K = ⊤) : Module.finrank K F = 1 := by
  subst h
  have hbij : Function.Bijective (algebraMap (↥(⊤ : Subfield F)) F) := by
    exact ⟨Subtype.val_injective, fun x => ⟨⟨x, Subfield.mem_top x⟩, rfl⟩⟩
  have hle : LinearEquiv (RingHom.id ↥(⊤ : Subfield F)) ↥(⊤ : Subfield F) F :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij
  rw [← hle.finrank_eq]
  exact Module.finrank_self _

theorem Morphism.isIso_iff_degree_eq_one (φ : F₂ →+* F₁) :
    Function.Surjective φ ↔ Morphism.degree φ = 1 := by
  constructor
  ·
    intro hsurj
    unfold Morphism.degree
    have htop : φ.fieldRange = ⊤ := RingHom.fieldRange_eq_top_iff.mpr hsurj
    exact finrank_eq_one_of_subfield_eq_top φ.fieldRange htop
  ·
    intro hdeg
    rw [← RingHom.fieldRange_eq_top_iff]
    exact Subfield.eq_top_of_finrank_eq_one φ.fieldRange hdeg

end FunctionField_k

end ArithmeticGeometry

open Ideal

namespace ArithmeticGeometry


variable {k F : Type*} [Field k] [Field F] [Algebra k F]

def localizationSubalgebraCarrier (S : Subalgebra k F) [IsFractionRing S F]
    (𝔭 : Ideal S) [𝔭.IsPrime] : Set F :=
  {x : F | ∃ (a : S) (b : 𝔭.primeCompl),
    x * algebraMap S F b.1 = algebraMap S F a}

section Lemma18_11_Helpers

theorem dvr_valuation_subring_eq_of_le {K : Type*} [Field K]
    {R₁ R₂ : ValuationSubring K}
    [IsDiscreteValuationRing R₁] [IsDiscreteValuationRing R₂]
    (hle : R₁ ≤ R₂) : R₁ = R₂ := by
  by_contra hne
  have hlt : R₁ < R₂ := lt_of_le_of_ne hle hne
  have h1 : ringKrullDim R₁ = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one R₁ (IsDiscreteValuationRing.not_isField R₁)
  have h2 : ringKrullDim R₂ = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one R₂ (IsDiscreteValuationRing.not_isField R₂)
  have hdim : ringKrullDim R₂ + 1 ≤ ringKrullDim R₁ :=
    ValuationSubring.ringKrullDim_add_one_le_of_lt hlt
  rw [h1, h2] at hdim
  norm_num at hdim

lemma Subalgebra.inv_mem_of_isUnit' {R : Subalgebra k F} {x : F}
    (hx : x ∈ (R : Set F)) (hu : IsUnit (⟨x, hx⟩ : R)) :
    x⁻¹ ∈ (R : Set F) := by
  obtain ⟨u, hu_eq⟩ := hu
  have hub : (u.val : R).val = x := congr_arg Subtype.val hu_eq
  have hmul : x * ((u⁻¹ : Rˣ).val : R).val = 1 := by
    rw [← hub]
    have : ((u : R) * (u⁻¹ : Rˣ).val : R) = 1 := by exact_mod_cast u.mul_inv
    exact_mod_cast congr_arg Subtype.val this
  have hinv : ((u⁻¹ : Rˣ).val : R).val = x⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [← hinv]; exact ((u⁻¹ : Rˣ).val : R).2

lemma localization_subset_of_complement_units
    (S R : Subalgebra k F) [IsFractionRing S F]
    (𝔭 : Ideal S) [𝔭.IsPrime]
    (hSR : S ≤ R)
    (hunit : ∀ (b : 𝔭.primeCompl), IsUnit (⟨algebraMap S F b.1, hSR b.1.2⟩ : R)) :
    localizationSubalgebraCarrier S 𝔭 ⊆ (R : Set F) := by
  intro x ⟨a, b, hab⟩
  have ha_mem : (algebraMap S F a : F) ∈ (R : Set F) := hSR a.2
  have hb_mem : (algebraMap S F b.1 : F) ∈ (R : Set F) := hSR b.1.2
  have hb_unit := hunit b
  have hb_ne : algebraMap S F b.1 ≠ 0 := by
    intro h0
    have hinj := IsFractionRing.injective S F
    have := hinj (by rw [h0, map_zero] : algebraMap S F b.1 = algebraMap S F 0)
    simp at this; exact b.2 (this ▸ 𝔭.zero_mem)
  have hx_eq : x = algebraMap S F a * (algebraMap S F b.1)⁻¹ := by
    rw [← hab, mul_assoc, mul_inv_cancel₀ hb_ne, mul_one]
  rw [hx_eq]
  exact R.mul_mem ha_mem (Subalgebra.inv_mem_of_isUnit' hb_mem hb_unit)

def dvrSubalgebraToValuationSubring
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    ValuationSubring F where
  toSubring := R.toSubring
  mem_or_inv_mem' := by
    intro x
    haveI : ValuationRing R := of_isDiscreteValuationRing R
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
    · left; show x ∈ (R : Set F); rw [← ha]; exact a.2
    · right; show x⁻¹ ∈ (R : Set F); rw [← ha]; exact a.2


instance dvrSubalgebraToValuationSubring_isDVR
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    IsDiscreteValuationRing (dvrSubalgebraToValuationSubring R) := by
  change IsDiscreteValuationRing R; infer_instance

theorem dvr_subalgebra_set_eq_of_subset
    (R₁ R₂ : Subalgebra k F)
    [IsDomain R₁] [IsDiscreteValuationRing R₁] [IsFractionRing R₁ F]
    [IsDomain R₂] [IsDiscreteValuationRing R₂] [IsFractionRing R₂ F]
    (h : (R₁ : Set F) ⊆ (R₂ : Set F)) :
    (R₁ : Set F) = (R₂ : Set F) := by
  have hle : dvrSubalgebraToValuationSubring R₁ ≤ dvrSubalgebraToValuationSubring R₂ := h
  have heq := dvr_valuation_subring_eq_of_le hle
  ext x
  constructor
  · intro hx
    have : x ∈ (dvrSubalgebraToValuationSubring R₁ : Set F) := hx
    rw [heq] at this; exact this
  · intro hx
    have : x ∈ (dvrSubalgebraToValuationSubring R₂ : Set F) := hx
    rw [← heq] at this; exact this


lemma adjoin_image_inv_or_self_eq (S : Set F) (f : F → F)
    (hf : ∀ x ∈ S, f x = x ∨ f x = x⁻¹) :
    IntermediateField.adjoin k (f '' S) = IntermediateField.adjoin k S := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := hy
    rcases hf x hxS with h | h
    · rw [h]; exact IntermediateField.subset_adjoin k S hxS
    · rw [h]; exact IntermediateField.inv_mem _ (IntermediateField.subset_adjoin k S hxS)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hxS
    have hfx_mem : f x ∈ IntermediateField.adjoin k (f '' S) :=
      IntermediateField.subset_adjoin k _ ⟨x, hxS, rfl⟩
    rcases hf x hxS with h | h
    · rwa [h] at hfx_mem
    · have : x = (f x)⁻¹ := by rw [h, inv_inv]
      rw [this]; exact IntermediateField.inv_mem _ hfx_mem

lemma exists_generators_in_dvr
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F]
    (S : Set F) (hS_fin : S.Finite) (hS_gen : IntermediateField.adjoin k S = ⊤) :
    ∃ T : Set F, T.Finite ∧ (∀ t ∈ T, t ∈ (R : Set F)) ∧
      IntermediateField.adjoin k T = ⊤ := by
  classical
  let f : F → F := fun x => if x ∈ (R : Set F) then x else x⁻¹
  refine ⟨f '' S, hS_fin.image f, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, _, rfl⟩ := ht
    simp only [f]
    split_ifs with h
    · exact h
    · haveI : ValuationRing R := of_isDiscreteValuationRing R
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exfalso; exact h (by rw [← ha]; exact a.2)
      · rw [← ha]; exact a.2
  · rw [adjoin_image_inv_or_self_eq S f, hS_gen]
    intro x _
    simp only [f]
    split_ifs <;> [left; right] <;> rfl

end Lemma18_11_Helpers

theorem isFractionRing_adjoin_of_field_generators
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (T : Set F) (hT_gen : IntermediateField.adjoin k T = ⊤) :
    IsFractionRing (Algebra.adjoin k T) F := by
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ IntermediateField.adjoin k T := by rw [hT_gen]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hz
  obtain ⟨r, hr, s, hs, hzrs⟩ := hz
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, by simp [hzrs]⟩

theorem exists_generators_in_dvr_of_function_field
    {k F : Type*} [Field k] [Field F] [Algebra k F] [FunctionField_k k F]
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    ∃ T : Set F, T.Finite ∧ (∀ t ∈ T, t ∈ (R : Set F)) ∧
      IntermediateField.adjoin k T = ⊤ := by
  obtain ⟨S, hS_fin, hS_gen⟩ := IntermediateField.fg_def.mp (FunctionField_k.finitelyGenerated (k := k) (F := F))
  exact exists_generators_in_dvr R S hS_fin hS_gen






theorem exists_maximal_with_complement_units
    {k F : Type*} [Field k] [Field F] [Algebra k F] [FunctionField_k k F]
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F]
    (S : Subalgebra k F) [IsDedekindDomain S] [IsFractionRing S F]
    (hSR : S ≤ R) :
    ∃ (𝔭 : Ideal S) (_ : 𝔭.IsMaximal),
      ∀ (b : 𝔭.primeCompl), IsUnit (⟨algebraMap S F b.1, hSR b.1.2⟩ : R) := by

  let ι : ↥S →+* ↥R := (Subalgebra.inclusion hSR).toRingHom

  let 𝔪 := IsLocalRing.maximalIdeal ↥R

  let 𝔭 := Ideal.comap ι 𝔪

  haveI h𝔭_prime : 𝔭.IsPrime := Ideal.comap_isPrime ι 𝔪


  have h𝔭_ne_bot : 𝔭 ≠ ⊥ := by
    intro h𝔭_eq_bot
    apply IsDiscreteValuationRing.not_isField ↥R
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro f
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective S f
    have hb_ne_zero : (b : ↥S) ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb_not_in_p : b ∉ 𝔭 := by rw [h𝔭_eq_bot]; simp; exact hb_ne_zero
    have hιb_unit : IsUnit (ι b) := by
      have : ι b ∉ 𝔪 := fun h => hb_not_in_p (Ideal.mem_comap.mpr h)
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
    obtain ⟨u, hu⟩ := hιb_unit
    refine ⟨ι a * ↑u⁻¹, ?_⟩
    have key : ∀ (x : ↥R), (algebraMap ↥R F) x = x.val := fun _ => rfl
    rw [key, ← hab]
    change (a : ↥S).val * (↑u⁻¹ : ↥R).val = (a : ↥S).val / (b : ↥S).val
    rw [div_eq_mul_inv]
    congr 1
    have hu_val : ((↑u : ↥R) : F) = ((b : ↥S) : F) := by
      show (↑u : ↥R).val = (ι b : ↥R).val; rw [hu]
    have hmul : ((↑u : ↥R) : F) * ((↑u⁻¹ : ↥R) : F) = 1 := by
      calc ((u : ↥R) : F) * ((↑u⁻¹ : ↥R) : F) = ((↑u * ↑u⁻¹ : ↥R) : F) := rfl
        _ = ((1 : ↥R) : F) := by rw [u.mul_inv]
        _ = 1 := rfl
    rw [← hu_val]; exact eq_inv_of_mul_eq_one_right hmul

  have h𝔭_max : 𝔭.IsMaximal := h𝔭_prime.isMaximal h𝔭_ne_bot

  refine ⟨𝔭, h𝔭_max, ?_⟩

  intro ⟨b, hb⟩
  have hb' : b ∉ 𝔭 := hb
  have hb_not_in_max : ι b ∉ 𝔪 := fun h => hb' (Ideal.mem_comap.mpr h)
  have hunit : IsUnit (ι b) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hb_not_in_max
  convert hunit

theorem localization_embeds_as_dvr_subalgebra
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Subalgebra k F) [IsDedekindDomain S]
    (hfrac : IsFractionRing S F)
    (hnotfield : ¬IsField S)
    (𝔭 : Ideal S) (hmax : 𝔭.IsMaximal) :
    ∃ (L : Subalgebra k F),
      ∃ (_ : IsDomain L),
      ∃ (_ : IsDiscreteValuationRing L),
      ∃ (_ : IsFractionRing L F),
        (L : Set F) = @localizationSubalgebraCarrier k F _ _ _ S hfrac 𝔭
          (@Ideal.IsMaximal.isPrime S _ 𝔭 hmax) := by
  haveI : 𝔭.IsPrime := hmax.isPrime

  set oF := Localization.subalgebra.ofField F 𝔭.primeCompl
    𝔭.primeCompl_le_nonZeroDivisors with oF_def
  set L := oF.restrictScalars k with L_def

  have algebraMap_ne : ∀ (s : ↥S), s ∈ 𝔭.primeCompl → algebraMap ↥S F s ≠ 0 := by
    intro s hs h0
    rw [map_eq_zero_iff _ (IsFractionRing.injective ↥S F)] at h0
    exact hs (h0 ▸ 𝔭.zero_mem)
  refine ⟨L, inferInstance, ?_, ?_, ?_⟩
  ·
    have h𝔭ne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax hnotfield
    have hAtPrime : IsLocalization.AtPrime oF 𝔭 :=
      Localization.subalgebra.isLocalization_ofField F 𝔭.primeCompl
        𝔭.primeCompl_le_nonZeroDivisors
    exact @IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥S _ _ _ _
      h𝔭ne _ oF _ _ _ hAtPrime
  ·
    change IsFractionRing oF F
    infer_instance
  ·
    ext x
    simp only [SetLike.mem_coe]

    change (∃ (a s : ↥S) (_ : s ∈ 𝔭.primeCompl),
        x = algebraMap ↥S F a * (algebraMap ↥S F s)⁻¹) ↔
      (∃ (a : ↥S) (b : 𝔭.primeCompl),
        x * algebraMap ↥S F b.1 = algebraMap ↥S F a)
    constructor
    · rintro ⟨a, s, hs, rfl⟩
      refine ⟨a, ⟨s, hs⟩, ?_⟩
      simp only
      have hsne := algebraMap_ne s hs
      field_simp
    · rintro ⟨a, ⟨s, hs⟩, h⟩
      refine ⟨a, s, hs, ?_⟩
      have hsne := algebraMap_ne s hs
      simp only at h
      have : x * algebraMap ↥S F s * (algebraMap ↥S F s)⁻¹ =
          algebraMap ↥S F a * (algebraMap ↥S F s)⁻¹ := by rw [h]
      rwa [mul_assoc, mul_inv_cancel₀ hsne, mul_one] at this



section AbstractCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

structure DVROfFunctionField (k F : Type*) [Field k] [Field F] [Algebra k F] where
  valRing : ValuationSubring F
  contains_k : ∀ (a : k), algebraMap k F a ∈ valRing
  isDVR : IsDiscreteValuationRing valRing
  isFractionRing : IsFractionRing valRing F

attribute [instance] DVROfFunctionField.isDVR DVROfFunctionField.isFractionRing

def DVROfFunctionField.localRing (P : DVROfFunctionField k F) : ValuationSubring F :=
  P.valRing

def DVROfFunctionField.vanishesAt (P : DVROfFunctionField k F) (f : F) : Prop :=
  ∃ (hf : f ∈ P.valRing), ¬IsUnit (⟨f, hf⟩ : P.valRing)

def AbstractCurve.regularFunctions (U : Set (DVROfFunctionField k F)) : Subring F where
  carrier := {f : F | ∀ P ∈ U, f ∈ P.valRing}
  mul_mem' hf hg P hP := P.valRing.toSubring.mul_mem (hf P hP) (hg P hP)
  one_mem' P _ := P.valRing.toSubring.one_mem
  add_mem' hf hg P hP := P.valRing.toSubring.add_mem (hf P hP) (hg P hP)
  zero_mem' P _ := P.valRing.toSubring.zero_mem
  neg_mem' hf P hP := P.valRing.toSubring.neg_mem (hf P hP)

def AbstractCurve.zeroLocus (S : Set F) : Set (DVROfFunctionField k F) :=
  {P | ∀ f ∈ S, P.vanishesAt f}

instance AbstractCurve.zariskiTopology : TopologicalSpace (DVROfFunctionField k F) :=
  TopologicalSpace.generateFrom
    {U | ∃ (f : F), U = (AbstractCurve.zeroLocus ({f} : Set F))ᶜ}

structure AbstractCurve (k F : Type*) [Field k] [Field F] [Algebra k F] where
  finitelyGenerated : (⊤ : IntermediateField k F).FG
  transcendenceDegreeOne : ∃ (x : F), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) F
  algClosedInF : ∀ (x : F), IsAlgebraic k x → x ∈ (⊥ : IntermediateField k F)
  topology : TopologicalSpace (DVROfFunctionField k F) := AbstractCurve.zariskiTopology

@[reducible]
def AbstractCurve.toFunctionField_k {k F : Type*} [Field k] [Field F] [Algebra k F]
    (C : AbstractCurve k F) : FunctionField_k k F where
  finitelyGenerated := C.finitelyGenerated
  transcendenceDegreeOne := C.transcendenceDegreeOne
  algClosedInF := C.algClosedInF

def AbstractCurve.ofFunctionField_k (k F : Type*) [Field k] [Field F] [Algebra k F]
    [h : FunctionField_k k F] : AbstractCurve k F where
  finitelyGenerated := h.finitelyGenerated
  transcendenceDegreeOne := h.transcendenceDegreeOne
  algClosedInF := h.algClosedInF

lemma AbstractCurve.regularFunctions_mem (U : Set (DVROfFunctionField k F))
    (f : AbstractCurve.regularFunctions U) (P : DVROfFunctionField k F) (hP : P ∈ U) :
    (f : F) ∈ P.valRing := f.2 P hP

lemma AbstractCurve.globalRegularFunctions_eq :
    (AbstractCurve.regularFunctions (Set.univ : Set (DVROfFunctionField k F))).carrier =
      {f : F | ∀ P : DVROfFunctionField k F, f ∈ P.valRing} := by
  ext f
  simp only [regularFunctions, Set.mem_setOf_eq, Set.mem_univ, true_implies]

structure AbstractCurveMorphism (k F₁ F₂ : Type*) [Field k] [Field F₁] [Field F₂]
    [Algebra k F₁] [Algebra k F₂] where
  toFun : DVROfFunctionField k F₁ → DVROfFunctionField k F₂
  pullback : F₂ →+* F₁
  pullback_comp : ∀ (a : k), pullback (algebraMap k F₂ a) = algebraMap k F₁ a
  pullback_regular : ∀ (P : DVROfFunctionField k F₁) (f : F₂),
    f ∈ (toFun P).valRing → pullback f ∈ P.valRing

lemma AbstractCurveMorphism.pullback_regular_on_open
    {k F₁ F₂ : Type*} [Field k] [Field F₁] [Field F₂] [Algebra k F₁] [Algebra k F₂]
    (φ : AbstractCurveMorphism k F₁ F₂) (U : Set (DVROfFunctionField k F₂))
    (f : F₂) (hf : ∀ P ∈ U, f ∈ P.valRing) :
    ∀ Q ∈ φ.toFun ⁻¹' U, φ.pullback f ∈ Q.valRing := by
  intro Q hQ
  exact φ.pullback_regular Q f (hf (φ.toFun Q) hQ)

end AbstractCurve

section Theorem18_10

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

noncomputable def SmoothProjectiveCurveData.pointValSubring
    {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) :
    ValuationSubring K where
  toSubring := (algebraMap (C.R p) K).range
  mem_or_inv_mem' x := by
    haveI : ValuationRing (C.R p) := of_isDiscreteValuationRing (C.R p)
    rcases ValuationRing.isInteger_or_isInteger (C.R p) x with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; exact ⟨r, hr⟩
    · right; exact ⟨r, hr⟩

noncomputable instance SmoothProjectiveCurveData.pointValSubring_isDVR
    {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) :
    IsDiscreteValuationRing (C.pointValSubring p) := by
  have : IsDomain (C.pointValSubring p) := Subring.instIsDomainSubtypeMem _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective
      ((algebraMap (C.R p) K).codRestrict (C.pointValSubring p).toSubring (fun r => ⟨r, rfl⟩))
      ⟨fun _ _ h => IsFractionRing.injective (C.R p) K (Subtype.ext_iff.mp h),
       fun ⟨_, r, rfl⟩ => ⟨r, rfl⟩⟩)

theorem SmoothProjectiveCurveData.contains_k
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P)
    (a : k) : algebraMap k K a ∈ C.pointValSubring p := by
  change ∃ a_1, (algebraMap (C.R p) K) a_1 = (algebraMap k K) a
  exact ⟨algebraMap k (C.R p) a, (IsScalarTower.algebraMap_apply k (C.R p) K a).symm⟩

noncomputable def SmoothProjectiveCurveData.pointToDVR
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) : DVROfFunctionField k K where
  valRing := C.pointValSubring p
  contains_k := C.contains_k p
  isDVR := C.pointValSubring_isDVR p
  isFractionRing := inferInstance

theorem SmoothProjectiveCurveData.pointToDVR_injective
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) :
    Function.Injective C.pointToDVR := by
  intro p₁ p₂ h
  apply C.localRing_injective p₁ p₂
  exact congrArg ValuationSubring.toSubring (congrArg DVROfFunctionField.valRing h)

theorem SmoothProjectiveCurveData.pointToDVR_surjective
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) :
    Function.Surjective C.pointToDVR := by
  intro d
  haveI := d.isDVR
  haveI := d.isFractionRing
  obtain ⟨p, hp⟩ := C.localRing_surjective d.valRing
  refine ⟨p, ?_⟩
  have h_eq : C.pointValSubring p = d.valRing := ValuationSubring.toSubring_injective hp
  cases d
  subst h_eq
  rfl

def SmoothProjectiveCurveData.vanishesAt
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) (f : K) : Prop :=
  ∃ (hf : f ∈ (C.pointValSubring p : Set K)),
    ¬IsUnit (⟨f, hf⟩ : C.pointValSubring p)

def SmoothProjectiveCurveData.zariskiTopology
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) : TopologicalSpace C.P :=
  TopologicalSpace.generateFrom
    {U | ∃ (f : K), U = {p | ¬C.vanishesAt p f}}

def SmoothProjectiveCurveData.regularFunctions
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (U : Set C.P) : Set K :=
  {f : K | ∀ p ∈ U, f ∈ (C.pointValSubring p : Set K)}

structure AbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) where
  pointEquiv : C.P ≃ DVROfFunctionField k K
  localRing_compat : ∀ p, Set.range (algebraMap (C.R p) K) = ((pointEquiv p).valRing : Set K)
  forward_continuous : @Continuous C.P (DVROfFunctionField k K)
    C.zariskiTopology AbstractCurve.zariskiTopology pointEquiv

  regularFunctions_compat : ∀ (U : Set (DVROfFunctionField k K)),
    (AbstractCurve.regularFunctions U).carrier =
      C.regularFunctions (pointEquiv.symm '' U)

theorem smooth_projective_curve_isomorphic_abstract_curve
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) :
    Nonempty (AbstractCurveIsomorphism C) := by

  let φ := Equiv.ofBijective C.pointToDVR
    ⟨C.pointToDVR_injective, C.pointToDVR_surjective⟩

  have hlr : ∀ p, Set.range (algebraMap (C.R p) K) = ((φ p).valRing : Set K) := by
    intro p
    show Set.range (algebraMap (C.R p) K) = ↑(Equiv.ofBijective C.pointToDVR _ p).valRing
    simp only [Equiv.ofBijective_apply]
    rfl


  have hcont : @Continuous C.P (DVROfFunctionField k K) C.zariskiTopology
      AbstractCurve.zariskiTopology φ := by
    change @Continuous C.P (DVROfFunctionField k K)
      (TopologicalSpace.generateFrom {U | ∃ f : K, U = {p | ¬C.vanishesAt p f}})
      (TopologicalSpace.generateFrom {U | ∃ f : K, U = (AbstractCurve.zeroLocus ({f} : Set K))ᶜ}) φ
    rw [continuous_generateFrom_iff]
    intro U ⟨f, hfU⟩
    subst hfU

    suffices h : φ ⁻¹' (AbstractCurve.zeroLocus ({f} : Set K))ᶜ = {p | ¬C.vanishesAt p f} by
      rw [h]; exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, rfl⟩
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
      AbstractCurve.zeroLocus, Set.mem_singleton_iff, forall_eq,
      DVROfFunctionField.vanishesAt, SmoothProjectiveCurveData.vanishesAt,
      show (C.pointValSubring p : Set K) = ((φ p).valRing : Set K) from rfl]

    exact Iff.rfl

  have hreg : ∀ (U : Set (DVROfFunctionField k K)),
      (AbstractCurve.regularFunctions U).carrier =
        C.regularFunctions (φ.symm '' U) := by
    intro U
    ext f
    simp only [AbstractCurve.regularFunctions, Set.mem_setOf_eq,
      SmoothProjectiveCurveData.regularFunctions]
    constructor
    · intro hf p hp
      obtain ⟨Q, hQU, hQp⟩ := hp
      subst hQp
      have hfQ := hf Q hQU


      show f ∈ (C.pointValSubring (φ.symm Q) : Set K)
      change f ∈ ((φ (φ.symm Q)).valRing : Set K)
      simp only [Equiv.apply_symm_apply]
      exact hfQ
    · intro hf Q hQU
      have hQ : φ.symm Q ∈ φ.symm '' U := ⟨Q, hQU, rfl⟩
      have hmem := hf (φ.symm Q) hQ

      show f ∈ Q.valRing
      have : (C.pointValSubring (φ.symm Q) : Set K) = ((φ (φ.symm Q)).valRing : Set K) := rfl
      rw [this, show (φ (φ.symm Q)).valRing = Q.valRing from by simp [Equiv.apply_symm_apply]] at hmem
      exact hmem
  exact ⟨⟨φ, hlr, hcont, hreg⟩⟩

structure IsAbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n)
    (φ : C.P ≃ DVROfFunctionField k K) : Prop where
  localRing_eq : ∀ p, Set.range (algebraMap (C.R p) K) = ((φ p).valRing : Set K)
  regularFunctions_eq : ∀ (U : Set C.P) (f : K),
    f ∈ C.regularFunctions U ↔ f ∈ AbstractCurve.regularFunctions (φ '' U)

theorem smooth_projective_curve_isomorphic_abstract_curve_as_curves
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) :
    ∃ (φ : C.P ≃ DVROfFunctionField k K), IsAbstractCurveIsomorphism C φ := by

  let φ := Equiv.ofBijective C.pointToDVR
    ⟨C.pointToDVR_injective, C.pointToDVR_surjective⟩
  refine ⟨φ, ?_⟩

  have hlr : ∀ p, Set.range (algebraMap (C.R p) K) = ((φ p).valRing : Set K) := by
    intro p
    show Set.range (algebraMap (C.R p) K) = ↑(Equiv.ofBijective C.pointToDVR _ p).valRing
    simp only [Equiv.ofBijective_apply]
    rfl
  exact ⟨hlr, fun U f => by


    simp only [SmoothProjectiveCurveData.regularFunctions, AbstractCurve.regularFunctions,
      Set.mem_setOf_eq, Set.mem_image]
    constructor
    ·
      intro hf Q ⟨p, hpU, hpQ⟩
      have hmem : f ∈ (↑(φ p).valRing : Set K) := (hlr p) ▸ hf p hpU
      rw [← hpQ]
      exact hmem
    ·
      intro hf p hpU
      have hmem : f ∈ (↑(φ p).valRing : Set K) := hf (φ p) ⟨p, hpU, rfl⟩
      rw [← hlr p] at hmem
      exact hmem⟩

end Theorem18_10

instance instIsDiscreteValuationRingSubtypeValuationSubring {K : Type*} [Field K]
    (p : { V : ValuationSubring K // IsDiscreteValuationRing V }) :
    IsDiscreteValuationRing ↥p.val := p.prop

lemma ValuationSubring.eq_top_of_isField {K : Type*} [Field K]
    (V : ValuationSubring K) (hField : IsField V) : V = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_top, iff_true]
  by_cases hx : x = 0
  · exact hx ▸ V.zero_mem
  · rcases V.mem_or_inv_mem x with h | h
    · exact h
    · have hxinv_ne : (⟨x⁻¹, h⟩ : V) ≠ 0 := by
        simp [Subtype.ext_iff, inv_ne_zero hx]
      obtain ⟨y, hy⟩ := hField.mul_inv_cancel hxinv_ne
      have hval : x⁻¹ * (y : K) = 1 := by
        have := congr_arg Subtype.val hy; simpa using this
      have heq : (y : K) = x := by
        have h1 : x⁻¹ = (↑y)⁻¹ := eq_inv_of_mul_eq_one_left hval
        rw [← inv_inj, h1]
      exact heq ▸ y.prop

lemma ValuationSubring.isDVR_of_isNoetherianRing_of_ne_top {K : Type*} [Field K]
    (V : ValuationSubring K) (hNoeth : IsNoetherianRing V) (hV : V ≠ ⊤) :
    IsDiscreteValuationRing V :=
  ((IsDiscreteValuationRing.TFAE (↑V) (fun hField => hV (ValuationSubring.eq_top_of_isField V hField))).out 0 1).mpr
    (inferInstance : ValuationRing V)










def BiratIso.ofSameFunctionField
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    BiratIso C₁ C₂ where
  σ := RingEquiv.refl F
  forward := ⟨C₂.emb, C₂.emb_ne_zero⟩
  backward := ⟨C₁.emb, C₁.emb_ne_zero⟩
  forward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩
  backward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩

def unique_smooth_model_uniqueness
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    CurveIso C₁ C₂ :=
  SmoothProjectiveCurve.birational_map_is_isomorphism (BiratIso.ofSameFunctionField C₁ C₂)


end ArithmeticGeometry
