/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Lagrange
import Atlas.ArithmeticGeometry.code.CompleteVarieties
import Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Atlas.ArithmeticGeometry.code.ProjectiveComplete

universe u

class IsProjectiveVariety (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] :
    Prop where
  exists_algVariety_projective :
    ∃ (_ : IsAlgClosed k)
      (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›) ∧
      Nonempty (AlgebraicGeometry.CompletenessValuationCriterion.IsProjectiveVariety algV)


def AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties
    {k : Type u} [Field k]
    (X Y : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
    (f : X.carrier → Y.carrier) : Prop :=
  ∃ (pullback : Y.functionField →+* X.functionField),


    (∀ a : k, pullback (Y.baseEmbed a) = X.baseEmbed a) ∧


    (∀ (P : X.carrier) (r : Y.functionField),
      r ∈ Y.localRingAt (f P) → pullback r ∈ X.localRingAt P)

class IsAlgebraicGroup (k : outParam (Type u)) [Field k] (V : Type u) [TopologicalSpace V] [Group V] : Prop where
  toIsTopologicalGroup : IsTopologicalGroup V
  isVariety :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hcarrier : algV.carrier = V),
      (hcarrier ▸ algV.topInst = ‹TopologicalSpace V›)
  mul_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (algVV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V) (hVV : algVV.carrier = (V × V))
      (f : algVV.carrier → algV.carrier),

      (∀ p : algVV.carrier, cast hV (f p) =
        (cast hVV p).1 * (cast hVV p).2) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algVV algV f
  inv_isMorphism :
    ∃ (algV : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
      (hV : algV.carrier = V)
      (f : algV.carrier → algV.carrier),

      (∀ v : algV.carrier, cast hV (f v) = (cast hV v)⁻¹) ∧

      AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties algV algV f


attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup



class IsAbelianVariety (k : outParam (Type u)) [Field k] (A : Type u) [TopologicalSpace A] [Group A] : Prop
    extends IsProjectiveVariety k A, IsAlgebraicGroup k A, ConnectedSpace A


open WeierstrassCurve

abbrev WeierstrassEquation (k : Type*) := WeierstrassCurve k


theorem WeierstrassCurve.exists_variableChange_a₁_a₂_a₃_eq_zero
    {k : Type*} [Field k] (hchar2 : (2 : k) ≠ 0) (hchar3 : (3 : k) ≠ 0)
    (W : WeierstrassCurve k) :
    ∃ C : VariableChange k, (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 := by

  set C₁ : VariableChange k := ⟨1, 0, -(W.a₁ / 2), -(W.a₃ / 2)⟩
  set W₁ := C₁ • W
  have hW₁_a₁ : W₁.a₁ = 0 := by
    simp [W₁, variableChange_a₁, C₁]
    field_simp
    ring
  have hW₁_a₃ : W₁.a₃ = 0 := by
    simp [W₁, variableChange_a₃, C₁]
    field_simp
    ring

  set C₂ : VariableChange k := ⟨1, -(W₁.a₂ / 3), 0, 0⟩

  refine ⟨C₂ * C₁, ?_, ?_, ?_⟩
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₁]
    simp [C₂, hW₁_a₁]
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₂]
    simp [C₂, hW₁_a₁]
    field_simp
    ring
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₃]
    simp [C₂, hW₁_a₁, hW₁_a₃]

def WeierstrassCurve.shortWeierstrass {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, A, B⟩

namespace WeierstrassCurve

abbrev IsShortWeierstrass {R : Type*} [CommRing R] (W : WeierstrassCurve R) : Prop :=
  W.IsShortNF

variable {R : Type*} [CommRing R] (A B : R)

instance shortWeierstrass_isShortNF : (shortWeierstrass A B).IsShortNF where
  a₁ := rfl
  a₂ := rfl
  a₃ := rfl


theorem isElliptic_shortNF_iff
    {F : Type*} [Field F] [NeZero (2 : F)] (W : WeierstrassCurve F) [W.IsShortNF] :
    W.IsElliptic ↔ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
  rw [isElliptic_iff, Δ_of_isShortNF, isUnit_iff_ne_zero, mul_ne_zero_iff]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro h
    exact ⟨by rw [neg_ne_zero]; exact_mod_cast pow_ne_zero 4 (NeZero.ne (2 : F)), h⟩

theorem shortWeierstrass_isElliptic_iff
    {F : Type*} [Field F] [NeZero (2 : F)] (A B : F) :
    (shortWeierstrass A B).IsElliptic ↔ 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 :=
  isElliptic_shortNF_iff (shortWeierstrass A B)


end WeierstrassCurve

abbrev EllipticCurve' (k : Type*) [CommRing k] := { W : WeierstrassCurve k // W.IsElliptic }

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

theorem divisorClassMap_injective :
    Function.Injective (toClass : W.Point → Additive (ClassGroup W.CoordinateRing)) :=
  toClass_injective





end WeierstrassCurve.Affine.Point

end Theorem_23_16

section Lemma_23_7

open Polynomial Matrix GeneralLinearGroup OnePoint

theorem aut_P1_fixing_three_points_is_identity {K : Type*} [Field K] [DecidableEq K]
    (g : GL (Fin 2) K) (p₁ p₂ p₃ : OnePoint K)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hf₁ : g • p₁ = p₁) (hf₂ : g • p₂ = p₂) (hf₃ : g • p₃ = p₃) :
    ∀ p : OnePoint K, g • p = p := by


  have hfp : g.fixpointPolynomial = 0 := by

    have eval_root : ∀ c : K, g • (c : OnePoint K) = c → g.fixpointPolynomial.eval c = 0 := by
      intro c hc
      have := fixpointPolynomial_aeval_eq_zero_iff.mpr hc
      simpa [aeval_def, eval₂_eq_eval_map] using this

    cases p₁ with
    | coe c₁ => cases p₂ with
      | coe c₂ => cases p₃ with
        | coe c₃ =>

          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₂, c₃})
          · rw [show ({c₁, c₂, c₃} : Finset K).card = 3 from by
              simp [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
                show c₁ ≠ c₂ from fun h => h₁₂ (congrArg _ h),
                show c₁ ≠ c₃ from fun h => h₁₃ (congrArg _ h),
                show c₂ ≠ c₃ from fun h => h₂₃ (congrArg _ h)]]
            calc g.fixpointPolynomial.degree ≤ 2 := by
                  apply degree_le_of_natDegree_le; unfold fixpointPolynomial
                  rw [sub_eq_add_neg, ← C_neg]; exact natDegree_quadratic_le
              _ < 3 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> exact eval_root _ (by assumption)
        | infty =>

          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₃
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₂})
          · rw [Finset.card_pair (fun h => h₁₂ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
                  apply degree_le_of_natDegree_le; unfold fixpointPolynomial
                  rw [h10, sub_eq_add_neg, ← C_neg]
                  simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact eval_root _ (by assumption)
      | infty => cases p₃ with
        | coe c₃ =>

          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₂
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₃})
          · rw [Finset.card_pair (fun h => h₁₃ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
                  apply degree_le_of_natDegree_le; unfold fixpointPolynomial
                  rw [h10, sub_eq_add_neg, ← C_neg]
                  simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact eval_root _ (by assumption)
        | infty => exact absurd rfl h₂₃
    | infty => cases p₂ with
      | coe c₂ => cases p₃ with
        | coe c₃ =>

          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₁
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₂, c₃})
          · rw [Finset.card_pair (fun h => h₂₃ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
                  apply degree_le_of_natDegree_le; unfold fixpointPolynomial
                  rw [h10, sub_eq_add_neg, ← C_neg]
                  simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact eval_root _ (by assumption)
        | infty => exact absurd rfl h₁₃
      | infty => exact absurd rfl h₁₂

  have hscalar := fixpointPolynomial_eq_zero_iff.mp hfp

  obtain ⟨a, ha⟩ := hscalar
  intro p
  cases p with
  | infty => rw [smul_infty_eq_self_iff]; simp [← ha]
  | coe c =>
    rw [smul_some_eq_ite]
    have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp [← ha]
    have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = a := by simp [← ha]
    have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = a := by simp [← ha]
    have h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp [← ha]
    have ha_ne : a ≠ 0 := by
      intro ha0
      exact g.det_ne_zero (by rw [← ha, det_fin_two]; simp [ha0])
    simp [h10, h11, h00, h01, ha_ne]

end Lemma_23_7

def MazurCyclicOrders : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

def MazurProductOrders : Finset ℕ := {1, 2, 3, 4}


namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

def lineThirdIntersection : W.Point → W.Point → W.Point
  | zero, Q => -Q
  | some x₁ y₁ h₁, zero => -(some x₁ y₁ h₁)
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
      if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0
      else some _ _ (nonsingular_negAdd h₁ h₂ hxy)

theorem geometric_group_law (P Q : W.Point) :
    P + Q = -(lineThirdIntersection P Q) := by
  cases P with
  | zero =>
    simp only [lineThirdIntersection, ← zero_def, zero_add, neg_neg]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      simp only [lineThirdIntersection, ← zero_def, add_zero, neg_neg]
    | some x₂ y₂ h₂ =>
      simp only [lineThirdIntersection]
      split_ifs with hxy
      · rw [neg_zero]
        exact add_of_Y_eq hxy.1 hxy.2
      · rw [add_some hxy, neg_some]
        simp only [addY]


end WeierstrassCurve.Affine.Point

section NTorsion

variable {G : Type*} [AddCommGroup G]

abbrev multiplicationByN (n : ℕ) : G →+ G := nsmulAddMonoidHom n

def nTorsionSubgroup (n : ℕ) : AddSubgroup G := (nsmulAddMonoidHom n : G →+ G).ker

@[simp]
theorem mem_nTorsionSubgroup (n : ℕ) (P : G) :
    P ∈ nTorsionSubgroup n ↔ n • P = 0 := by
  simp [nTorsionSubgroup]


end NTorsion

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

abbrev nTorsion (n : ℕ) : AddSubgroup W.Point := nTorsionSubgroup n


end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

noncomputable def autGroup (R : Type*) [CommRing R] (W : WeierstrassCurve R) :
    Subgroup (VariableChange R) :=
  MulAction.stabilizer (VariableChange R) W

section ShortNFAut

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF]

lemma VariableChange.u_inv_ne_zero (C : VariableChange F) : (↑C.u⁻¹ : F) ≠ 0 := by
  simp only [Units.val_inv_eq_inv_val, ne_eq, inv_eq_zero]; exact Units.ne_zero C.u

lemma aut_s_eq_zero {C : VariableChange F} (hC : C • W = W) (h2 : (2 : F) ≠ 0) :
    C.s = 0 := by
  have ha1 : (C • W).a₁ = W.a₁ := by rw [hC]
  rw [variableChange_a₁, IsShortNF.a₁ (W := W)] at ha1
  simp only [zero_add] at ha1
  cases mul_eq_zero.mp ha1 with
  | inl h => exact absurd h C.u_inv_ne_zero
  | inr h => exact mul_left_cancel₀ h2 (h.trans (mul_zero 2).symm)

lemma aut_r_eq_zero {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.r = 0 := by
  have ha2 : (C • W).a₂ = W.a₂ := by rw [hC]
  rw [variableChange_a₂, IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W)] at ha2
  simp only [aut_s_eq_zero hC h2, mul_zero, sub_zero, sq, zero_add] at ha2
  rcases mul_eq_zero.mp ha2 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' C.u_inv_ne_zero
    · exact absurd h' C.u_inv_ne_zero
  · exact mul_left_cancel₀ h3 (h.trans (mul_zero 3).symm)

lemma aut_t_eq_zero {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.t = 0 := by
  have ha3 : (C • W).a₃ = W.a₃ := by rw [hC]
  rw [variableChange_a₃, IsShortNF.a₁ (W := W), IsShortNF.a₃ (W := W)] at ha3
  simp only [aut_r_eq_zero hC h2 h3, zero_mul, zero_add] at ha3
  cases mul_eq_zero.mp ha3 with
  | inl h => exact absurd h (pow_ne_zero 3 C.u_inv_ne_zero)
  | inr h => exact mul_left_cancel₀ h2 (h.trans (mul_zero 2).symm)

lemma aut_u_inv_pow4_mul_a₄ {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (↑C.u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ := by
  have ha4 : (C • W).a₄ = W.a₄ := by rw [hC]
  rw [variableChange_a₄] at ha4
  simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W),
    aut_s_eq_zero hC h2, aut_r_eq_zero hC h2 h3, aut_t_eq_zero hC h2 h3] at ha4
  ring_nf at ha4 ⊢; exact ha4

lemma aut_u_inv_pow6_mul_a₆ {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (↑C.u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  have ha6 : (C • W).a₆ = W.a₆ := by rw [hC]
  rw [variableChange_a₆] at ha6
  simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W),
    aut_r_eq_zero hC h2 h3, aut_t_eq_zero hC h2 h3] at ha6
  ring_nf at ha6 ⊢; exact ha6

lemma aut_u_inv_pow4_eq_one {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) :
    (↑C.u⁻¹ : F) ^ 4 = 1 := by
  have h := aut_u_inv_pow4_mul_a₄ hC h2 h3
  rwa [← sub_eq_zero, ← sub_one_mul, mul_eq_zero, sub_eq_zero, or_iff_left ha4] at h

lemma aut_u_inv_pow6_eq_one {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0) :
    (↑C.u⁻¹ : F) ^ 6 = 1 := by
  have h := aut_u_inv_pow6_mul_a₆ hC h2 h3
  rwa [← sub_eq_zero, ← sub_one_mul, mul_eq_zero, sub_eq_zero, or_iff_left ha6] at h

lemma aut_u_inv_pow2_eq_one {C : VariableChange F} (hC : C • W = W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ ≠ 0) :
    (↑C.u⁻¹ : F) ^ 2 = 1 := by
  have h4 := aut_u_inv_pow4_eq_one hC h2 h3 ha4
  have h6 := aut_u_inv_pow6_eq_one hC h2 h3 ha6
  have : (↑C.u⁻¹ : F) ^ 6 = (↑C.u⁻¹ : F) ^ 4 * (↑C.u⁻¹ : F) ^ 2 := by ring
  rw [h6, h4, one_mul] at this; exact this.symm

lemma a₄_ne_zero_or_a₆_ne_zero [W.IsElliptic] : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  exact W.isUnit_Δ.ne_zero (by
    simp only [Δ, b₂, b₄, b₆, b₈,
      IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W), h.1, h.2]; ring)

lemma u_pow_eq_one_of_inv_val_pow_eq_one {C : VariableChange F} {n : ℕ}
    (h : (↑C.u⁻¹ : F) ^ n = 1) : C.u ^ n = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one] at h
  exact Units.val_injective (by rw [Units.val_pow_eq_pow_val]; simpa using h)

end ShortNFAut

section Theorem26_11

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF] [W.IsElliptic]

lemma autGroup_u_pow_twelve {C : VariableChange F} (hC : C ∈ autGroup F W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : C.u ^ 12 = 1 := by
  rcases a₄_ne_zero_or_a₆_ne_zero (W := W) with ha4 | ha6
  · have h4 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one hC h2 h3 ha4)
    have : C.u ^ 12 = (C.u ^ 4) ^ 3 := by group
    rw [this, h4, one_pow]
  · have h6 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow6_eq_one hC h2 h3 ha6)
    have : C.u ^ 12 = (C.u ^ 6) ^ 2 := by group
    rw [this, h6, one_pow]

instance autGroup_finite (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Finite (autGroup F W) := by
  haveI : Finite (rootsOfUnity 12 F) := Finite.of_fintype _
  let f : autGroup F W → rootsOfUnity 12 F := fun C =>
    ⟨(C : VariableChange F).u,
     (mem_rootsOfUnity 12 _).mpr (autGroup_u_pow_twelve C.2 h2 h3)⟩
  apply Finite.of_injective f
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  have hu : C₁.u = C₂.u := congr_arg Subtype.val h
  exact Subtype.ext (VariableChange.ext hu
    (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
    (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
    (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))

omit [W.IsElliptic] in
noncomputable def autGroupToFHom
    (_h2 : (2 : F) ≠ 0) (_h3 : (3 : F) ≠ 0) : autGroup F W →* F where
  toFun C := ↑(C : VariableChange F).u
  map_one' := by simp [VariableChange.one_def]
  map_mul' _ _ := by simp [VariableChange.mul_def]

omit [W.IsElliptic] in
lemma autGroupToFHom_injective (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Function.Injective (autGroupToFHom h2 h3 : autGroup F W →* F) := by
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  simp only [autGroupToFHom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  have hu : C₁.u = C₂.u := Units.val_injective h
  exact Subtype.ext (VariableChange.ext hu
    (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
    (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
    (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))

theorem autGroup_isCyclic (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsCyclic (autGroup F W) := by
  haveI : Finite (autGroup F W) := autGroup_finite h2 h3
  exact isCyclic_of_injective_ringHom (autGroupToFHom h2 h3) (autGroupToFHom_injective h2 h3)

omit [W.IsElliptic] in
theorem autGroup_u_sq_eq_one_of_generic_j
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ ≠ 0)
    {C : VariableChange F} (hC : C ∈ autGroup F W) :
    C.u ^ 2 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow2_eq_one hC h2 h3 ha4 ha6),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

omit [W.IsElliptic] in
theorem autGroup_u_pow4_eq_one_of_j_1728
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0)
    {C : VariableChange F} (hC : C ∈ autGroup F W) :
    C.u ^ 4 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one hC h2 h3 ha4),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

omit [W.IsElliptic] in
theorem autGroup_u_pow6_eq_one_of_j_0
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0)
    {C : VariableChange F} (hC : C ∈ autGroup F W) :
    C.u ^ 6 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow6_eq_one hC h2 h3 ha6),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

omit [W.IsElliptic] in
lemma neg_one_mem_autGroup : (⟨-1, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
  show (⟨-1, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  ext <;> simp [Units.val_neg, Units.val_one] <;> ring

lemma u_inv_val_pow_eq_one {n : ℕ} {u : Fˣ} (h : u ^ n = 1) :
    (↑u⁻¹ : F) ^ n = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one]
  have := congr_arg Units.val h
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
  exact this

omit [W.IsElliptic] in
lemma fourth_root_mem_autGroup {u : Fˣ} (hu : u ^ 4 = 1) (ha₆ : W.a₆ = 0) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
  show (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  have hinv : (↑u⁻¹ : F) ^ 4 = 1 := u_inv_val_pow_eq_one hu
  ext <;> simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W),
    IsShortNF.a₃ (W := W), ha₆] <;> ring_nf
  · rw [hinv, one_mul]

omit [W.IsElliptic] in
lemma sixth_root_mem_autGroup {u : Fˣ} (hu : u ^ 6 = 1) (ha₄ : W.a₄ = 0) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
  show (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  have hinv : (↑u⁻¹ : F) ^ 6 = 1 := u_inv_val_pow_eq_one hu
  ext <;> simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W),
    IsShortNF.a₃ (W := W), ha₄] <;> ring_nf
  · rw [hinv, one_mul]

lemma neg_one_ne_one_variableChange (h2 : (2 : F) ≠ 0) :
    (⟨-1, 0, 0, 0⟩ : VariableChange F) ≠ 1 := by
  rw [VariableChange.one_def]
  intro h
  have := congr_arg VariableChange.u h
  simp only at this
  have hF : (-1 : F) = 1 := by
    have := congr_arg Units.val this; simpa using this
  apply h2
  have h' : (1 : F) + 1 = 0 := by
    have h0 : (-1 : F) + 1 = 0 := by ring
    rwa [hF] at h0
  have h1 : (2 : F) = 1 + 1 := by norm_num
  rw [h1]; exact h'

lemma vc_eq_one_or_neg_one {C : VariableChange F}
    (hu : C.u ^ 2 = 1) (hr : C.r = 0) (hs : C.s = 0) (ht : C.t = 0) :
    C = 1 ∨ C = ⟨-1, 0, 0, 0⟩ := by
  have hv : (↑C.u : F) ^ 2 = 1 := by
    have := congr_arg Units.val hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this; exact this
  rcases sq_eq_one_iff.mp hv with h1 | h1
  · left; rw [VariableChange.one_def]
    exact VariableChange.ext (Units.val_injective (by simpa using h1)) hr hs ht
  · right
    exact VariableChange.ext (Units.val_injective (by simpa using h1)) hr hs ht

omit [W.IsElliptic] in
theorem autGroup_card_eq_two_of_generic_j
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ ≠ 0) :
    Nat.card (autGroup F W) = 2 := by
  haveI : Finite (autGroup F W) := by
    haveI : Finite (rootsOfUnity 12 F) := Finite.of_fintype _
    let f : autGroup F W → rootsOfUnity 12 F := fun C =>
      ⟨(C : VariableChange F).u,
       (mem_rootsOfUnity 12 _).mpr (by
        have h4 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one C.2 h2 h3 ha4)
        have : C.val.u ^ 12 = (C.val.u ^ 4) ^ 3 := by group
        rw [this, h4, one_pow])  ⟩
    apply Finite.of_injective f
    intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
    have hu : C₁.u = C₂.u := congr_arg Subtype.val h
    exact Subtype.ext (VariableChange.ext hu
      (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
      (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
      (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨⟨-1, 0, 0, 0⟩, neg_one_mem_autGroup⟩, ?_, ?_⟩
  · intro h
    exact neg_one_ne_one_variableChange h2
      (congr_arg Subtype.val h).symm
  · apply Set.eq_univ_of_forall
    intro ⟨C, hC⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have := autGroup_u_sq_eq_one_of_generic_j h2 h3 ha4 ha6 hC
    rcases vc_eq_one_or_neg_one this.1 this.2.1 this.2.2.1 this.2.2.2 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity4
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ = 0) :
    autGroup F W ≃ rootsOfUnity 4 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 4 C.u).mpr
        (autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₁
      have hd2 := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, fourth_root_mem_autGroup ((mem_rootsOfUnity 4 ζ).mp hζ) ha6⟩, ?_⟩
      exact Subtype.ext rfl⟩

omit [W.IsElliptic] in
theorem autGroup_card_eq_four_of_j_1728
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ = 0) {ζ : F} (hζ : IsPrimitiveRoot ζ 4) :
    Nat.card (autGroup F W) = 4 := by
  haveI : NeZero (4 : ℕ) := ⟨by omega⟩
  have hcard := hζ.card_rootsOfUnity
  rw [show Nat.card (autGroup F W) =
      Nat.card (rootsOfUnity 4 F) from
    Nat.card_congr (autGroupEquivRootsOfUnity4 h2 h3 ha4 ha6)]
  rw [Nat.card_eq_fintype_card, hcard]

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity6
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0) (ha4 : W.a₄ = 0) :
    autGroup F W ≃ rootsOfUnity 6 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 6 C.u).mpr
        (autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₁
      have hd2 := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, sixth_root_mem_autGroup ((mem_rootsOfUnity 6 ζ).mp hζ) ha4⟩, ?_⟩
      exact Subtype.ext rfl⟩

omit [W.IsElliptic] in
theorem autGroup_card_eq_six_of_j_0
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (ha6 : W.a₆ ≠ 0) (ha4 : W.a₄ = 0) {ζ : F} (hζ : IsPrimitiveRoot ζ 6) :
    Nat.card (autGroup F W) = 6 := by
  haveI : NeZero (6 : ℕ) := ⟨by omega⟩
  have hcard := hζ.card_rootsOfUnity
  rw [show Nat.card (autGroup F W) =
      Nat.card (rootsOfUnity 6 F) from
    Nat.card_congr (autGroupEquivRootsOfUnity6 h2 h3 ha6 ha4)]
  rw [Nat.card_eq_fintype_card, hcard]

end Theorem26_11

end WeierstrassCurve

section Theorem_23_20

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W' : WeierstrassCurve F} [W'.IsShortNF]


theorem shortNF_addX (x₁ x₂ ℓ : F) :
    W'.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
  simp only [addX, IsShortNF.a₁, IsShortNF.a₂]; ring

theorem shortNF_addY (x₁ x₂ y₁ ℓ : F) :
    W'.toAffine.addY x₁ x₂ y₁ ℓ =
      ℓ * (x₁ - W'.toAffine.addX x₁ x₂ ℓ) - y₁ := by
  simp only [addY, negAddY, negY, addX, IsShortNF.a₁, IsShortNF.a₂, IsShortNF.a₃]; ring

variable [DecidableEq F]

omit [W'.IsShortNF] in
theorem shortNF_slope_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W'.toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
  slope_of_X_ne hx

theorem shortNF_slope_of_tangent {x₁ y₁ y₂ : F}
    (hy : y₁ ≠ W'.toAffine.negY x₁ y₂) :
    W'.toAffine.slope x₁ x₁ y₁ y₂ = (3 * x₁ ^ 2 + W'.a₄) / (2 * y₁) := by
  rw [slope_of_Y_ne rfl hy]
  congr 1
  · simp only [IsShortNF.a₂, IsShortNF.a₁]; ring
  · simp only [negY, IsShortNF.a₁, IsShortNF.a₃]; ring

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]
  {W' : WeierstrassCurve F} [W'.IsShortNF]

theorem explicit_chord_formula {x₁ x₂ y₁ y₂ : F}
    (h₁ : W'.toAffine.Nonsingular x₁ y₁) (h₂ : W'.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let ℓ := W'.toAffine.slope x₁ x₂ y₁ y₂
    let x₃ := W'.toAffine.addX x₁ x₂ ℓ
    ∃ h₃ : W'.toAffine.Nonsingular x₃ (W'.toAffine.addY x₁ x₂ y₁ ℓ),
      some _ _ h₁ + some _ _ h₂ = some x₃ (W'.toAffine.addY x₁ x₂ y₁ ℓ) h₃
      ∧ ℓ = (y₁ - y₂) / (x₁ - x₂)
      ∧ x₃ = ℓ ^ 2 - x₁ - x₂
      ∧ W'.toAffine.addY x₁ x₂ y₁ ℓ = ℓ * (x₁ - x₃) - y₁ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W'.toAffine.negY x₂ y₂) := fun h => hx h.1
  exact ⟨nonsingular_add h₁ h₂ hxy,
    add_some hxy,
    shortNF_slope_of_X_ne hx,
    shortNF_addX x₁ x₂ _,
    shortNF_addY x₁ x₂ y₁ _⟩


end WeierstrassCurve.Affine.Point

end Theorem_23_20

section Theorem_23_1

open ArithmeticGeometry

def ArithmeticGeometry.SmoothProjectiveCurve.genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : ℕ := C.genusVal

def ArithmeticGeometry.SmoothProjectiveCurve.HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty C.RatPoint







end Theorem_23_1
