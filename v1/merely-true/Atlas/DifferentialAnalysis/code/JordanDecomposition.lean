/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice


/-- The space `C₀(X, ℝ)` of continuous real-valued functions on `X` vanishing at infinity. -/
abbrev C₀Map (X : Type*) [TopologicalSpace X] := ZeroAtInftyContinuousMap X ℝ

namespace ContinuousFunctions

/-- A continuous linear functional `u` on `C₀(X, ℝ)` is positive iff it sends nonnegative
functions to nonnegative real numbers. -/
def IsPositiveFunctional {X : Type*} [TopologicalSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : Prop :=
  ∀ f : C₀Map X, (∀ x, 0 ≤ f x) → 0 ≤ u f

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- Pointwise evaluation of a `C₀` function is bounded by its sup norm. -/
lemma c0_eval_le_norm (f : C₀Map X) (x : X) : |f x| ≤ ‖f‖ := by
  have : ‖f.toBCF x‖ ≤ ‖f.toBCF‖ := BoundedContinuousFunction.norm_coe_le_norm f.toBCF x
  simp only [Real.norm_eq_abs] at this; exact this

/-- Monotonicity of the sup norm on nonnegative `C₀` functions: if `0 ≤ g ≤ f` pointwise then
`‖g‖ ≤ ‖f‖`. -/
lemma c0_norm_le_of_nonneg_le (f g : C₀Map X) (hg0 : ∀ x, 0 ≤ g x)
    (hgf : ∀ x, g x ≤ f x) : ‖g‖ ≤ ‖f‖ := by
  change ‖g.toBCF‖ ≤ ‖f.toBCF‖
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
  intro x; show |g x| ≤ ‖f‖
  rw [abs_of_nonneg (hg0 x)]
  exact le_trans (hgf x) (le_trans (le_abs_self _) (c0_eval_le_norm f x))

/-- The pointwise minimum of two `C₀` functions, again in `C₀(X, ℝ)`. -/
noncomputable def c0min (f g : C₀Map X) : C₀Map X where
  toFun := fun x => min (f x) (g x)
  continuous_toFun := (map_continuous f).min (map_continuous g)
  zero_at_infty' := by
    have := (zero_at_infty f).min (zero_at_infty g)
    simp only [min_self] at this; exact this

/-- For a functional `u` and `f ∈ C₀(X, ℝ)`, the set of values `u g` ranging over `g` with
`0 ≤ g ≤ f` pointwise. The supremum of this set defines the positive part `u⁺(f)`. -/
def posPartSet (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : Set ℝ :=
  {r | ∃ g : C₀Map X, (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ f x) ∧ r = u g}

/-- For nonnegative `f`, the set `posPartSet u f` is nonempty, witnessed by the choice `g = 0`. -/
lemma posPartSet_nonempty (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    (posPartSet u f).Nonempty :=
  ⟨u 0, 0, fun _ => le_refl 0, hf, by simp [map_zero]⟩

/-- The set `posPartSet u f` is bounded above by `‖u‖ * ‖f‖`. -/
lemma posPartSet_bddAbove (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (_hf : ∀ x, 0 ≤ f x) :
    BddAbove (posPartSet u f) := by
  refine ⟨‖u‖ * ‖f‖, fun r ⟨g, hg0, hgf, hr⟩ => ?_⟩; rw [hr]
  calc u g ≤ |u g| := le_abs_self _
    _ = ‖u g‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖u‖ * ‖g‖ := le_opNorm u g
    _ ≤ ‖u‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_left (c0_norm_le_of_nonneg_le f g hg0 hgf) (norm_nonneg u)

/-- The positive part of `u` evaluated at `f`: defined as `sup {u g | 0 ≤ g ≤ f}`. This is the
classical construction used to extract the positive component in the Jordan decomposition. -/
noncomputable def posPartSup (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : ℝ :=
  sSup (posPartSet u f)

/-- For nonnegative `f`, the positive-part supremum is nonnegative. -/
lemma posPartSup_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ posPartSup u f := by
  exact le_csSup (posPartSet_bddAbove u f hf)
    ⟨0, fun _ => le_refl 0, hf, by simp [map_zero]⟩

/-- The positive-part supremum is bounded above by `‖u‖ * ‖f‖`. -/
lemma posPartSup_le_norm_mul (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    posPartSup u f ≤ ‖u‖ * ‖f‖ := by
  exact csSup_le (posPartSet_nonempty u f hf) (fun r ⟨g, hg0, hgf, hr⟩ => by
    rw [hr]
    calc u g ≤ |u g| := le_abs_self _
      _ = ‖u g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u‖ * ‖g‖ := le_opNorm u g
      _ ≤ ‖u‖ * ‖f‖ :=
          mul_le_mul_of_nonneg_left (c0_norm_le_of_nonneg_le f g hg0 hgf) (norm_nonneg u))

/-- The positive-part supremum vanishes at the zero function. -/
lemma posPartSup_zero (u : C₀Map X →L[ℝ] ℝ) :
    posPartSup u 0 = 0 := by
  unfold posPartSup
  have h_set : posPartSet u 0 = {0} := by
    ext r; simp only [posPartSet, Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
    · rintro ⟨g, hg0, hg0', rfl⟩
      have : g = 0 := DFunLike.ext g 0 (fun x => by
        have h1 := hg0 x; have h2 := hg0' x
        simp only [ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply] at h2 ⊢; linarith)
      rw [this, map_zero]
    · rintro rfl
      exact ⟨0, fun _ => le_refl 0, fun _ => le_refl _, by simp [map_zero]⟩
  rw [h_set, csSup_singleton]

/-- Additivity of the positive-part supremum on nonnegative functions: for `f₁, f₂ ≥ 0` we have
`posPartSup u (f₁ + f₂) = posPartSup u f₁ + posPartSup u f₂`. -/
lemma posPartSup_add (u : C₀Map X →L[ℝ] ℝ) (f₁ f₂ : C₀Map X)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x) :
    posPartSup u (f₁ + f₂) = posPartSup u f₁ + posPartSup u f₂ := by
  unfold posPartSup
  apply le_antisymm
  ·
    apply csSup_le (posPartSet_nonempty u (f₁ + f₂) (fun x => add_nonneg (hf₁ x) (hf₂ x)))
    intro r ⟨g, hg0, hgf, hr⟩; rw [hr]
    set g₁ := c0min g f₁
    set g₂ := g - g₁
    have hg₁_0 : ∀ x, 0 ≤ g₁ x := fun x => le_min (hg0 x) (hf₁ x)
    have hg₁_f₁ : ∀ x, g₁ x ≤ f₁ x := fun x => min_le_right _ _
    have hg₂_0 : ∀ x, 0 ≤ g₂ x := fun x =>
      show g x - min (g x) (f₁ x) ≥ 0 from sub_nonneg.mpr (min_le_left _ _)
    have hg₂_f₂ : ∀ x, g₂ x ≤ f₂ x := fun x => by
      show g x - min (g x) (f₁ x) ≤ f₂ x
      have hgfx : g x ≤ f₁ x + f₂ x := hgf x
      rcases le_or_gt (g x) (f₁ x) with h | h
      · simp only [min_eq_left h]; linarith [hf₂ x]
      · simp only [min_eq_right (le_of_lt h)]; linarith
    have hg_eq : u g = u g₁ + u g₂ := by
      have : g = g₁ + g₂ := by
        ext x; show g x = min (g x) (f₁ x) + (g x - min (g x) (f₁ x)); ring
      rw [this, map_add]
    rw [hg_eq]
    exact add_le_add
      (le_csSup (posPartSet_bddAbove u f₁ hf₁) ⟨g₁, hg₁_0, hg₁_f₁, rfl⟩)
      (le_csSup (posPartSet_bddAbove u f₂ hf₂) ⟨g₂, hg₂_0, hg₂_f₂, rfl⟩)
  ·
    rw [← csSup_add (posPartSet_nonempty u f₁ hf₁) (posPartSet_bddAbove u f₁ hf₁)
                     (posPartSet_nonempty u f₂ hf₂) (posPartSet_bddAbove u f₂ hf₂)]
    apply csSup_le_csSup
      (posPartSet_bddAbove u (f₁ + f₂) (fun x => add_nonneg (hf₁ x) (hf₂ x)))
      ((posPartSet_nonempty u f₁ hf₁).add (posPartSet_nonempty u f₂ hf₂))
    intro r hr
    rw [Set.mem_add] at hr
    obtain ⟨r₁, hr₁, r₂, hr₂, hrr⟩ := hr
    obtain ⟨g₁, hg₁0, hg₁f₁, hrg₁⟩ := hr₁
    obtain ⟨g₂, hg₂0, hg₂f₂, hrg₂⟩ := hr₂
    exact ⟨g₁ + g₂,
      fun x => add_nonneg (hg₁0 x) (hg₂0 x),
      fun x => show g₁ x + g₂ x ≤ f₁ x + f₂ x from add_le_add (hg₁f₁ x) (hg₂f₂ x),
      by rw [← hrr, hrg₁, hrg₂, map_add]⟩

/-- Homogeneity of `posPartSup` under multiplication by a positive scalar. -/
lemma posPartSup_smul_pos (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x)
    (c : ℝ) (hc : 0 < c) :
    posPartSup u (c • f) = c * posPartSup u f := by
  unfold posPartSup
  have h_eq : posPartSet u (c • f) = (fun r => c * r) '' posPartSet u f := by
    ext r; constructor
    · rintro ⟨g, hg0, hgcf, rfl⟩
      refine ⟨u (c⁻¹ • g), ⟨c⁻¹ • g, fun x => ?_, fun x => ?_, rfl⟩, ?_⟩
      · show c⁻¹ * g x ≥ 0; exact mul_nonneg (inv_nonneg.mpr hc.le) (hg0 x)
      · show c⁻¹ * g x ≤ f x; rw [inv_mul_le_iff₀ hc]; exact hgcf x
      · show (fun r => c * r) (u (c⁻¹ • g)) = u g
        simp only; rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨h, hh0, hhf, rfl⟩, rfl⟩
      refine ⟨c • h, fun x => ?_, fun x => ?_, ?_⟩
      · show c * h x ≥ 0; exact mul_nonneg hc.le (hh0 x)
      · show c * h x ≤ c * f x; exact mul_le_mul_of_nonneg_left (hhf x) hc.le
      · rw [map_smul, smul_eq_mul]
  rw [h_eq]
  symm; exact Monotone.map_csSup_of_continuousAt
    (continuous_const.mul continuous_id |>.continuousAt)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hc.le)
    (posPartSet_nonempty u f hf)
    (posPartSet_bddAbove u f hf)

/-- Homogeneity of `posPartSup` under multiplication by a nonnegative scalar. -/
lemma posPartSup_smul_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X)
    (hf : ∀ x, 0 ≤ f x) (c : ℝ) (hc : 0 ≤ c) :
    posPartSup u (c • f) = c * posPartSup u f := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp only [zero_smul, zero_mul, posPartSup_zero]
  · exact posPartSup_smul_pos u f hf c hc_pos

/-- Well-definedness of the positive part on signed decompositions: if `f = h₁ - h₂` with
`h₁, h₂ ≥ 0`, then `posPartSup u f⁺ - posPartSup u f⁻ = posPartSup u h₁ - posPartSup u h₂`. -/
lemma posPartSup_well_defined (u : C₀Map X →L[ℝ] ℝ) (f h₁ h₂ : C₀Map X)
    (hh₁ : ∀ x, 0 ≤ h₁ x) (hh₂ : ∀ x, 0 ≤ h₂ x) (hf : f = h₁ - h₂) :
    posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) =
    posPartSup u h₁ - posPartSup u h₂ := by

  have hkey : ∀ x, zeroAtInftyPosPart f x + h₂ x = h₁ x + zeroAtInftyNegPart f x := by
    intro x
    simp only [posPart_apply, negPart_apply]
    have hfx : f x = h₁ x - h₂ x := by
      have := DFunLike.congr_fun hf x
      simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] at this; exact this
    rw [hfx]
    rcases le_or_gt (h₁ x - h₂ x) 0 with hle | hgt
    · rw [max_eq_right hle, zero_add, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith), add_zero]; ring

  have heq_fn : zeroAtInftyPosPart f + h₂ = h₁ + zeroAtInftyNegPart f := by
    ext x; exact hkey x

  have h1 := posPartSup_add u (zeroAtInftyPosPart f) h₂ (posPart_nonneg f) hh₂
  have h2 := posPartSup_add u h₁ (zeroAtInftyNegPart f) hh₁ (negPart_nonneg f)
  rw [heq_fn] at h1
  linarith

/-- The positive-part functional extended to arbitrary (signed) `C₀` functions via the
decomposition `f = f⁺ - f⁻`. -/
noncomputable def posPartFn (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : ℝ :=
  posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f)

/-- Additivity of `posPartFn` on arbitrary `C₀` functions. -/
lemma posPartFn_add (u : C₀Map X →L[ℝ] ℝ) (f g : C₀Map X) :
    posPartFn u (f + g) = posPartFn u f + posPartFn u g := by
  unfold posPartFn

  have h_decomp : f + g = (zeroAtInftyPosPart f + zeroAtInftyPosPart g) -
      (zeroAtInftyNegPart f + zeroAtInftyNegPart g) := by
    conv_lhs => rw [decompose_pos_neg f, decompose_pos_neg g]
    ext x; simp only [ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_sub,
      Pi.add_apply, Pi.sub_apply]; ring

  rw [posPartSup_well_defined u (f + g)
    (zeroAtInftyPosPart f + zeroAtInftyPosPart g)
    (zeroAtInftyNegPart f + zeroAtInftyNegPart g)
    (fun x => add_nonneg (posPart_nonneg f x) (posPart_nonneg g x))
    (fun x => add_nonneg (negPart_nonneg f x) (negPart_nonneg g x))
    h_decomp]
  rw [posPartSup_add u _ _ (posPart_nonneg f) (posPart_nonneg g)]
  rw [posPartSup_add u _ _ (negPart_nonneg f) (negPart_nonneg g)]
  ring

/-- Homogeneity of `posPartFn` under multiplication by a nonnegative scalar. -/
lemma posPartFn_smul_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) (hc : 0 ≤ c) :
    posPartFn u (c • f) = c * posPartFn u f := by
  unfold posPartFn

  have hpos : zeroAtInftyPosPart (c • f) = c • zeroAtInftyPosPart f := by
    ext x; simp only [posPart_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rcases le_or_gt (f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc h.le)]
      rw [max_eq_left h.le]
  have hneg : zeroAtInftyNegPart (c • f) = c • zeroAtInftyNegPart f := by
    ext x; simp only [negPart_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show -(c * f x) = c * (-f x) by ring]
    rcases le_or_gt (-f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc h.le)]
      rw [max_eq_left h.le]
  rw [hpos, hneg]
  rw [posPartSup_smul_nonneg u _ (posPart_nonneg f) c hc]
  rw [posPartSup_smul_nonneg u _ (negPart_nonneg f) c hc]
  ring

/-- Homogeneity of `posPartFn` under multiplication by a negative scalar (using the symmetry
between positive and negative parts under negation). -/
lemma posPartFn_smul_neg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) (hc : c < 0) :
    posPartFn u (c • f) = c * posPartFn u f := by
  unfold posPartFn

  have hpos : zeroAtInftyPosPart (c • f) = (-c) • zeroAtInftyNegPart f := by
    ext x; simp only [posPart_apply, negPart_apply, ZeroAtInftyContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [show c * f x = (-c) * (-f x) by ring]
    have hc' : 0 ≤ -c := neg_nonneg.mpr hc.le
    rcases le_or_gt (-f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc' h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc' h.le)]
      rw [max_eq_left h.le]
  have hneg : zeroAtInftyNegPart (c • f) = (-c) • zeroAtInftyPosPart f := by
    ext x; simp only [negPart_apply, posPart_apply, ZeroAtInftyContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [show -(c * f x) = (-c) * f x by ring]
    have hc' : 0 ≤ -c := neg_nonneg.mpr hc.le
    rcases le_or_gt (f x) 0 with h | h
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc' h)]
      rw [max_eq_right h]; ring
    · rw [max_eq_left (mul_nonneg hc' h.le)]
      rw [max_eq_left h.le]
  rw [hpos, hneg]
  rw [posPartSup_smul_nonneg u _ (negPart_nonneg f) (-c) (neg_nonneg.mpr hc.le)]
  rw [posPartSup_smul_nonneg u _ (posPart_nonneg f) (-c) (neg_nonneg.mpr hc.le)]
  ring

/-- Full ℝ-linearity of `posPartFn` in the scalar argument. -/
lemma posPartFn_smul (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (c : ℝ) :
    posPartFn u (c • f) = c * posPartFn u f := by
  rcases le_or_gt 0 c with hc | hc
  · exact posPartFn_smul_nonneg u f c hc
  · exact posPartFn_smul_neg u f c hc

/-- Operator-norm bound for the positive part functional: `‖posPartFn u f‖ ≤ ‖u‖ * ‖f‖`. -/
lemma posPartFn_bound (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) :
    ‖posPartFn u f‖ ≤ ‖u‖ * ‖f‖ := by
  unfold posPartFn
  rw [Real.norm_eq_abs]
  have h1 := posPartSup_le_norm_mul u (zeroAtInftyPosPart f) (posPart_nonneg f)
  have h2 := posPartSup_le_norm_mul u (zeroAtInftyNegPart f) (negPart_nonneg f)
  have h3 := posPartSup_nonneg u (zeroAtInftyPosPart f) (posPart_nonneg f)
  have h4 := posPartSup_nonneg u (zeroAtInftyNegPart f) (negPart_nonneg f)

  rw [abs_le]
  have hfp_le : ‖zeroAtInftyPosPart f‖ ≤ ‖f‖ := by
    change ‖(zeroAtInftyPosPart f).toBCF‖ ≤ ‖f.toBCF‖
    rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
    intro x
    calc |zeroAtInftyPosPart f x| = zeroAtInftyPosPart f x :=
            abs_of_nonneg (posPart_nonneg f x)
      _ ≤ |f x| := posPart_le_abs f x
      _ ≤ ‖f‖ := c0_eval_le_norm f x
  have hfn_le : ‖zeroAtInftyNegPart f‖ ≤ ‖f‖ := by
    change ‖(zeroAtInftyNegPart f).toBCF‖ ≤ ‖f.toBCF‖
    rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
    intro x
    calc |zeroAtInftyNegPart f x| = zeroAtInftyNegPart f x :=
            abs_of_nonneg (negPart_nonneg f x)
      _ ≤ |f x| := negPart_le_abs f x
      _ ≤ ‖f‖ := c0_eval_le_norm f x
  have h1' : posPartSup u (zeroAtInftyPosPart f) ≤ ‖u‖ * ‖f‖ :=
    le_trans h1 (mul_le_mul_of_nonneg_left hfp_le (norm_nonneg u))
  have h2' : posPartSup u (zeroAtInftyNegPart f) ≤ ‖u‖ * ‖f‖ :=
    le_trans h2 (mul_le_mul_of_nonneg_left hfn_le (norm_nonneg u))
  constructor <;> linarith

/-- The positive part of a continuous linear functional `u` packaged as a linear map. -/
noncomputable def posPartLinearMap (u : C₀Map X →L[ℝ] ℝ) : C₀Map X →ₗ[ℝ] ℝ where
  toFun := posPartFn u
  map_add' := posPartFn_add u
  map_smul' c f := by
    simp only [posPartFn_smul, smul_eq_mul, RingHom.id_apply]

/-- The positive part of a continuous linear functional `u` on `C₀(X, ℝ)`, packaged as a CLM. -/
noncomputable def posPartCLM {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : C₀Map X →L[ℝ] ℝ :=
  (posPartLinearMap u).mkContinuous ‖u‖ (fun f => posPartFn_bound u f)

/-- The CLM `posPartCLM u` agrees with the function `posPartFn u`. -/
lemma posPartCLM_apply (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) :
    posPartCLM u f = posPartFn u f := by
  show (posPartLinearMap u).mkContinuous ‖u‖ _ f = posPartFn u f
  rw [LinearMap.mkContinuous_apply]
  rfl

/-- The positive part `posPartCLM u` is a positive linear functional on `C₀(X, ℝ)`. -/
theorem posPartCLM_positive {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : IsPositiveFunctional (posPartCLM u) := by
  intro f hf
  rw [posPartCLM_apply]
  unfold posPartFn

  have hpos : zeroAtInftyPosPart f = f := by
    ext x; simp [posPart_apply, max_eq_left (hf x)]
  have hneg : zeroAtInftyNegPart f = 0 := by
    ext x; simp [negPart_apply, max_eq_right (by linarith [hf x] : -f x ≤ 0)]
  rw [hpos, hneg, posPartSup_zero]
  linarith [posPartSup_nonneg u f hf]

/-- For nonnegative `f`, the value `u f` is dominated by the positive part `posPartCLM u f`. -/
theorem posPartCLM_ge {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    u f ≤ posPartCLM u f := by
  rw [posPartCLM_apply]
  unfold posPartFn
  have hpos : zeroAtInftyPosPart f = f := by
    ext x; simp [posPart_apply, max_eq_left (hf x)]
  have hneg : zeroAtInftyNegPart f = 0 := by
    ext x; simp [negPart_apply, max_eq_right (by linarith [hf x] : -f x ≤ 0)]
  rw [hpos, hneg, posPartSup_zero, sub_zero]

  exact le_csSup (posPartSet_bddAbove u f hf)
    ⟨f, hf, fun _ => le_refl _, rfl⟩

/-- The operator norm of the positive part is bounded by the operator norm of `u`. -/
theorem norm_posPartCLM_le {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : ‖posPartCLM u‖ ≤ ‖u‖ := by
  exact LinearMap.mkContinuous_norm_le (posPartLinearMap u) (norm_nonneg u) _

/-- The operator norm of the negative part `posPartCLM u - u` is bounded by the operator norm
of `u`. -/
theorem norm_negPart_le {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : ‖posPartCLM u - u‖ ≤ ‖u‖ := by


  apply opNorm_le_bound _ (norm_nonneg u)
  intro f
  rw [ContinuousLinearMap.sub_apply, posPartCLM_apply]
  unfold posPartFn
  rw [Real.norm_eq_abs]


  have hf_decomp : u f = u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f) := by
    have := decompose_pos_neg f
    conv_lhs => rw [this]
    rw [map_sub]
  rw [hf_decomp]


  have key : ∀ (g : C₀Map X), (∀ x, 0 ≤ g x) →
      posPartSup u g - u g = posPartSup (-u) g := by
    intro g hg
    unfold posPartSup


    have h_shift : sSup (posPartSet u g) - u g =
        sSup ((fun r => r - u g) '' posPartSet u g) := by
      have := Monotone.map_csSup_of_continuousAt (f := fun r => r - u g)
        ((continuous_id.sub continuous_const).continuousAt)
        (fun _ _ h => sub_le_sub_right h _)
        (posPartSet_nonempty u g hg)
        (posPartSet_bddAbove u g hg)
      exact this
    rw [h_shift]
    congr 1
    ext r; constructor
    · rintro ⟨s, ⟨h, hh0, hhg, rfl⟩, rfl⟩

      refine ⟨g - h, fun x => ?_, fun x => ?_, ?_⟩
      · show g x - h x ≥ 0; linarith [hhg x]
      · show g x - h x ≤ g x; linarith [hh0 x]
      · show u h - u g = (-u) (g - h)
        simp only [ContinuousLinearMap.neg_apply, map_sub]; ring
    · rintro ⟨k, hk0, hkg, rfl⟩

      refine ⟨u (g - k), ⟨g - k, fun x => ?_, fun x => ?_, rfl⟩, ?_⟩
      · show g x - k x ≥ 0; linarith [hkg x]
      · show g x - k x ≤ g x; linarith [hk0 x]
      · simp only [ContinuousLinearMap.neg_apply, map_sub]; ring

  have hkey1 := key (zeroAtInftyPosPart f) (posPart_nonneg f)
  have hkey2 := key (zeroAtInftyNegPart f) (negPart_nonneg f)


  show |posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) -
    (u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f))| ≤ ‖u‖ * ‖f‖
  rw [show posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) -
    (u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f)) =
    (posPartSup u (zeroAtInftyPosPart f) - u (zeroAtInftyPosPart f)) -
    (posPartSup u (zeroAtInftyNegPart f) - u (zeroAtInftyNegPart f)) by ring]
  rw [hkey1, hkey2]


  calc |posPartSup (-u) (zeroAtInftyPosPart f) - posPartSup (-u) (zeroAtInftyNegPart f)|
      = ‖posPartFn (-u) f‖ := by unfold posPartFn; rw [Real.norm_eq_abs]
    _ ≤ ‖-u‖ * ‖f‖ := posPartFn_bound (-u) f
    _ = ‖u‖ * ‖f‖ := by congr 1; exact norm_neg u

end PosPartConstruction

/-- Lemma 1.5 (Jordan decomposition for `C₀` functionals): every continuous linear functional
`u : C₀(X, ℝ) →L[ℝ] ℝ` decomposes as a difference `u = u₊ - u₋` of two positive linear
functionals whose operator norms are bounded by `‖u‖`. -/
theorem dual_jordan_decomposition
    {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) :
    ∃ u_pos u_neg : C₀Map X →L[ℝ] ℝ,
      IsPositiveFunctional u_pos ∧ IsPositiveFunctional u_neg ∧
      u = u_pos - u_neg ∧ ‖u_pos‖ ≤ ‖u‖ ∧ ‖u_neg‖ ≤ ‖u‖ := by
  refine ⟨posPartCLM u, posPartCLM u - u,
    posPartCLM_positive u, ?_, ?_, norm_posPartCLM_le u, norm_negPart_le u⟩
  ·
    intro f hf
    simp only [ContinuousLinearMap.sub_apply]
    linarith [posPartCLM_ge u f hf]
  ·
    ext f
    simp only [ContinuousLinearMap.sub_apply]
    ring

end ContinuousFunctions
