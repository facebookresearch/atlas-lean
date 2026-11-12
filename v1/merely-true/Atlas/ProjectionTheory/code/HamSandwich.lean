/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.BorsukUlam

open MeasureTheory InnerProductSpace Set Filter Topology

namespace HamSandwich

noncomputable section

/-- The open half-space `{x : ⟨v, x⟩ < c} ⊆ ℝⁿ`. -/
def halfSpaceBelow (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪v, x⟫_ℝ < c}

/-- The open half-space `{x : ⟨v, x⟩ > c} ⊆ ℝⁿ`. -/
def halfSpaceAbove (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪v, x⟫_ℝ > c}

/-- A hyperplane with normal `v` and offset `c` *bisects* a set `A ⊆ ℝⁿ` if the two open
half-spaces it defines have equal Lebesgue measure when intersected with `A`. -/
def Bisects (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  volume (A ∩ halfSpaceBelow n v c) = volume (A ∩ halfSpaceAbove n v c)

/-- Given `θ ∈ ℝⁿ⁺¹` (a parameter on the unit sphere), `extractNormal` returns the first
`n` coordinates regarded as the normal vector of a hyperplane in `ℝⁿ`. -/
def extractNormal (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => θ (Fin.castSucc i))

/-- Given `θ ∈ ℝⁿ⁺¹`, `extractOffset` returns its last coordinate, interpreted as the
constant `c` of an affine hyperplane `⟨v, x⟩ = c`. -/
def extractOffset (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  θ (Fin.last n)

/-- The affine functional `x ↦ ⟨extractNormal θ, x⟩ - extractOffset θ` whose sign
determines the two sides of the hyperplane parametrised by `θ ∈ Sⁿ`. -/
def affineFunctional (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪extractNormal n θ, x⟫_ℝ - extractOffset n θ

/-- `extractNormal` is linear in `θ`, in particular it sends negation to negation. -/
lemma extractNormal_neg (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) :
    extractNormal n (-θ) = -extractNormal n θ := by
  simp only [extractNormal, EuclideanSpace.equiv, PiLp.neg_apply]
  ext i; simp [PiLp.neg_apply]

/-- `extractOffset` sends negation to negation. -/
lemma extractOffset_neg (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) :
    extractOffset n (-θ) = -extractOffset n θ := by
  simp [extractOffset, PiLp.neg_apply]

/-- The affine functional is odd in the parameter `θ`: replacing `θ` by `-θ` flips the
sign of `affineFunctional n θ x`. This antipodal symmetry is what allows Borsuk-Ulam to be
applied. -/
lemma affineFunctional_neg (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin n)) :
    affineFunctional n (-θ) x = -affineFunctional n θ x := by
  simp [affineFunctional, extractNormal_neg, extractOffset_neg, inner_neg_left]; ring

/-- `extractNormal` is continuous in its argument. -/
lemma continuous_extractNormal (n : ℕ) : Continuous (extractNormal n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
    (continuous_pi (fun i => PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.castSucc i)))

/-- `extractOffset` is continuous (it is a coordinate projection). -/
lemma continuous_extractOffset (n : ℕ) : Continuous (extractOffset n) :=
  PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.last n)

/-- For fixed `x ∈ ℝⁿ`, the map `θ ↦ affineFunctional n θ x` is continuous at every `θ₀`. -/
lemma continuousAt_affineFunctional (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (θ₀ : EuclideanSpace ℝ (Fin (n + 1))) :
    ContinuousAt (fun θ => affineFunctional n θ x) θ₀ :=
  (((continuous_extractNormal n).inner continuous_const).sub
    (continuous_extractOffset n)).continuousAt

/-- For fixed `θ`, the affine functional `affineFunctional n θ : ℝⁿ → ℝ` is continuous. -/
lemma continuous_affineFunctional_x (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) :
    Continuous (affineFunctional n θ) :=
  (continuous_const.inner continuous_id).sub continuous_const

/-- The positive half-space `{y : affineFunctional n θ y > 0}` is open in `ℝⁿ`. -/
lemma isOpen_halfSpace_pos (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) :
    IsOpen {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0} :=
  isOpen_lt continuous_const (continuous_affineFunctional_x n θ)

/-- If `affineFunctional n θ₀ x ≠ 0`, then the indicator of the positive half-space
evaluated at `x` is continuous in `θ` at `θ₀` (since `x` is in the interior of one side). -/
lemma indicator_halfspace_continuousAt (n : ℕ) (θ₀ : EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : affineFunctional n θ₀ x ≠ 0) :
    ContinuousAt (fun θ => Set.indicator
      {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0}
      (fun _ => (1 : ℝ)) x) θ₀ := by
  rw [ContinuousAt]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [show Set.indicator {y | affineFunctional n θ₀ y > 0} (fun _ => (1 : ℝ)) x = 0 from by
      simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt h))]]
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Iio_mem_nhds h)]
        with θ hθ
      simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt hθ))])
  · rw [show Set.indicator {y | affineFunctional n θ₀ y > 0} (fun _ => (1 : ℝ)) x = 1 from by
      simp only [indicator_apply, mem_setOf_eq, if_pos h]]
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Ioi_mem_nhds h)]
        with θ hθ
      simp only [indicator_apply, mem_setOf_eq, if_pos hθ])

/-- An affine hyperplane `{x : ⟨v, x⟩ = c}` in `ℝⁿ` (with `v ≠ 0`) has Lebesgue measure
zero. -/
lemma hyperplane_measure_zero {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hv : v ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} = 0 := by
  set f := (innerSL (𝕜 := ℝ) v).toLinearMap
  have hfv : ∀ x, f x = ⟪v, x⟫_ℝ := fun x => by simp [f]
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h; apply hv
    have hmem : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hfv, real_inner_self_eq_norm_sq, sq_eq_zero_iff,
      norm_eq_zero] at hmem
    exact hmem
  by_cases hex : ∃ x₀ : EuclideanSpace ℝ (Fin n), ⟪v, x₀⟫_ℝ = c
  · obtain ⟨x₀, hx₀⟩ := hex
    have heq : {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} =
      (x₀ +ᵥ ·) '' (LinearMap.ker f : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      simp only [mem_setOf_eq, mem_image, SetLike.mem_coe, LinearMap.mem_ker, hfv]
      exact ⟨fun hx => ⟨x - x₀, by rw [inner_sub_right]; linarith, by simp [vadd_eq_add]⟩,
        fun ⟨y, hy, hyx⟩ => by rw [← hyx, vadd_eq_add, inner_add_right, hy, add_zero]; exact hx₀⟩
    rw [heq, image_vadd, measure_vadd]
    exact Measure.addHaar_submodule volume _ hker
  · have hempty : {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hx => hex ⟨x, hx⟩
    rw [hempty, measure_empty]

/-- For any nonzero parameter `θ₀ ∈ ℝⁿ⁺¹` and any set `A ⊆ ℝⁿ`, the affine functional is
almost everywhere nonzero on `A` (the zero set is the hyperplane, which has measure zero
when the normal is nonzero, and is empty when the normal is zero but the offset is not). -/
lemma ae_affineFunctional_ne_zero (n : ℕ) (θ₀ : EuclideanSpace ℝ (Fin (n + 1)))
    (hθ : θ₀ ≠ 0) (A : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ᵐ x ∂(volume.restrict A), affineFunctional n θ₀ x ≠ 0 := by
  suffices h : volume {x : EuclideanSpace ℝ (Fin n) | affineFunctional n θ₀ x = 0} = 0 by
    apply ae_restrict_of_ae; rw [ae_iff]; simp only [not_not]
    exact measure_mono_null (fun x hx => hx) h
  have heq : {x : EuclideanSpace ℝ (Fin n) | affineFunctional n θ₀ x = 0} =
    {x | ⟪extractNormal n θ₀, x⟫_ℝ = extractOffset n θ₀} := by
    ext x; simp [affineFunctional, sub_eq_zero]
  rw [heq]
  by_cases hv : extractNormal n θ₀ = 0
  · have hc : extractOffset n θ₀ ≠ 0 := by
      intro hc; apply hθ; ext i
      by_cases hi : i = Fin.last n
      · subst hi; exact hc
      · have hij := Fin.exists_castSucc_eq.mpr hi

        obtain ⟨j, rfl⟩ := hij
        have : (extractNormal n θ₀) j = 0 := by rw [hv]; rfl
        simpa [extractNormal, EuclideanSpace.equiv] using this
    have : {x : EuclideanSpace ℝ (Fin n) | ⟪extractNormal n θ₀, x⟫_ℝ = extractOffset n θ₀} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, hv, inner_zero_left]
      exact fun hx => hc hx.symm
    rw [this, measure_empty]
  · exact hyperplane_measure_zero _ _ hv

/-- For a bounded set `A` and nonzero `θ₀`, the volume of `A ∩ {affineFunctional n θ · > 0}`
(as an integral of the indicator) varies continuously in `θ` at `θ₀`. -/
lemma continuousAt_volume_halfspace (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hBdd : Bornology.IsBounded A) (θ₀ : EuclideanSpace ℝ (Fin (n + 1))) (hθ : θ₀ ≠ 0) :
    ContinuousAt (fun θ : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∫ x in A, Set.indicator {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0}
        (fun _ => (1 : ℝ)) x ∂volume) θ₀ := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (hBdd.measure_lt_top.ne)
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · apply Eventually.of_forall; intro θ
    exact (stronglyMeasurable_const.indicator
      (isOpen_halfSpace_pos n θ).measurableSet).aestronglyMeasurable
  · apply Eventually.of_forall; intro θ
    apply Eventually.of_forall; intro x
    unfold Set.indicator; split_ifs <;> simp
  · exact integrable_const 1
  · exact (ae_affineFunctional_ne_zero n θ₀ hθ A).mono
      (fun x hx => indicator_halfspace_continuousAt n θ₀ x hx)

/-- Same continuity as `continuousAt_volume_halfspace` but for the *negative* half-space. -/
lemma continuousAt_volume_halfspace_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hBdd : Bornology.IsBounded A) (θ₀ : EuclideanSpace ℝ (Fin (n + 1))) (hθ : θ₀ ≠ 0) :
    ContinuousAt (fun θ : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∫ x in A, Set.indicator {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y < 0}
        (fun _ => (1 : ℝ)) x ∂volume) θ₀ := by


  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (hBdd.measure_lt_top.ne)
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · apply Eventually.of_forall; intro θ
    exact (stronglyMeasurable_const.indicator
      (isOpen_lt (continuous_affineFunctional_x n θ) continuous_const).measurableSet).aestronglyMeasurable
  · apply Eventually.of_forall; intro θ
    apply Eventually.of_forall; intro x
    unfold Set.indicator; split_ifs <;> simp
  · exact integrable_const 1
  ·

    apply (ae_affineFunctional_ne_zero n θ₀ hθ A).mono
    intro x hx

    rw [ContinuousAt]
    rcases lt_or_gt_of_ne hx with h | h
    ·
      rw [show Set.indicator {y | affineFunctional n θ₀ y < 0} (fun _ => (1 : ℝ)) x = 1 from by
        simp only [indicator_apply, mem_setOf_eq, if_pos h]]
      exact tendsto_nhds_of_eventually_eq (by
        filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Iio_mem_nhds h)]
          with θ hθ
        simp only [indicator_apply, mem_setOf_eq, if_pos hθ])
    ·
      rw [show Set.indicator {y | affineFunctional n θ₀ y < 0} (fun _ => (1 : ℝ)) x = 0 from by
        simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt h))]]
      exact tendsto_nhds_of_eventually_eq (by
        filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Ioi_mem_nhds h)]
          with θ hθ
        simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt hθ))])

/-- The integral over `A` of the indicator of a measurable set `S` equals the real value
of `volume (A ∩ S)`. -/
lemma integral_indicator_eq_volume {n : ℕ} (A S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : MeasurableSet S) :
    ∫ x in A, S.indicator (fun _ => (1 : ℝ)) x ∂volume = (volume (A ∩ S)).toReal := by
  rw [integral_indicator hS, Measure.restrict_restrict hS, inter_comm]
  simp [Measure.real]


end

end HamSandwich
