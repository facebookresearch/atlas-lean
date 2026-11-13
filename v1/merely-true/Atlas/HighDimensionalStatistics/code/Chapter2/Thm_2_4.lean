/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_16
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6

open Matrix MeasureTheory Real ProbabilityTheory ENNReal Finset Set Pointwise

noncomputable section

/-- Monotonicity of the sub-Gaussian property in the variance proxy: if `f` is
sub-Gaussian with variance proxy `σ²₁` and `σ²₁ ≤ σ²₂`, then `f` is also
sub-Gaussian with the larger proxy `σ²₂`. -/
theorem IsSubGaussian.mono_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {σsq₁ σsq₂ : ℝ} (h : IsSubGaussian f σsq₁ μ) (hle : σsq₁ ≤ σsq₂) :
    IsSubGaussian f σsq₂ μ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun s => ?_⟩
  calc ∫ ω, exp (s * f ω) ∂μ
      ≤ exp (σsq₁ * s ^ 2 / 2) := h.2.2.2 s
    _ ≤ exp (σsq₂ * s ^ 2 / 2) := by
        apply exp_le_exp_of_le
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hle (sq_nonneg s)
        · positivity

namespace Rigollet.Chapter2

/-- Fundamental inequality for constrained least squares: if `θ*` lies in the
constraint set `K` and `θ̂` is the constrained least squares estimator, then
`‖X(θ̂ - θ*)‖² ≤ 2⟨ε, X(θ̂ - θ*)⟩`. -/
theorem constrained_fundamental_inequality
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Fin n → ℝ)
    (θhat : Fin d → ℝ)
    (K : Set (Fin d → ℝ))
    (hθstar_in_K : θstar ∈ K)
    (hLS : ∀ θ ∈ K,
      dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θhat) ((X *ᵥ θstar + ε) - X *ᵥ θhat) ≤
      dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θ) ((X *ᵥ θstar + ε) - X *ᵥ θ)) :
    dotProduct (X *ᵥ (θhat - θstar)) (X *ᵥ (θhat - θstar)) ≤
      2 * dotProduct ε (X *ᵥ (θhat - θstar)) := by

  have h1 := hLS θstar hθstar_in_K
  have heps : (X *ᵥ θstar + ε) - X *ᵥ θstar = ε := by
    simp [add_sub_cancel_left]
  rw [heps] at h1

  set v := X *ᵥ (θhat - θstar) with hv_def
  have hresid : (X *ᵥ θstar + ε) - X *ᵥ θhat = ε - v := by
    rw [hv_def, mulVec_sub]; ext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  rw [hresid] at h1

  rw [dotProduct_sub_expand] at h1
  linarith

/-- Polytope sub-Gaussian tail bound: probability that a linear functional `g`
exceeds `t` over the convex hull of a finite set `S` of sub-Gaussian directions
is at most `|S| · exp(-t²/(2σ²))`. Specialisation of Theorem 1.16. -/
theorem thm_2_4_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g : Ω → ((Fin n → ℝ) →ₗ[ℝ] ℝ)) (S : Finset (Fin n → ℝ)) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set (Fin n → ℝ)), g ω θ > t} ≤
    S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
  theorem_1_16_polytope_subgaussian g S hsg t ht

/-- Deterministic step in Theorem 2.4: for a symmetric convex constraint set
`K` containing `θ*`, the prediction error of the constrained LS estimator is
controlled by `4 · sup_{θ ∈ K} ⟨ε, Xθ⟩`. -/
theorem thm_2_4_deterministic_bound
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Fin n → ℝ)
    (θhat : Fin d → ℝ)
    (K : Set (Fin d → ℝ))
    (hθstar_in_K : θstar ∈ K)
    (hθhat_in_K : θhat ∈ K)

    (hK_symm : ∀ θ, θ ∈ K ↔ -θ ∈ K)

    (hK_convex : Convex ℝ K)
    (hLS : ∀ θ ∈ K,
      dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θhat) ((X *ᵥ θstar + ε) - X *ᵥ θhat) ≤
      dotProduct ((X *ᵥ θstar + ε) - X *ᵥ θ) ((X *ᵥ θstar + ε) - X *ᵥ θ))
    (hbdd : BddAbove (Set.image (fun θ => dotProduct ε (X *ᵥ θ)) K)) :
    dotProduct (X *ᵥ (θhat - θstar)) (X *ᵥ (θhat - θstar)) ≤
      4 * sSup (Set.image (fun θ => dotProduct ε (X *ᵥ θ)) K) := by


  have h_basic := constrained_fundamental_inequality X θstar ε θhat K hθstar_in_K hLS


  have h_neg_θstar : -θstar ∈ K := (hK_symm θstar).mp hθstar_in_K
  have h_midpoint : (1/2 : ℝ) • θhat + (1/2 : ℝ) • (-θstar) ∈ K := by
    apply hK_convex hθhat_in_K h_neg_θstar
    · linarith
    · linarith
    · norm_num
  have h_mid_eq : (1/2 : ℝ) • θhat + (1/2 : ℝ) • (-θstar) = (1/2 : ℝ) • (θhat - θstar) := by
    ext i; simp [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring
  rw [h_mid_eq] at h_midpoint

  have h_dot_half : dotProduct ε (X *ᵥ (θhat - θstar)) =
      2 * dotProduct ε (X *ᵥ ((1/2 : ℝ) • (θhat - θstar))) := by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
    ring

  have h_le_sup : dotProduct ε (X *ᵥ ((1/2 : ℝ) • (θhat - θstar))) ≤
      sSup (Set.image (fun θ => dotProduct ε (X *ᵥ θ)) K) :=
    le_csSup hbdd (Set.mem_image_of_mem _ h_midpoint)
  linarith

/-- Linear combinations of independent sub-Gaussian coordinates remain
sub-Gaussian: if each `ε_i` is sub-Gaussian with variance proxy `σ²` and
`∑ a_i² ≤ C`, then `⟨ε, a⟩` is sub-Gaussian with variance proxy `C · σ²`. -/
theorem subgaussian_dotProduct_column
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ε : Ω → (Fin n → ℝ)) (σsq : ℝ) (hσsq : 0 ≤ σsq)
    (hmeas : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) σsq μ)
    (a : Fin n → ℝ) (C : ℝ) (hC : ∑ i, (a i) ^ 2 ≤ C) :
    IsSubGaussian (fun ω => dotProduct (ε ω) a) (C * σsq) μ := by
  have h16 := theorem_1_6_subgaussian_vector (X := fun i (ω : Ω) => ε ω i)
    hε hindep hmeas a
  have heq : (fun ω => ∑ i : Fin n, a i * ε ω i) = (fun ω => dotProduct (ε ω) a) := by
    ext ω; simp only [dotProduct]; congr 1; ext i; ring
  rw [heq] at h16
  exact IsSubGaussian.mono_variance h16 (by nlinarith [mul_le_mul_of_nonneg_right hC hσsq])

/-- Tail bound for the supremum of `⟨ε, Xθ⟩` over the `ℓ¹`-ball of radius `R`,
under column-normalisation `∑_i X_{ij}² ≤ n`:
`μ{∃ θ, ‖θ‖₁ ≤ R, ⟨ε, Xθ⟩ > t} ≤ 2d · exp(-t²/(2 n σ² R²))`. -/
theorem subgaussian_l1_ball_tail
    {n d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ) (R : ℝ) (hR : 0 < R)
    (hcol : ∀ j : Fin d, ∑ i : Fin n, (X i j) ^ 2 ≤ (n : ℝ))
    (ε : Ω → (Fin n → ℝ)) (σ : ℝ) (hσ : 0 < σ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hmeas_ε : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep_ε : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧
      dotProduct (ε ω) (X *ᵥ θ) > t} ≤
    ENNReal.ofReal ((2 * d) * exp (-(t ^ 2 / (2 * ↑n * σ ^ 2 * R ^ 2)))) := by

  let g : Ω → ((Fin n → ℝ) →ₗ[ℝ] ℝ) := fun ω => {
    toFun := fun v => dotProduct (ε ω) v
    map_add' := fun v w => dotProduct_add _ v w
    map_smul' := fun c v => by simp [dotProduct_smul, smul_eq_mul]
  }
  let col : Fin d → (Fin n → ℝ) := fun j i => R * X i j
  let S_pos : Finset (Fin n → ℝ) := Finset.univ.image col
  let S_neg : Finset (Fin n → ℝ) := Finset.univ.image (fun j => -col j)
  let S : Finset (Fin n → ℝ) := S_pos ∪ S_neg

  have hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) (↑n * σ ^ 2 * R ^ 2) μ := by
    intro v hv

    have hv' : v ∈ S_pos ∨ v ∈ S_neg := Finset.mem_union.mp hv
    rcases hv' with hpos | hneg
    ·
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpos
      show IsSubGaussian (fun ω => dotProduct (ε ω) (col j)) (↑n * σ ^ 2 * R ^ 2) μ
      have hcol_sq : ∑ i, (col j i) ^ 2 ≤ ↑n * R ^ 2 := by
        show ∑ i, (R * X i j) ^ 2 ≤ ↑n * R ^ 2
        simp only [mul_pow]
        rw [← Finset.mul_sum]
        calc R ^ 2 * ∑ i, X i j ^ 2 ≤ R ^ 2 * ↑n :=
              mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg R)
          _ = ↑n * R ^ 2 := by ring
      have h := subgaussian_dotProduct_column ε (σ ^ 2) (sq_nonneg σ)
        hmeas_ε hindep_ε hε (col j) (↑n * R ^ 2) hcol_sq
      have : ↑n * R ^ 2 * σ ^ 2 = ↑n * σ ^ 2 * R ^ 2 := by ring
      rwa [this] at h
    ·
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hneg
      show IsSubGaussian (fun ω => dotProduct (ε ω) (-col j)) (↑n * σ ^ 2 * R ^ 2) μ
      have hcol_sq : ∑ i, ((-col j) i) ^ 2 ≤ ↑n * R ^ 2 := by
        show ∑ i, (-(R * X i j)) ^ 2 ≤ ↑n * R ^ 2
        simp only [neg_sq, mul_pow]
        rw [← Finset.mul_sum]
        calc R ^ 2 * ∑ i, X i j ^ 2 ≤ R ^ 2 * ↑n :=
              mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg R)
          _ = ↑n * R ^ 2 := by ring
      have h := subgaussian_dotProduct_column ε (σ ^ 2) (sq_nonneg σ)
        hmeas_ε hindep_ε hε (-col j) (↑n * R ^ 2) hcol_sq
      have : ↑n * R ^ 2 * σ ^ 2 = ↑n * σ ^ 2 * R ^ 2 := by ring
      rwa [this] at h


  have h_subset : {ω | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧ dotProduct (ε ω) (X *ᵥ θ) > t} ⊆
      {ω | ∃ v ∈ convexHull ℝ (↑S : Set (Fin n → ℝ)), g ω v > t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    obtain ⟨θ, hθ_l1, hθ_gt⟩ := hω
    refine ⟨X *ᵥ θ, ?_, hθ_gt⟩


    let w' : Option (Fin d) → ℝ := fun
      | some j => |θ j| / R
      | none => 1 - ∑ j, |θ j| / R
    let z' : Option (Fin d) → (Fin n → ℝ) := fun
      | some j => if 0 ≤ θ j then col j else -col j
      | none => 0
    have hR' : R ≠ 0 := ne_of_gt hR
    have hRle : (0 : ℝ) ≤ R := le_of_lt hR
    have hsum_le : ∑ j : Fin d, |θ j| / R ≤ 1 := by
      rw [← Finset.sum_div]; exact div_le_one_of_le₀ hθ_l1 hRle
    have heq : X *ᵥ θ = ∑ i : Option (Fin d), w' i • z' i := by
      rw [Fintype.sum_option]
      simp only [w', z', smul_zero, zero_add]
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
      congr 1; ext j
      split_ifs with h
      · simp only [col, abs_of_nonneg h]; field_simp
      · push Not at h; simp only [col, Pi.neg_apply, abs_of_neg h]; field_simp
    rw [heq]
    apply Convex.sum_mem (convex_convexHull ℝ _)
    · intro i _
      match i with
      | some j => exact div_nonneg (abs_nonneg _) hRle
      | none => linarith [hsum_le]
    · rw [Fintype.sum_option]; simp only [w']; linarith
    · intro i _
      match i with
      | none =>
        simp only [z']
        have hd' : 0 < d := by omega
        let j₀ : Fin d := ⟨0, hd'⟩
        have hcol_in : col j₀ ∈ (↑S : Set (Fin n → ℝ)) :=
          Finset.mem_coe.mpr (Finset.mem_union_left _
            (Finset.mem_image_of_mem col (Finset.mem_univ j₀)))
        have hncol_in : -col j₀ ∈ (↑S : Set (Fin n → ℝ)) :=
          Finset.mem_coe.mpr (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ j₀)))
        rw [show (0 : Fin n → ℝ) = midpoint ℝ (col j₀) (-col j₀)
            from (midpoint_self_neg ℝ (col j₀)).symm]
        exact (convex_convexHull ℝ _).midpoint_mem
          (subset_convexHull ℝ _ hcol_in) (subset_convexHull ℝ _ hncol_in)
      | some j =>
        simp only [z']
        split_ifs
        · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_left _ (Finset.mem_image_of_mem col (Finset.mem_univ j))))
        · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

  have h_thm116 := theorem_1_16_polytope_subgaussian' g S hsg t ht

  have hS_card : (S.card : ℝ) ≤ 2 * ↑d := by
    have h1 : S.card ≤ S_pos.card + S_neg.card := Finset.card_union_le S_pos S_neg
    have h2 : S_pos.card ≤ d := Finset.card_image_le.trans (by simp)
    have h3 : S_neg.card ≤ d := Finset.card_image_le.trans (by simp)
    have h4 : S.card ≤ 2 * d := by omega
    exact_mod_cast h4
  calc μ {ω | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧ dotProduct (ε ω) (X *ᵥ θ) > t}
      ≤ μ {ω | ∃ v ∈ convexHull ℝ (↑S : Set (Fin n → ℝ)), g ω v > t} :=
        measure_mono h_subset
    _ ≤ ENNReal.ofReal (↑S.card * exp (-(t ^ 2 / (2 * (↑n * σ ^ 2 * R ^ 2))))) :=
        h_thm116
    _ ≤ ENNReal.ofReal ((2 * ↑d) * exp (-(t ^ 2 / (2 * ↑n * σ ^ 2 * R ^ 2)))) := by
        apply ENNReal.ofReal_le_ofReal
        have hassoc : 2 * (↑n * σ ^ 2 * R ^ 2) = 2 * ↑n * σ ^ 2 * R ^ 2 := by ring
        rw [hassoc]
        exact mul_le_mul_of_nonneg_right hS_card (le_of_lt (exp_pos _))

/-- Expectation bound for the supremum of `⟨ε, Xθ⟩` over the `ℓ¹`-ball of
radius `R`, under column-normalisation `∑_i X_{ij}² ≤ n`:
`E[sup_{‖θ‖₁ ≤ R} ⟨ε, Xθ⟩] ≤ σ R √n · √(2 log(2d))`. -/
theorem subgaussian_l1_ball_expectation
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ) (R : ℝ) (hR : 0 < R)
    (hcol : ∀ j : Fin d, ∑ i : Fin n, (X i j) ^ 2 ≤ (n : ℝ))
    (ε : Ω → (Fin n → ℝ)) (σ : ℝ) (hσ : 0 < σ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hmeas_ε : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep_ε : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)
    (hmeas_sup : Measurable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)})) :
    ∫ ω, sSup {v | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧
      v = dotProduct (ε ω) (X *ᵥ θ)} ∂μ ≤
    σ * R * Real.sqrt (↑n) * Real.sqrt (2 * Real.log (2 * ↑d)) := by

  let g : Ω → ((Fin n → ℝ) →ₗ[ℝ] ℝ) := fun ω => {
    toFun := fun v => dotProduct (ε ω) v
    map_add' := fun v w => dotProduct_add _ v w
    map_smul' := fun c v => by simp [dotProduct_smul, smul_eq_mul]
  }
  let col : Fin d → (Fin n → ℝ) := fun j i => R * X i j
  let S_pos : Finset (Fin n → ℝ) := Finset.univ.image col
  let S_neg : Finset (Fin n → ℝ) := Finset.univ.image (fun j => -col j)
  let S : Finset (Fin n → ℝ) := S_pos ∪ S_neg
  have hd' : 0 < d := by omega
  have hS_ne : S.Nonempty := by
    apply Finset.Nonempty.mono (Finset.subset_union_left)
    exact ⟨col ⟨0, hd'⟩, Finset.mem_image_of_mem col (Finset.mem_univ _)⟩

  have hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) (↑n * σ ^ 2 * R ^ 2) μ := by
    intro v hv
    have hv' : v ∈ S_pos ∨ v ∈ S_neg := Finset.mem_union.mp hv
    rcases hv' with hpos | hneg
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpos
      show IsSubGaussian (fun ω => dotProduct (ε ω) (col j)) (↑n * σ ^ 2 * R ^ 2) μ
      have hcol_sq : ∑ i, (col j i) ^ 2 ≤ ↑n * R ^ 2 := by
        show ∑ i, (R * X i j) ^ 2 ≤ ↑n * R ^ 2
        simp only [mul_pow]; rw [← Finset.mul_sum]
        calc R ^ 2 * ∑ i, X i j ^ 2 ≤ R ^ 2 * ↑n :=
              mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg R)
          _ = ↑n * R ^ 2 := by ring
      have h := subgaussian_dotProduct_column ε (σ ^ 2) (sq_nonneg σ)
        hmeas_ε hindep_ε hε (col j) (↑n * R ^ 2) hcol_sq
      have : ↑n * R ^ 2 * σ ^ 2 = ↑n * σ ^ 2 * R ^ 2 := by ring
      rwa [this] at h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hneg
      show IsSubGaussian (fun ω => dotProduct (ε ω) (-col j)) (↑n * σ ^ 2 * R ^ 2) μ
      have hcol_sq : ∑ i, ((-col j) i) ^ 2 ≤ ↑n * R ^ 2 := by
        show ∑ i, (-(R * X i j)) ^ 2 ≤ ↑n * R ^ 2
        simp only [neg_sq, mul_pow]; rw [← Finset.mul_sum]
        calc R ^ 2 * ∑ i, X i j ^ 2 ≤ R ^ 2 * ↑n :=
              mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg R)
          _ = ↑n * R ^ 2 := by ring
      have h := subgaussian_dotProduct_column ε (σ ^ 2) (sq_nonneg σ)
        hmeas_ε hindep_ε hε (-col j) (↑n * R ^ 2) hcol_sq
      have : ↑n * R ^ 2 * σ ^ 2 = ↑n * σ ^ 2 * R ^ 2 := by ring
      rwa [this] at h

  have hmem_hull : ∀ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R →
      X *ᵥ θ ∈ convexHull ℝ (↑S : Set (Fin n → ℝ)) := by
    intro θ hθ_l1
    let w' : Option (Fin d) → ℝ := fun
      | some j => |θ j| / R
      | none => 1 - ∑ j, |θ j| / R
    let z' : Option (Fin d) → (Fin n → ℝ) := fun
      | some j => if 0 ≤ θ j then col j else -col j
      | none => 0
    have hRle : (0 : ℝ) ≤ R := le_of_lt hR
    have hsum_le : ∑ j : Fin d, |θ j| / R ≤ 1 := by
      rw [← Finset.sum_div]; exact div_le_one_of_le₀ hθ_l1 hRle
    have heq : X *ᵥ θ = ∑ i : Option (Fin d), w' i • z' i := by
      rw [Fintype.sum_option]
      simp only [w', z', smul_zero, zero_add]
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
      congr 1; ext j
      split_ifs with h
      · simp only [col, abs_of_nonneg h]; field_simp
      · push Not at h; simp only [col, Pi.neg_apply, abs_of_neg h]; field_simp
    rw [heq]
    apply Convex.sum_mem (convex_convexHull ℝ _)
    · intro i _
      match i with
      | some j => exact div_nonneg (abs_nonneg _) hRle
      | none => linarith [hsum_le]
    · rw [Fintype.sum_option]; simp only [w']; linarith
    · intro i _
      match i with
      | none =>
        simp only [z']
        let j₀ : Fin d := ⟨0, hd'⟩
        rw [show (0 : Fin n → ℝ) = midpoint ℝ (col j₀) (-col j₀)
            from (midpoint_self_neg ℝ (col j₀)).symm]
        exact (convex_convexHull ℝ _).midpoint_mem
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_union_left _
            (Finset.mem_image_of_mem col (Finset.mem_univ j₀)))))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ j₀)))))
      | some j =>
        simp only [z']
        split_ifs
        · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_left _ (Finset.mem_image_of_mem col (Finset.mem_univ j))))
        · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

  have hbdd : ∀ ω, BddAbove {v | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧
      v = dotProduct (ε ω) (X *ᵥ θ)} := by
    intro ω
    exact ⟨S.sup' hS_ne (fun v => g ω v), fun b ⟨θ, hθ_l1, hb_eq⟩ => by
      rw [hb_eq]
      obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S (X *ᵥ θ) (hmem_hull θ hθ_l1)
      exact le_trans hv_le (Finset.le_sup' _ hv_mem)⟩
  have h_zero_mem : ∀ ω, (0 : ℝ) ∈ {v | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧
      v = dotProduct (ε ω) (X *ᵥ θ)} :=
    fun ω => ⟨0, by simp [le_of_lt hR], by simp [dotProduct, mulVec]⟩

  have hpw : ∀ ω, sSup {v | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧
      v = dotProduct (ε ω) (X *ᵥ θ)} ≤ S.sup' hS_ne (fun v => g ω v) := by
    intro ω
    apply csSup_le
    · exact ⟨0, h_zero_mem ω⟩
    · intro b ⟨θ, hθ_l1, hb_eq⟩
      rw [hb_eq]
      obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S (X *ᵥ θ) (hmem_hull θ hθ_l1)
      exact le_trans hv_le (Finset.le_sup' (fun v => (g ω) v) hv_mem)

  have hint_gv : ∀ v ∈ S, Integrable (fun ω => g ω v) μ :=
    fun v hv => (hsg v hv).integrable
  have hint_sup : Integrable (fun ω => S.sup' hS_ne (fun v => g ω v)) μ :=
    integrable_sup' hS_ne hint_gv
  have hsSup_nonneg : ∀ ω, 0 ≤ sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)} :=
    fun ω => le_csSup (hbdd ω) (h_zero_mem ω)
  have hint_sSup : Integrable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}) μ :=
    hint_sup.mono hmeas_sup.aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg (hsSup_nonneg ω)]
        exact le_trans (hpw ω) (le_abs_self _)))

  have hσsq_nn : 0 ≤ ↑n * σ ^ 2 * R ^ 2 := by positivity
  calc ∫ ω, sSup {v | ∃ θ, ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)} ∂μ
      ≤ ∫ ω, S.sup' hS_ne (fun v => g ω v) ∂μ :=
        MeasureTheory.integral_mono hint_sSup hint_sup hpw
    _ ≤ Real.sqrt (↑n * σ ^ 2 * R ^ 2) * Real.sqrt (2 * Real.log ↑S.card) :=
        theorem_1_16_expectation_max g S hS_ne hσsq_nn hsg
    _ ≤ σ * R * Real.sqrt ↑n * Real.sqrt (2 * Real.log (2 * ↑d)) := by

        have h1 : Real.sqrt (↑n * σ ^ 2 * R ^ 2) = σ * R * Real.sqrt ↑n := by
          rw [show (↑n : ℝ) * σ ^ 2 * R ^ 2 = (σ * R) ^ 2 * ↑n from by ring]
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        rw [h1]
        gcongr
        have h1' : S.card ≤ S_pos.card + S_neg.card := Finset.card_union_le S_pos S_neg
        have h2 : S_pos.card ≤ d := Finset.card_image_le.trans (by simp)
        have h3 : S_neg.card ≤ d := Finset.card_image_le.trans (by simp)
        have h4 : S.card ≤ 2 * d := by omega
        exact_mod_cast h4

/-- High-probability MSE bound for the `ℓ¹`-constrained LS estimator (Theorem
2.4, tail version): if `‖θ*‖₁ ≤ R` and the columns of `X` are normalised so
that `∑_i X_{ij}² ≤ n`, then for every `t > 0`,
`μ{MSE(X θ̂^{LS}_{B_1}) > t} ≤ 2d · exp(-n t²/(32 σ² R²))`. -/
theorem thm_2_4_l1_ball_tail
    {n d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (R : ℝ) (hR : 0 < R)

    (hθstar_l1 : ∑ j, |θstar j| ≤ R)

    (hcol : ∀ j : Fin d, ∑ i : Fin n, (X i j) ^ 2 ≤ (n : ℝ))

    (ε : Ω → (Fin n → ℝ)) (σ : ℝ) (hσ : 0 < σ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hmeas_ε : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep_ε : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)

    (θhat : Ω → (Fin d → ℝ))
    (hθhat_l1 : ∀ ω, ∑ j, |θhat ω j| ≤ R)
    (hLS : ∀ ω, ∀ θ, ∑ j, |θ j| ≤ R →
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω) ≤
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
    (t : ℝ) (ht : 0 < t) :
    μ {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) / (n : ℝ) > t} ≤
    ENNReal.ofReal ((2 * d) * exp (-(↑n * t ^ 2 / (32 * σ ^ 2 * R ^ 2)))) := by

  set K := {θ : Fin d → ℝ | ∑ j, |θ j| ≤ R} with hK_def
  have hK_symm : ∀ θ, θ ∈ K ↔ -θ ∈ K := by
    intro θ; simp only [K, Set.mem_setOf_eq]; constructor
    · intro h; simp [abs_neg]; exact h
    · intro h; simp [abs_neg] at h; exact h
  have hK_convex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    simp only [K, Set.mem_setOf_eq] at hx hy ⊢
    have h1 : ∀ j, |(a • x + b • y) j| ≤ a * |x j| + b * |y j| := by
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * x j + b * y j|
          ≤ |a * x j| + |b * y j| := abs_add_le _ _
        _ = a * |x j| + b * |y j| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    calc ∑ j, |(a • x + b • y) j|
        ≤ ∑ j, (a * |x j| + b * |y j|) := Finset.sum_le_sum (fun j _ => h1 j)

      _ = a * ∑ j, |x j| + b * ∑ j, |y j| := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ a * R + b * R := by
          have := mul_le_mul_of_nonneg_left hx ha
          have := mul_le_mul_of_nonneg_left hy hb
          linarith
      _ = R := by rw [← add_mul, hab, one_mul]
  have hθstar_K : θstar ∈ K := hθstar_l1
  have hθhat_K : ∀ ω, θhat ω ∈ K := fun ω => hθhat_l1 ω

  have h_subset : {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) / ↑n > t} ⊆
    {ω | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧ dotProduct (ε ω) (X *ᵥ θ) > ↑n * t / 4} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢


    have hbdd : BddAbove (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K) := by


      refine ⟨∑ j : Fin d, R * |dotProduct (ε ω) (fun i => X i j)|, ?_⟩
      intro y hy
      obtain ⟨θ, hθK, rfl⟩ := hy


      show dotProduct (ε ω) (X *ᵥ θ) ≤ ∑ j : Fin d, R * |dotProduct (ε ω) (fun i => X i j)|
      have h_expand : dotProduct (ε ω) (X *ᵥ θ) =
          ∑ j, θ j * dotProduct (ε ω) (fun i => X i j) := by
        simp only [dotProduct, mulVec, dotProduct]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1; ext j; congr 1; ext i; ring
      rw [h_expand]
      calc ∑ j, θ j * dotProduct (ε ω) (fun i => X i j)
          ≤ ∑ j, |θ j * dotProduct (ε ω) (fun i => X i j)| :=
            Finset.sum_le_sum (fun j _ => le_abs_self _)
        _ = ∑ j, |θ j| * |dotProduct (ε ω) (fun i => X i j)| := by
            congr 1; ext j; exact abs_mul _ _
        _ ≤ ∑ j, R * |dotProduct (ε ω) (fun i => X i j)| := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact (Finset.single_le_sum (fun i _ => abs_nonneg (θ i))
              (Finset.mem_univ j)).trans hθK

    have hLS_K : ∀ θ ∈ K, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω)
        ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω) ≤
        dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ) := by
      intro θ hθ; exact hLS ω θ hθ
    have h_det := thm_2_4_deterministic_bound X θstar (ε ω) (θhat ω) K
      hθstar_K (hθhat_K ω) hK_symm hK_convex hLS_K hbdd
    by_cases hn0 : (n : ℝ) = 0
    · simp [hn0] at hω; linarith
    · have hn_pos : (0 : ℝ) < ↑n := by
        cases n with
        | zero => simp at hn0
        | succ m => positivity
      have h_sq_gt : dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) > ↑n * t := by
        rw [gt_iff_lt, ← mul_comm]; rwa [gt_iff_lt, lt_div_iff₀ hn_pos] at hω

      have h_sup_gt : sSup (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K) > ↑n * t / 4 := by
        linarith
      have hne : (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K).Nonempty :=
        ⟨_, Set.mem_image_of_mem _ hθstar_K⟩
      have h_exists := exists_lt_of_lt_csSup hne h_sup_gt
      obtain ⟨y, hy_mem, hy_gt⟩ := h_exists
      obtain ⟨θ, hθ_K, rfl⟩ := hy_mem
      exact ⟨θ, hθ_K, hy_gt⟩

  by_cases hn0 : (n : ℝ) = 0
  ·
    have h_empty : {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) / ↑n > t} = ∅ := by
      ext ω; simp [hn0]; linarith
    simp [h_empty]
  · have hn_pos : (0 : ℝ) < ↑n := by
      cases n with
      | zero => simp at hn0
      | succ m => positivity
    have hnt4 : 0 < (↑n : ℝ) * t / 4 := by positivity
    have h_tail := subgaussian_l1_ball_tail hd X R hR hcol ε σ hσ hε hmeas_ε hindep_ε (↑n * t / 4) hnt4

    calc μ {ω | dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) / ↑n > t}
        ≤ μ {ω | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧ dotProduct (ε ω) (X *ᵥ θ) > ↑n * t / 4} :=
          measure_mono h_subset
      _ ≤ ENNReal.ofReal ((2 * ↑d) * exp (-((↑n * t / 4) ^ 2 / (2 * ↑n * σ ^ 2 * R ^ 2)))) :=
          h_tail
      _ ≤ ENNReal.ofReal ((2 * ↑d) * exp (-(↑n * t ^ 2 / (32 * σ ^ 2 * R ^ 2)))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply exp_le_exp.mpr
          apply neg_le_neg
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith [sq_nonneg t, sq_nonneg σ, sq_nonneg R]

/-- Expected MSE bound for the `ℓ¹`-constrained LS estimator (Theorem 2.4,
expectation version): under the same column-normalisation hypothesis,
`E[MSE(X θ̂^{LS}_{B_1})] ≤ 4 σ R · √(2 log(2d)/n)`. -/
theorem thm_2_4_l1_ball_expectation
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (R : ℝ) (hR : 0 < R)

    (hθstar_l1 : ∑ j, |θstar j| ≤ R)

    (hcol : ∀ j : Fin d, ∑ i : Fin n, (X i j) ^ 2 ≤ (n : ℝ))

    (ε : Ω → (Fin n → ℝ)) (σ : ℝ) (hσ : 0 < σ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hmeas_ε : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep_ε : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)


    (θhat : Ω → (Fin d → ℝ))
    (hθhat_l1 : ∀ ω, ∑ j, |θhat ω j| ≤ R)
    (hLS : ∀ ω, ∀ θ, ∑ j, |θ j| ≤ R →
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω) ≤
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θ))

    (hmeas : Measurable (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
                                             (X *ᵥ (θhat ω - θstar)) / (n : ℝ)))

    (hmeas_sup : Measurable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}))
    (hint_mse : Integrable (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
                                                 (X *ᵥ (θhat ω - θstar))) μ)
    (hint_sup : Integrable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}) μ) :
    ∫ ω, (dotProduct (X *ᵥ (θhat ω - θstar))
                     (X *ᵥ (θhat ω - θstar)) / (n : ℝ)) ∂μ ≤
    4 * σ * R * Real.sqrt (2 * Real.log (2 * d) / n) := by

  set K := {θ : Fin d → ℝ | ∑ j, |θ j| ≤ R} with hK_def
  set sup_func := (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
    ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}) with hsup_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

  have hK_symm : ∀ θ, θ ∈ K ↔ -θ ∈ K := by
    intro θ; simp only [K, Set.mem_setOf_eq]; constructor
    · intro h; simp [abs_neg]; exact h
    · intro h; simp [abs_neg] at h; exact h
  have hK_convex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    simp only [K, Set.mem_setOf_eq] at hx hy ⊢
    have h1 : ∀ j, |(a • x + b • y) j| ≤ a * |x j| + b * |y j| := by
      intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * x j + b * y j|
          ≤ |a * x j| + |b * y j| := abs_add_le _ _
        _ = a * |x j| + b * |y j| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    calc ∑ j, |(a • x + b • y) j|
        ≤ ∑ j, (a * |x j| + b * |y j|) := Finset.sum_le_sum (fun j _ => h1 j)
      _ = a * ∑ j, |x j| + b * ∑ j, |y j| := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ a * R + b * R := by
          have := mul_le_mul_of_nonneg_left hx ha
          have := mul_le_mul_of_nonneg_left hy hb
          linarith
      _ = R := by rw [← add_mul, hab, one_mul]
  have hθstar_K : θstar ∈ K := hθstar_l1

  have hbdd : ∀ ω, BddAbove (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K) := by
    intro ω
    refine ⟨∑ j : Fin d, R * |dotProduct (ε ω) (fun i => X i j)|, ?_⟩
    intro y hy; obtain ⟨θ, hθK, rfl⟩ := hy
    show dotProduct (ε ω) (X *ᵥ θ) ≤ ∑ j : Fin d, R * |dotProduct (ε ω) (fun i => X i j)|
    have h_expand : dotProduct (ε ω) (X *ᵥ θ) =
        ∑ j, θ j * dotProduct (ε ω) (fun i => X i j) := by
      simp only [dotProduct, mulVec, dotProduct]
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      congr 1; ext j; congr 1; ext i; ring
    rw [h_expand]
    calc ∑ j, θ j * dotProduct (ε ω) (fun i => X i j)
        ≤ ∑ j, |θ j * dotProduct (ε ω) (fun i => X i j)| :=
          Finset.sum_le_sum (fun j _ => le_abs_self _)
      _ = ∑ j, |θ j| * |dotProduct (ε ω) (fun i => X i j)| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, R * |dotProduct (ε ω) (fun i => X i j)| := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact (Finset.single_le_sum (fun i _ => abs_nonneg (θ i))
            (Finset.mem_univ j)).trans hθK

  have hsup_eq : ∀ ω, sSup (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K) =
      sSup {v | ∃ θ : Fin d → ℝ, ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)} := by
    intro ω; congr 1; ext v; simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨θ, hθ, rfl⟩; exact ⟨θ, hθ, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩; exact ⟨θ, hθ, rfl⟩


  have h_pointwise : ∀ ω, dotProduct (X *ᵥ (θhat ω - θstar))
      (X *ᵥ (θhat ω - θstar)) / ↑n ≤
      4 / ↑n * sup_func ω := by
    intro ω
    have hθhat_K : θhat ω ∈ K := hθhat_l1 ω
    have hLS_K : ∀ θ ∈ K, dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω)
        ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω) ≤
        dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ) ((X *ᵥ θstar + ε ω) - X *ᵥ θ) := by
      intro θ hθ; exact hLS ω θ hθ
    have h_det := thm_2_4_deterministic_bound X θstar (ε ω) (θhat ω) K
      hθstar_K hθhat_K hK_symm hK_convex hLS_K (hbdd ω)


    have h_sup_rw : 4 * sSup (Set.image (fun θ => dotProduct (ε ω) (X *ᵥ θ)) K) =
        4 * sup_func ω := by rw [hsup_def, hsup_eq]
    have h_le : dotProduct (X *ᵥ (θhat ω - θstar)) (X *ᵥ (θhat ω - θstar)) ≤
        4 * sup_func ω := by linarith
    have h4n : 4 / ↑n * sup_func ω = (4 * sup_func ω) / ↑n := by ring
    rw [h4n]
    exact div_le_div_of_nonneg_right h_le (le_of_lt hn_pos)


  have hint_rhs : Integrable (fun ω => 4 / ↑n * sup_func ω) μ :=
    hint_sup.const_mul (4 / ↑n)
  have hint_lhs : Integrable (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
      (X *ᵥ (θhat ω - θstar)) / ↑n) μ := hint_mse.div_const ↑n
  have h_int_mono := integral_mono hint_lhs hint_rhs h_pointwise

  have h_pull_const : ∫ ω, 4 / ↑n * sup_func ω ∂μ =
      4 / ↑n * ∫ ω, sup_func ω ∂μ := integral_const_mul_of_integrable hint_sup
  rw [h_pull_const] at h_int_mono

  have h_exp := subgaussian_l1_ball_expectation hn hd X R hR hcol ε σ hσ hε hmeas_ε hindep_ε hmeas_sup

  calc ∫ ω, dotProduct (X *ᵥ (θhat ω - θstar))
                       (X *ᵥ (θhat ω - θstar)) / ↑n ∂μ
      ≤ 4 / ↑n * ∫ ω, sup_func ω ∂μ := h_int_mono
    _ ≤ 4 / ↑n * (σ * R * Real.sqrt ↑n * Real.sqrt (2 * Real.log (2 * ↑d))) := by
        apply mul_le_mul_of_nonneg_left h_exp (by positivity)
    _ = 4 * σ * R * Real.sqrt (2 * Real.log (2 * ↑d) / ↑n) := by

        have hlog_pos : 0 < Real.log (2 * ↑d) := by
          apply Real.log_pos
          have : (2 : ℝ) ≤ ↑d := by exact_mod_cast hd
          linarith
        rw [Real.sqrt_div (by linarith)]
        field_simp
        rw [Real.sq_sqrt (le_of_lt hn_pos)]
    _ = 4 * σ * R * Real.sqrt (2 * Real.log (2 * ↑d) / ↑n) := by norm_cast

/-- **Theorem 2.4** (Rigollet, High-Dimensional Statistics).  Combined MSE bound
for the $\ell^1$-constrained least squares estimator over $B_1$. With
column-normalised $X$ and $\theta^* \in B_1(R)$,
$$\mathbb{E}\bigl[\operatorname{MSE}(X\hat\theta^{LS}_{B_1})\bigr]
  \;\lesssim\; \sigma \sqrt{\frac{\log d}{n}},$$
with the matching high-probability tail bound. -/
theorem thm_2_4_l1_ball_mse
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (hθstar_l1 : ∑ j, |θstar j| ≤ R)
    (hcol : ∀ j : Fin d, ∑ i : Fin n, (X i j) ^ 2 ≤ (n : ℝ))
    (ε : Ω → (Fin n → ℝ)) (σ : ℝ) (hσ : 0 < σ)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hmeas_ε : ∀ i : Fin n, Measurable (fun (ω : Ω) => ε ω i))
    (hindep_ε : iIndepFun (β := fun (_ : Fin n) => ℝ)
      (fun (i : Fin n) (ω : Ω) => ε ω i) μ)
    (θhat : Ω → (Fin d → ℝ))

    (hθhat_l1 : ∀ ω, ∑ j, |θhat ω j| ≤ R)
    (hLS : ∀ ω, ∀ θ, ∑ j, |θ j| ≤ R →
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θhat ω) ≤
      dotProduct ((X *ᵥ θstar + ε ω) - X *ᵥ θ)
                 ((X *ᵥ θstar + ε ω) - X *ᵥ θ))
    (hmeas : Measurable (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
                                             (X *ᵥ (θhat ω - θstar)) / (n : ℝ)))

    (hmeas_sup : Measurable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}))
    (hint_mse : Integrable (fun ω => dotProduct (X *ᵥ (θhat ω - θstar))
                                                 (X *ᵥ (θhat ω - θstar))) μ)
    (hint_sup : Integrable (fun ω => sSup {v | ∃ θ : Fin d → ℝ,
      ∑ j, |θ j| ≤ R ∧ v = dotProduct (ε ω) (X *ᵥ θ)}) μ) :

    (∫ ω, (dotProduct (X *ᵥ (θhat ω - θstar))
                      (X *ᵥ (θhat ω - θstar)) / (n : ℝ)) ∂μ ≤
     4 * σ * R * Real.sqrt (2 * Real.log (2 * d) / n)) ∧

    (∀ t : ℝ, 0 < t →
      μ {ω | dotProduct (X *ᵥ (θhat ω - θstar))
                        (X *ᵥ (θhat ω - θstar)) / (n : ℝ) > t} ≤
      ENNReal.ofReal ((2 * d) * exp (-(↑n * t ^ 2 / (32 * σ ^ 2 * R ^ 2))))) := by
  constructor
  · exact thm_2_4_l1_ball_expectation hn hd X θstar R hR hθstar_l1 hcol ε σ hσ hε
      hmeas_ε hindep_ε θhat hθhat_l1 hLS hmeas hmeas_sup hint_mse hint_sup
  · intro t ht
    exact thm_2_4_l1_ball_tail hd X θstar R hR hθstar_l1 hcol ε σ hσ hε
      hmeas_ε hindep_ε θhat hθhat_l1 hLS t ht

end Rigollet.Chapter2
