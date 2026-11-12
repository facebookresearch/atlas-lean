/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_14
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Mathlib

set_option maxHeartbeats 4800000

open MeasureTheory Metric Set Real ENNReal

noncomputable section

/-- If `N` is a `1/2`-net of the closed unit ball, then for every nonzero `x`
there is a point `z ∈ N` with `⟨z, x⟩ ≥ ‖x‖ / 2`. This is the key discretization
step used to reduce a sup over the unit ball to a max over a finite net. -/
lemma exists_net_inner_ge_half_norm
    {d : ℕ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (hN_net : IsEpsilonNet (Metric.closedBall 0 1)
      (N : Set (EuclideanSpace ℝ (Fin d))) (1/2))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ≠ 0) :
    ∃ z ∈ N, @inner ℝ _ _ z x ≥ (1/2) * ‖x‖ := by
  set θ := (‖x‖⁻¹ : ℝ) • x with hθ_def
  have hx_norm_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hθ_norm : ‖θ‖ = 1 := by
    rw [hθ_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]
  have hθ_ball : θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_closedBall_zero_iff]; exact le_of_eq hθ_norm
  obtain ⟨z, hz_mem, hz_dist⟩ := hN_net.2 θ hθ_ball
  refine ⟨z, hz_mem, ?_⟩
  have hθ_inner : @inner ℝ _ _ θ x = ‖x‖ := by
    rw [hθ_def, real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  have hdist : ‖θ - z‖ ≤ 1/2 := by
    rw [← dist_eq_norm, dist_comm]; exact hz_dist
  have hCS : @inner ℝ _ _ (θ - z) x ≤ ‖θ - z‖ * ‖x‖ := real_inner_le_norm _ _
  have hsplit : @inner ℝ _ _ z x = @inner ℝ _ _ θ x - @inner ℝ _ _ (θ - z) x := by
    rw [inner_sub_left]; ring
  rw [hsplit, hθ_inner]
  linarith [mul_le_mul_of_nonneg_right hdist (norm_nonneg x)]

/-- If some `θ` with `‖θ‖ ≤ 1` satisfies `⟨θ, x⟩ > t`, then some net point `z ∈ N`
satisfies `⟨z, x⟩ > t / 2`. Used to reduce the unit-ball tail event to a net event. -/
lemma event_containment_net
    {d : ℕ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (hN_net : IsEpsilonNet (Metric.closedBall 0 1)
      (N : Set (EuclideanSpace ℝ (Fin d))) (1/2))
    (x : EuclideanSpace ℝ (Fin d))
    (t : ℝ) (ht : 0 < t)
    (hθ_exists : ∃ θ : EuclideanSpace ℝ (Fin d),
      ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ x > t) :
    ∃ z ∈ (N : Set (EuclideanSpace ℝ (Fin d))), @inner ℝ _ _ z x > t / 2 := by
  obtain ⟨θ, hθ_norm, hθ_inner⟩ := hθ_exists
  have hx_norm_gt : ‖x‖ > t := by
    calc (t : ℝ) < @inner ℝ _ _ θ x := hθ_inner
      _ ≤ ‖θ‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hθ_norm (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hx_ne : x ≠ 0 := by
    intro heq; simp [heq] at hx_norm_gt; linarith
  obtain ⟨z, hz_mem, hz_inner⟩ := exists_net_inner_ge_half_norm hN_net x hx_ne
  exact ⟨z, hz_mem, by linarith⟩

/-- Tail bound flavour of Theorem 1.19: for a sub-Gaussian random vector `X` in
`ℝ^d` with parameter `σ²`,
`P(∃ θ ∈ B₂, ⟨θ, X⟩ > t) ≤ 6^d · exp(-t²/(8σ²))`. -/
theorem theorem_1_19_tail_bound
    {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (_hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} ≤
      ENNReal.ofReal ((6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq)))) := by

  obtain ⟨N, hN_net, hN_card⟩ :=
    lemma_1_18_covering_number_euclidean_ball hd (1/2 : ℝ) (by norm_num) (by norm_num)

  have h_subset :
      {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} ⊆
      {ω | ∃ z ∈ (N : Set (EuclideanSpace ℝ (Fin d))), @inner ℝ _ _ z (X ω) > t / 2} := by
    intro ω hω
    exact event_containment_net hN_net (X ω) t ht hω

  have hN_in_ball : ∀ z ∈ N, ‖z‖ ≤ 1 := by
    intro z hz; exact mem_closedBall_zero_iff.mp (hN_net.1 hz)
  have hsg_net : ∀ z ∈ N,
      IsSubGaussian (fun ω => @inner ℝ _ _ z (X ω)) σsq μ := by
    intro z hz; exact hsg z (hN_in_ball z hz)


  have ht2 : (0 : ℝ) < t / 2 := by linarith
  have h_per_elem : ∀ z ∈ N,
      μ {ω | @inner ℝ _ _ z (X ω) > t / 2} ≤
        ENNReal.ofReal (exp (-(t ^ 2 / (8 * σsq)))) := by
    intro z hz
    have := lemma_1_3_upper_tail (hsg_net z hz) (t / 2) ht2
    convert this using 2
    congr 1; ring

  calc μ {ω | ∃ θ, ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t}
      ≤ μ {ω | ∃ z ∈ (N : Set (EuclideanSpace ℝ (Fin d))),
            @inner ℝ _ _ z (X ω) > t / 2} :=
        measure_mono h_subset
    _ = μ (⋃ z ∈ (N : Set (EuclideanSpace ℝ (Fin d))),
            {ω | @inner ℝ _ _ z (X ω) > t / 2}) := by
        congr 1; ext ω; simp [Set.mem_iUnion]
    _ ≤ ∑' (z : ↥(N : Set (EuclideanSpace ℝ (Fin d)))),
          μ {ω | @inner ℝ _ _ (z : EuclideanSpace ℝ (Fin d)) (X ω) > t / 2} :=
        measure_biUnion_le μ N.countable_toSet _
    _ ≤ ∑' (_ : ↥(N : Set (EuclideanSpace ℝ (Fin d)))),
          ENNReal.ofReal (exp (-(t ^ 2 / (8 * σsq)))) := by
        apply ENNReal.tsum_le_tsum
        intro ⟨z, hz⟩
        exact h_per_elem z hz
    _ = N.card • ENNReal.ofReal (exp (-(t ^ 2 / (8 * σsq)))) := by
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => (hi (Finset.mem_univ i)).elim)]
        simp [Finset.sum_const]
    _ ≤ ENNReal.ofReal ((6 : ℝ) ^ d * exp (-(t ^ 2 / (8 * σsq)))) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))

        have h6 : (3 / (1/2 : ℝ)) = (6 : ℝ) := by norm_num
        have hceil : Nat.ceil ((6 : ℝ) ^ d) = (6 : ℕ) ^ d := by
          rw [show (6 : ℝ) ^ d = ((6 : ℕ) ^ d : ℕ) from by push_cast; ring]
          exact Nat.ceil_natCast _
        have hcard : N.card ≤ 6 ^ d := by rw [← hceil, ← h6]; exact hN_card
        exact_mod_cast hcard

/-- Theorem 1.19 (expectation): for a sub-Gaussian random vector `X` in `ℝ^d`
with parameter `σ²`, `E[‖X‖] ≤ 4 σ √d`. -/
theorem theorem_1_19_expectation_bound
    {d : ℕ} (hd : 0 < d)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {_ : IsProbabilityMeasure μ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ) :
    ∫ ω, ‖X ω‖ ∂μ ≤ 4 * Real.sqrt σsq * Real.sqrt d := by

  obtain ⟨N, hN_net, hN_card⟩ :=
    lemma_1_18_covering_number_euclidean_ball hd (1/2 : ℝ) (by norm_num) (by norm_num)

  have hN_nonempty : N.Nonempty := by
    have h0_in : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      simp [Metric.mem_closedBall]
    obtain ⟨z, hz_mem, _⟩ := hN_net.2 0 h0_in
    exact ⟨z, hz_mem⟩
  have hN_card_pos : 0 < N.card := Finset.card_pos.mpr hN_nonempty

  haveI : Nonempty (Fin N.card) := ⟨⟨0, hN_card_pos⟩⟩
  set f : Fin N.card → EuclideanSpace ℝ (Fin d) := fun i => (N.equivFin.symm i).val with hf_def
  set Y : Fin N.card → Ω → ℝ := fun i ω => @inner ℝ _ _ (f i) (X ω) with hY_def

  have hf_mem : ∀ i, f i ∈ N := fun i => (N.equivFin.symm i).prop
  have hf_norm : ∀ i, ‖f i‖ ≤ 1 := fun i =>
    mem_closedBall_zero_iff.mp (hN_net.1 (hf_mem i))
  have hY_sg : ∀ i, IsSubGaussian (Y i) σsq μ := fun i => hsg (f i) (hf_norm i)

  set Z : Ω → ℝ := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) with hZ_def
  have hpw : ∀ ω, ‖X ω‖ ≤ 2 * Z ω := by
    intro ω
    by_cases hx : X ω = 0
    · simp [hx, hZ_def, hY_def]
    · obtain ⟨z, hz_mem, hz_inner⟩ := exists_net_inner_ge_half_norm hN_net (X ω) hx

      have ⟨j, hj⟩ : ∃ j : Fin N.card, f j = z :=
        ⟨N.equivFin ⟨z, hz_mem⟩, by simp [hf_def]⟩
      have hZ_ge : Z ω ≥ Y j ω :=
        Finset.le_sup' (fun i => Y i ω) (Finset.mem_univ j)
      have hYj : Y j ω = @inner ℝ _ _ z (X ω) := by simp [hY_def, hj]
      calc ‖X ω‖ = 2 * (1/2 * ‖X ω‖) := by ring
        _ ≤ 2 * @inner ℝ _ _ z (X ω) :=
            mul_le_mul_of_nonneg_left hz_inner (by norm_num : (0:ℝ) ≤ 2)
        _ = 2 * Y j ω := by rw [← hYj]
        _ ≤ 2 * Z ω := by linarith [hZ_ge]


  have hZ_int : Integrable Z μ :=
    integrable_sup' Finset.univ_nonempty (fun i _ => (hY_sg i).integrable)
  have h2Z_int : Integrable (fun ω => 2 * Z ω) μ := hZ_int.const_mul 2

  have h_int_le : ∫ ω, ‖X ω‖ ∂μ ≤ 2 * ∫ ω, Z ω ∂μ := by
    calc ∫ ω, ‖X ω‖ ∂μ
        ≤ ∫ ω, (2 * Z ω) ∂μ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun ω => norm_nonneg _)
          · exact h2Z_int
          · exact Filter.Eventually.of_forall hpw
      _ = 2 * ∫ ω, Z ω ∂μ := integral_const_mul 2 Z


  have hlog6_pos : (0 : ℝ) < Real.log 6 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num

  have hlog6_lt_2 : Real.log 6 < 2 := by
    rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
    apply Real.log_lt_log (by norm_num : (0 : ℝ) < 6)
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    simp [Finset.sum_range_succ] at h; linarith
  have hd_pos_real : (0 : ℝ) < d := Nat.cast_pos.mpr hd

  set sval : ℝ := Real.sqrt (2 * ↑d * Real.log 6 / σsq) with hsval_def
  have hsval_pos : 0 < sval := by
    rw [hsval_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hsval_sq : sval ^ 2 = 2 * ↑d * Real.log 6 / σsq := by
    rw [hsval_def, sq, Real.mul_self_sqrt (by positivity)]

  have h14 := theorem_1_14_expectation_max_parametric hN_card_pos hσ.le hY_sg sval hsval_pos


  have hNcard_le_6d : (N.card : ℝ) ≤ (6 : ℝ) ^ d := by
    have h6 : (3 / (1/2 : ℝ)) = (6 : ℝ) := by norm_num
    have hceil : Nat.ceil ((6 : ℝ) ^ d) = (6 : ℕ) ^ d := by
      rw [show (6 : ℝ) ^ d = ((6 : ℕ) ^ d : ℕ) from by push_cast; ring]
      exact Nat.ceil_natCast _
    have hcard : N.card ≤ 6 ^ d := by rw [← hceil, ← h6]; exact hN_card
    exact_mod_cast hcard
  have hlog_Ncard : Real.log N.card ≤ d * Real.log 6 := by
    calc Real.log N.card ≤ Real.log ((6 : ℝ) ^ d) := by
          apply Real.log_le_log (Nat.cast_pos.mpr hN_card_pos) hNcard_le_6d
      _ = d * Real.log 6 := by
          rw [Real.log_pow]

  have hsum_eq : ↑d * Real.log 6 / sval + σsq * sval / 2 = σsq * sval := by
    have h1 : ↑d * Real.log 6 = σsq * sval ^ 2 / 2 := by
      rw [hsval_sq]; field_simp
    rw [show ↑d * Real.log 6 / sval = σsq * sval ^ 2 / 2 / sval from by rw [← h1]]
    have hsval_ne : sval ≠ 0 := ne_of_gt hsval_pos
    field_simp
    ring


  have hfinal : 2 * (↑d * Real.log 6 / sval + σsq * sval / 2) ≤ 4 * Real.sqrt σsq * Real.sqrt d := by
    rw [hsum_eq]


    rw [show 2 * (σsq * sval) = 2 * σsq * sval from by ring]
    have h_lhs_nn : 0 ≤ 2 * σsq * sval := by positivity
    have h_rhs_nn : 0 ≤ 4 * Real.sqrt σsq * Real.sqrt d := by positivity
    rw [← Real.sqrt_sq h_lhs_nn, ← Real.sqrt_sq h_rhs_nn]
    apply Real.sqrt_le_sqrt

    have h_sqrt_σ : (Real.sqrt σsq) ^ 2 = σsq := Real.sq_sqrt hσ.le
    have h_sqrt_d : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, h_sqrt_σ, h_sqrt_d, hsval_sq]
    rw [show (2 : ℝ) ^ 2 = 4 from by norm_num, show (4 : ℝ) ^ 2 = 16 from by norm_num]

    have hσ_ne : σsq ≠ 0 := ne_of_gt hσ
    field_simp
    nlinarith [hlog6_lt_2]
  calc ∫ ω, ‖X ω‖ ∂μ ≤ 2 * ∫ ω, Z ω ∂μ := h_int_le
    _ ≤ 2 * (Real.log N.card / sval + σsq * sval / 2) := by linarith [h14]
    _ ≤ 2 * (↑d * Real.log 6 / sval + σsq * sval / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        linarith [div_le_div_of_nonneg_right hlog_Ncard (le_of_lt hsval_pos)]
    _ ≤ 4 * Real.sqrt σsq * Real.sqrt d := hfinal

/-- If `‖x‖ > t`, then taking `θ = x / ‖x‖` witnesses an element of the closed unit
ball with `⟨θ, x⟩ > t`. -/
lemma norm_gt_exists_inner_gt
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) (ht : 0 < t) (hxt : ‖x‖ > t) :
    ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ x > t := by
  have hx : x ≠ 0 := by intro h; simp [h] at hxt; linarith
  refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_, ?_⟩
  · have : ‖(↑‖x‖ : ℝ)⁻¹ • x‖ = 1 := norm_smul_inv_norm hx
    simp at this; exact le_of_eq this
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    field_simp
    exact hxt

/-- High-probability bound on `‖X‖` for a sub-Gaussian random vector: with
probability at least `1 - δ`,
`‖X‖ ≤ 4 σ √d + 2 σ √(2 log(1/δ))`. -/
theorem theorem_1_19_high_prob
    {d : ℕ} (hd : 0 < d)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {_ : IsProbabilityMeasure μ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    μ {ω | ‖X ω‖ > 4 * Real.sqrt σsq * Real.sqrt d +
      2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ))} ≤
      ENNReal.ofReal δ := by


  set t := 4 * Real.sqrt σsq * Real.sqrt d +
    2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ)) with ht_def

  have ht_pos : 0 < t := by
    have h1 : 0 < Real.sqrt σsq := Real.sqrt_pos.mpr hσ
    have h2 : 0 < Real.sqrt ↑d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    have h3 : 0 ≤ Real.sqrt (2 * Real.log (1 / δ)) := Real.sqrt_nonneg _
    have h4 : 0 < 4 * Real.sqrt σsq * Real.sqrt ↑d := by positivity
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h1.le) h3]

  have h_subset : {ω | ‖X ω‖ > t} ⊆
      {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} := by
    intro ω hω
    exact norm_gt_exists_inner_gt (X ω) t ht_pos hω

  have h_tail := @theorem_1_19_tail_bound d hd Ω ‹_› μ ‹_› X σsq hσ hsg t ht_pos


  have hlog_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ_pos, hδ_lt⟩

  have ht_sq : t ^ 2 ≥ σsq * (16 * ↑d + 8 * Real.log (1 / δ)) := by
    have h_factor : t = Real.sqrt σsq * (4 * Real.sqrt d + 2 * Real.sqrt (2 * Real.log (1 / δ))) := by
      simp only [t]; ring
    rw [h_factor, mul_pow, Real.sq_sqrt hσ.le]
    apply mul_le_mul_of_nonneg_left _ hσ.le
    have hsd : Real.sqrt ↑d ^ 2 = ↑d := Real.sq_sqrt (Nat.cast_nonneg d)
    have hsL : Real.sqrt (2 * Real.log (1 / δ)) ^ 2 = 2 * Real.log (1 / δ) :=
      Real.sq_sqrt (by linarith)
    have hab : 0 ≤ Real.sqrt ↑d * Real.sqrt (2 * Real.log (1 / δ)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (4 * Real.sqrt ↑d), sq_nonneg (2 * Real.sqrt (2 * Real.log (1 / δ)))]

  have hdiv_ge : t ^ 2 / (8 * σsq) ≥ 2 * ↑d + Real.log (1 / δ) := by
    rw [ge_iff_le, le_div_iff₀ (by positivity : 0 < 8 * σsq)]
    nlinarith

  have hexp_le : Real.exp (-(t ^ 2 / (8 * σsq))) ≤
      Real.exp (-(2 * ↑d + Real.log (1 / δ))) := by
    apply Real.exp_le_exp.mpr; linarith

  have hexp_split : Real.exp (-(2 * ↑d + Real.log (1 / δ))) =
      Real.exp (-(2 * ↑d)) * Real.exp (-Real.log (1 / δ)) := by
    rw [← Real.exp_add]; ring_nf

  have hexp_log : Real.exp (-Real.log (1 / δ)) = δ := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt hδ_pos)]
    simp [Real.log_one, Real.exp_log hδ_pos]

  have h6d : (6 : ℝ) ^ d * Real.exp (-(2 * ↑d)) ≤ 1 := by
    have h6 : (6 : ℝ) * Real.exp (-2) < 1 := by
      rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos 2)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num) 4
      simp [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have key : (6 : ℝ) ^ d * Real.exp (-(2 * ↑d)) = (6 * Real.exp (-2)) ^ d := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [key]
    exact pow_le_one₀ (by positivity) h6.le

  have h_bound : (6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq))) ≤ δ := by
    calc (6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq)))
        ≤ (6 : ℝ) ^ d * Real.exp (-(2 * ↑d + Real.log (1 / δ))) := by
          apply mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = (6 : ℝ) ^ d * (Real.exp (-(2 * ↑d)) * Real.exp (-Real.log (1 / δ))) := by
          rw [hexp_split]
      _ = ((6 : ℝ) ^ d * Real.exp (-(2 * ↑d))) * δ := by rw [hexp_log]; ring
      _ ≤ 1 * δ := by apply mul_le_mul_of_nonneg_right h6d hδ_pos.le
      _ = δ := one_mul δ

  calc μ {ω | ‖X ω‖ > t}
      ≤ μ {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} :=
        measure_mono h_subset
    _ ≤ ENNReal.ofReal ((6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq)))) :=
        h_tail
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal h_bound

end
