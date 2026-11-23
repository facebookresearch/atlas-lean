/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Equicontinuity

open Complex Metric Set Filter Topology

lemma ball_subset_cthickening_of_mem {X : Type*} [PseudoMetricSpace X]
    {K : Set X} {z : X} (hz : z ∈ K) {δ : ℝ} :
    ball z δ ⊆ cthickening δ K :=
  fun _ hw => thickening_subset_cthickening _ _
    (mem_thickening_iff.mpr ⟨z, hz, mem_ball.mp hw⟩)

lemma lipschitz_quarter_ball {R M : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ} {c : ℂ} (hf : DifferentiableOn ℂ f (ball c R))
    (hbnd : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ ball c (R / 4)) (hz₂ : z₂ ∈ ball c (R / 4)) :
    dist (f z₂) (f z₁) ≤ 4 * M / R * dist z₂ z₁ := by
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  have hz₁' : z₁ ∈ ball c (R / 2) := by
    simp only [mem_ball] at hz₁ ⊢; linarith
  have hdist : dist z₂ z₁ < R / 2 := by
    simp only [mem_ball] at hz₁ hz₂
    calc dist z₂ z₁ ≤ dist z₂ c + dist c z₁ := dist_triangle _ _ _
      _ = dist z₂ c + dist z₁ c := by rw [dist_comm c z₁]
      _ < R / 4 + R / 4 := add_lt_add hz₂ hz₁
      _ = R / 2 := by ring
  have hball_sub : ball z₁ (R / 2) ⊆ ball c R := by
    intro w hw; simp only [mem_ball] at hz₁' hw ⊢; linarith [dist_triangle w z₁ c]
  have hz₁'' : z₁ ∈ ball c R := hball_sub (mem_ball_self hR2)
  have hmaps : MapsTo f (ball z₁ (R / 2)) (closedBall (f z₁) (2 * M)) := by
    intro w hw
    simp only [mem_closedBall, dist_comm]
    calc dist (f z₁) (f w) = ‖f z₁ - f w‖ := dist_eq_norm _ _
      _ ≤ ‖f z₁‖ + ‖f w‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbnd z₁ hz₁'') (hbnd w (hball_sub hw))
      _ = 2 * M := by ring
  calc dist (f z₂) (f z₁)
      ≤ 2 * M / (R / 2) * dist z₂ z₁ :=
        Complex.dist_le_div_mul_dist_of_mapsTo_ball (hf.mono hball_sub) hmaps (mem_ball.mpr hdist)
    _ = 4 * M / R * dist z₂ z₁ := by ring

lemma diagonal_extraction_nat
    (x : ℕ → ℕ → ℂ)
    (hbdd : ∀ k, ∃ M, ∀ n, ‖x n k‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ∃ a, Tendsto (fun n => x (φ n) k) atTop (nhds a) := by
  have key : ∀ k, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ a, Tendsto (fun n => x (φ (σ n)) k) atTop (nhds a) := by
    intro k φ _
    obtain ⟨M, hM⟩ := hbdd k
    obtain ⟨a, _, σ, hσ, hconv⟩ :=
      (ProperSpace.isCompact_closedBall (0 : ℂ) M).tendsto_subseq
        (fun n => by simp [mem_closedBall, dist_zero_right]; exact hM (φ n))
    exact ⟨σ, hσ, a, hconv⟩
  choose σ_fun hσ_mono a_fun ha_conv using key
  let ψ : ℕ → {φ : ℕ → ℕ // StrictMono φ} := fun k =>
    Nat.rec ⟨id, strictMono_id⟩ (fun k prev =>
      ⟨prev.val ∘ σ_fun k prev.val prev.property,
       prev.property.comp (hσ_mono k prev.val prev.property)⟩) k
  have hψ_le : ∀ k n, (ψ k).val n ≤ (ψ (k + 1)).val n := by
    intro k n
    show (ψ k).val n ≤ ((ψ k).val ∘ σ_fun k (ψ k).val (ψ k).property) n
    simp only [Function.comp_apply]
    exact (ψ k).property.monotone ((hσ_mono k (ψ k).val (ψ k).property).id_le n)
  have hψ_le_gen : ∀ p q, q ≤ p → ∀ n, (ψ q).val n ≤ (ψ p).val n := by
    intro p q hpq; induction hpq with
    | refl => intro n; exact le_refl _
    | step h ih => intro n; exact le_trans (ih n) (hψ_le _ n)
  have hψ_factor : ∀ p q, q ≤ p → ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ n, (ψ p).val n = (ψ q).val (τ n) := by
    intro p q hpq; induction hpq with
    | refl => exact ⟨id, strictMono_id, fun n => rfl⟩
    | @step m _ ih =>
      obtain ⟨τ', hτ', hfact'⟩ := ih
      let σ_m := σ_fun m (ψ m).val (ψ m).property
      refine ⟨τ' ∘ σ_m, hτ'.comp (hσ_mono m (ψ m).val (ψ m).property), fun n => ?_⟩
      simp only [Function.comp_apply]
      conv_lhs => rw [show (ψ (m + 1)).val = (ψ m).val ∘ σ_m from rfl]
      simp only [Function.comp_apply]
      exact hfact' (σ_m n)
  let φ := fun n => (ψ n).val n
  refine ⟨φ, ?_, ?_⟩
  · intro m n hmn
    calc (ψ m).val m < (ψ m).val n := (ψ m).property hmn
      _ ≤ (ψ n).val n := hψ_le_gen n m hmn.le n
  · intro k
    refine ⟨a_fun k (ψ k).val (ψ k).property, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h_conv := ha_conv k (ψ k).val (ψ k).property
    rw [Metric.tendsto_atTop] at h_conv
    obtain ⟨N, hN⟩ := h_conv ε hε
    use max (k + 1) N
    intro n hn
    obtain ⟨τ, hτ, hfact⟩ := hψ_factor n (k + 1) (le_of_max_le_left hn)
    show dist (x ((ψ n).val n) k) (a_fun k (ψ k).val (ψ k).property) < ε
    rw [hfact n]
    exact hN (τ n) (le_trans (le_of_max_le_right hn) (hτ.id_le n))

theorem montel_normal_families
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hbdd : ∀ K : Set ℂ, K ⊆ Ω → IsCompact K →
      ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ),
      StrictMono φ ∧
      TendstoLocallyUniformlyOn (f ∘ φ) g atTop Ω ∧
      DifferentiableOn ℂ g Ω := by
  classical

  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense ℂ
  obtain ⟨ζ, hζ_surj⟩ := hD_count.exists_surjective hD_dense.nonempty


  let x : ℕ → ℕ → ℂ := fun n k => if (ζ k).val ∈ Ω then f n (ζ k).val else 0
  have hbdd_pts : ∀ k, ∃ Mb, ∀ n, ‖x n k‖ ≤ Mb := by
    intro k
    by_cases hzk : (ζ k).val ∈ Ω
    · obtain ⟨Mb, hMb⟩ := hbdd {(ζ k).val} (singleton_subset_iff.mpr hzk) isCompact_singleton
      exact ⟨Mb, fun n => by simp only [x, if_pos hzk]; exact hMb n _ (mem_singleton _)⟩
    · exact ⟨0, fun n => by simp only [x, if_neg hzk, norm_zero]; exact le_refl 0⟩

  obtain ⟨φ, hφ_mono, hφ_conv⟩ := diagonal_extraction_nat x hbdd_pts


  have hconv_D : ∀ d ∈ D, d ∈ Ω → ∃ a, Tendsto (fun n => f (φ n) d) atTop (nhds a) := by
    intro d hd hdΩ
    obtain ⟨k, hk⟩ := hζ_surj ⟨d, hd⟩
    obtain ⟨a, ha⟩ := hφ_conv k
    have hζk_eq : (ζ k).val = d := congr_arg Subtype.val hk
    have hζk_Ω : (ζ k).val ∈ Ω := hζk_eq ▸ hdΩ
    refine ⟨a, ?_⟩
    have : (fun n => x (φ n) k) = (fun n => f (φ n) d) := by
      ext n; simp only [x, if_pos hζk_Ω, hζk_eq]
    rwa [this] at ha

  have h_cauchy : ∀ K : Set ℂ, K ⊆ Ω → IsCompact K →
      UniformCauchySeqOn (f ∘ φ) atTop K := by
    intro K hKΩ hK
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε

    obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hΩ hKΩ

    obtain ⟨M, hM⟩ := hbdd (cthickening δ K) hδK hK.cthickening
    set L := 4 * M / δ

    set η := min (ε / (6 * |L| + 6)) (δ / 4)
    have hη_pos : 0 < η := lt_min (by positivity) (by linarith)

    have hLη : |L| * (2 * η) < ε / 3 := by
      have : |L| * (2 * η) = 2 * |L| * η := by ring
      rw [this]
      calc 2 * |L| * η
          ≤ 2 * |L| * (ε / (6 * |L| + 6)) := by
            apply mul_le_mul_of_nonneg_left (min_le_left _ _); positivity
        _ = 2 * |L| * ε / (6 * |L| + 6) := by ring
        _ < ε / 3 := by
            rw [div_lt_div_iff₀ (by positivity : 6 * |L| + 6 > 0) (by norm_num : (3:ℝ) > 0)]
            nlinarith [abs_nonneg L]

    obtain ⟨S, hSK, hS_fin, hS_cover⟩ := hK.elim_finite_subcover_image
      (fun _ _ => isOpen_ball)
      (show K ⊆ ⋃ z ∈ K, ball z η from fun z hz => mem_biUnion hz (mem_ball_self hη_pos))

    let dp : ℂ → ℂ := fun z_c =>
      if h : z_c ∈ S then (hD_dense.exists_dist_lt z_c hη_pos).choose else 0
    have hdp_mem : ∀ z_c, z_c ∈ S → dp z_c ∈ D := by
      intro z_c h; simp only [dp, dif_pos h]; exact (hD_dense.exists_dist_lt z_c hη_pos).choose_spec.1
    have hdp_dist : ∀ z_c, z_c ∈ S → dist z_c (dp z_c) < η := by
      intro z_c h; simp only [dp, dif_pos h]; exact (hD_dense.exists_dist_lt z_c hη_pos).choose_spec.2
    have hdp_Ω : ∀ z_c, z_c ∈ S → dp z_c ∈ Ω := by
      intro z_c h
      apply hδK; apply thickening_subset_cthickening
      rw [mem_thickening_iff]
      exact ⟨z_c, hSK h, by rw [dist_comm]; calc dist z_c (dp z_c) < η := hdp_dist z_c h
        _ ≤ δ / 4 := min_le_right _ _
        _ < δ := by linarith⟩

    have h_cp : ∀ z_c, z_c ∈ S →
        ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          dist (f (φ m) (dp z_c)) (f (φ n) (dp z_c)) < ε / 3 := by
      intro z_c hz_c
      obtain ⟨a, ha⟩ := hconv_D _ (hdp_mem z_c hz_c) (hdp_Ω z_c hz_c)
      rw [Metric.tendsto_atTop] at ha
      obtain ⟨N, hN⟩ := ha (ε / 6) (by linarith)
      exact ⟨N, fun m hm n hn => calc
        dist (f (φ m) (dp z_c)) (f (φ n) (dp z_c))
          ≤ dist (f (φ m) (dp z_c)) a + dist a (f (φ n) (dp z_c)) := dist_triangle _ _ _
        _ < ε / 6 + ε / 6 := add_lt_add (hN m hm) (by rw [dist_comm]; exact hN n hn)
        _ = ε / 3 := by ring⟩

    choose Nf hNf using h_cp
    let g_N : ℂ → ℕ := fun z_c => if h : z_c ∈ S then Nf z_c h else 0
    set N₀ := hS_fin.toFinset.sup g_N
    refine ⟨N₀, fun m hm n hn z hz => ?_⟩

    obtain ⟨z_c, hz_c_S, hz_c_ball⟩ : ∃ z_c ∈ S, z ∈ ball z_c η := by
      simpa using hS_cover hz

    have hz_q : z ∈ ball z_c (δ / 4) :=
      mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz_c_ball) (min_le_right _ _))

    have hdp_q : dp z_c ∈ ball z_c (δ / 4) :=
      mem_ball.mpr (by rw [dist_comm]; exact lt_of_lt_of_le (hdp_dist z_c hz_c_S) (min_le_right _ _))

    have hball_Ω : ball z_c δ ⊆ Ω :=
      (ball_subset_cthickening_of_mem (hSK hz_c_S)).trans hδK
    have hfn_bnd : ∀ w ∈ ball z_c δ, ∀ k, ‖f k w‖ ≤ M :=
      fun w hw k => hM k w (ball_subset_cthickening_of_mem (hSK hz_c_S) hw)

    have h_lip_z_dp : ∀ k, dist (f k z) (f k (dp z_c)) ≤ |L| * (2 * η) := by
      intro k
      have hLip := lipschitz_quarter_ball hδ ((hf k).mono hball_Ω)
        (fun w hw => hfn_bnd w hw k) hz_q hdp_q
      have hdist_dp_z : dist (dp z_c) z < 2 * η := calc
        dist (dp z_c) z ≤ dist (dp z_c) z_c + dist z_c z := dist_triangle _ _ _
        _ < η + η := add_lt_add (by rw [dist_comm]; exact hdp_dist z_c hz_c_S) (by rw [dist_comm]; exact mem_ball.mp hz_c_ball)
        _ = 2 * η := by ring
      calc dist (f k z) (f k (dp z_c))
          = dist (f k (dp z_c)) (f k z) := dist_comm _ _
        _ ≤ L * dist (dp z_c) z := hLip
        _ ≤ |L| * dist (dp z_c) z :=
            mul_le_mul_of_nonneg_right (le_abs_self L) dist_nonneg
        _ ≤ |L| * (2 * η) :=
            mul_le_mul_of_nonneg_left hdist_dp_z.le (abs_nonneg L)

    have h_N_le : Nf z_c hz_c_S ≤ N₀ := by
      show Nf z_c hz_c_S ≤ hS_fin.toFinset.sup g_N
      have hz_c_fin : z_c ∈ hS_fin.toFinset := hS_fin.mem_toFinset.mpr hz_c_S
      calc Nf z_c hz_c_S = g_N z_c := by simp [g_N, hz_c_S]
        _ ≤ hS_fin.toFinset.sup g_N := Finset.le_sup hz_c_fin
    show dist ((f ∘ φ) m z) ((f ∘ φ) n z) < ε
    simp only [Function.comp_apply]
    calc dist (f (φ m) z) (f (φ n) z)
        ≤ dist (f (φ m) z) (f (φ m) (dp z_c)) +
          (dist (f (φ m) (dp z_c)) (f (φ n) (dp z_c)) +
           dist (f (φ n) (dp z_c)) (f (φ n) z)) := by
            linarith [dist_triangle (f (φ m) z) (f (φ m) (dp z_c)) (f (φ n) z),
                      dist_triangle (f (φ m) (dp z_c)) (f (φ n) (dp z_c)) (f (φ n) z)]
      _ < ε / 3 + (ε / 3 + ε / 3) := by
          have t1 : dist (f (φ m) z) (f (φ m) (dp z_c)) < ε / 3 :=
            lt_of_le_of_lt (h_lip_z_dp (φ m)) hLη
          have t2 : dist (f (φ m) (dp z_c)) (f (φ n) (dp z_c)) < ε / 3 :=
            hNf z_c hz_c_S m (le_trans h_N_le hm) n (le_trans h_N_le hn)
          have t3 : dist (f (φ n) (dp z_c)) (f (φ n) z) < ε / 3 := by
            rw [dist_comm]; exact lt_of_le_of_lt (h_lip_z_dp (φ n)) hLη
          linarith
      _ = ε := by ring


  have h_ptwise : ∀ z ∈ Ω, ∃ a, Tendsto (fun n => f (φ n) z) atTop (nhds a) := by
    intro z hz
    have huc := h_cauchy {z} (singleton_subset_iff.mpr hz) isCompact_singleton
    exact cauchySeq_tendsto_of_complete (huc.cauchySeq (mem_singleton z))

  let g : ℂ → ℂ := fun z =>
    if h : z ∈ Ω then (h_ptwise z h).choose else 0
  have hg_lim : ∀ z ∈ Ω, Tendsto (fun n => f (φ n) z) atTop (nhds (g z)) := by
    intro z hz; simp only [g, dif_pos hz]; exact (h_ptwise z hz).choose_spec

  have h_loc_unif : TendstoLocallyUniformlyOn (f ∘ φ) g atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro K hKΩ hK
    exact (h_cauchy K hKΩ hK).tendstoUniformlyOn_of_tendsto
      (fun z hz => hg_lim z (hKΩ hz))
  refine ⟨φ, g, hφ_mono, h_loc_unif, ?_⟩

  exact h_loc_unif.differentiableOn (Eventually.of_forall (fun n => (hf (φ n)))) hΩ
