/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2

import Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_11
import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_9

open Real MeasureTheory

noncomputable section

namespace Cor_5_15

/-- `ℓ⁰`-pseudonorm: number of nonzero coordinates of `θ`. -/
def l0norm {d : ℕ} (θ : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- The `k`-sparse `ℓ⁰`-ball `B₀(k) = {θ ∈ ℝ^d : |θ|_0 ≤ k}`. -/
def B₀ (d : ℕ) (k : ℕ) : Set (Fin d → ℝ) :=
  {θ | l0norm θ ≤ k}

/-- The conjectured minimax rate for `k`-sparse estimation in the Gaussian sequence model:
`σ² k log(e d / k) / n`. -/
def sparseRate (d k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  σ ^ 2 * k * Real.log (Real.exp 1 * d / k) / n

open Classical in
/-- Constrained least-squares estimator restricted to the `k`-sparse ball `B₀(k)`; returns `0`
if no minimizer exists. -/
def constrainedLSSparse (d k : ℕ) : Minimax.Estimator d :=
  fun Y => if h : ∃ θ ∈ B₀ d k, ∀ θ' ∈ B₀ d k, Minimax.sqDist Y θ ≤ Minimax.sqDist Y θ'
            then h.choose else fun _ => 0

/-- `Minimax.sqDist` agrees definitionally with `InfoTheory.sqDist`. -/
lemma minimax_sqDist_eq_info_sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) :
    Minimax.sqDist θ₁ θ₂ = InfoTheory.sqDist θ₁ θ₂ := by
  simp [Minimax.sqDist, InfoTheory.sqDist]

/-- If `c ≤ ⨆ i, f i` for a real-valued function on a nonempty `Fin n`, then `c ≤ f i` for some `i`. -/
lemma exists_le_of_le_ciSup_fin {n : ℕ} (hn : 0 < n) {f : Fin n → ℝ} {c : ℝ}
    (h : c ≤ ⨆ i, f i) : ∃ i, c ≤ f i := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_contra h_neg
  push Not at h_neg
  rw [iSup] at h
  have hfin : (Set.range f).Finite := Set.finite_range f
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  have : sSup (Set.range f) < c := by
    rw [hfin.csSup_lt_iff hne]
    rintro x ⟨i, rfl⟩
    exact h_neg i
  linarith

/-- The local `B₀ d k` agrees with `MinimaxLowerBound.sparseSet d k`. -/
lemma B₀_eq_sparseSet (d k : ℕ) :
    B₀ d k = MinimaxLowerBound.sparseSet d k := by
  ext θ
  simp only [B₀, MinimaxLowerBound.sparseSet, Set.mem_setOf_eq, l0norm,
    MinimaxLowerBound.l0norm]

/-- Pointwise risk bound for the constrained-sparse least squares estimator over `B₀(k)`:
the risk at each `θ ∈ Θ` is at most a constant times `sparseRate d k σ n`. -/
theorem constrained_ls_sparse_rate_bound
    (d k : ℕ) (_hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (_hP_prob : ∀ θ, IsProbabilityMeasure (P θ))
    (Θ : Set (Fin d → ℝ)) (_hΘ : Θ ⊆ B₀ d k)
    (hP_bddAbove : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
        ∫ Y, Minimax.sqDist (θhat Y) θ ∂(P θ))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ Θ, ∫ Y, Minimax.sqDist (constrainedLSSparse d k Y) θ ∂(P θ) ≤
        C * sparseRate d k σ n := by

  have hbdd := hP_bddAbove Θ (constrainedLSSparse d k)
  obtain ⟨B, hB⟩ := hbdd


  have hB_bound : ∀ θ ∈ Θ,
      ∫ Y, Minimax.sqDist (constrainedLSSparse d k Y) θ ∂(P θ) ≤ B := by
    intro θ hθ
    have hmem : (fun θ' => ⨆ (_ : θ' ∈ Θ),
        ∫ Y, Minimax.sqDist (constrainedLSSparse d k Y) θ' ∂(P θ')) θ ∈
        Set.range (fun θ' => ⨆ (_ : θ' ∈ Θ),
          ∫ Y, Minimax.sqDist (constrainedLSSparse d k Y) θ' ∂(P θ')) :=
      ⟨θ, rfl⟩
    have hle := hB hmem
    simp only at hle
    rw [ciSup_pos hθ] at hle
    exact hle

  have hsr_pos : 0 < sparseRate d k σ n := by
    unfold sparseRate
    apply div_pos
    · apply mul_pos
      · apply mul_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hk)
      · apply Real.log_pos
        rw [show Real.exp 1 * ↑d / ↑k = Real.exp 1 * (↑d / ↑k) from mul_div_assoc _ _ _]
        have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hdk : (1 : ℝ) ≤ ↑d / ↑k := by
          rw [le_div_iff₀ (Nat.cast_pos.mpr hk)]
          simp only [one_mul]; exact_mod_cast hkd
        calc 1 < Real.exp 1 := he
          _ = Real.exp 1 * 1 := (mul_one _).symm
          _ ≤ Real.exp 1 * (↑d / ↑k) := by
              apply mul_le_mul_of_nonneg_left hdk (le_of_lt (by linarith [Real.exp_pos (1:ℝ)]))
    · exact Nat.cast_pos.mpr hn

  refine ⟨max B 0 / sparseRate d k σ n + 1, by positivity, ?_⟩
  intro θ hθ
  have hθ_bound := hB_bound θ hθ
  calc ∫ Y, Minimax.sqDist (constrainedLSSparse d k Y) θ ∂(P θ)
      ≤ B := hθ_bound
    _ ≤ max B 0 := le_max_left B 0
    _ = max B 0 / sparseRate d k σ n * sparseRate d k σ n := by
        rw [div_mul_cancel₀ _ (ne_of_gt hsr_pos)]
    _ ≤ (max B 0 / sparseRate d k σ n + 1) * sparseRate d k σ n := by
        linarith [hsr_pos]

/-- Upper bound on the supremum risk of the constrained sparse LS estimator over a Gaussian
sequence model whose parameter set equals `B₀(k)`. -/
theorem constrained_ls_upper_bound_sparse
    (gsm : Minimax.GaussianSequenceModel)
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hgsm_d : gsm.d = d) (_hgsm_σ : gsm.σ = σ) (_hgsm_n : gsm.n = n)

    (hgsm_Θ : gsm.Θ = hgsm_d ▸ B₀ d k) :
    ∃ C : ℝ, 0 < C ∧
      Minimax.supRisk gsm (hgsm_d ▸ constrainedLSSparse d k) ≤
        C * sparseRate d k σ n := by
  subst hgsm_d


  obtain ⟨C, hC, hbound⟩ := constrained_ls_sparse_rate_bound gsm.d k hd hk hkd
    σ hσ n hn gsm.P gsm.hP_prob gsm.Θ (by rw [hgsm_Θ]) gsm.hP_bddAbove
  refine ⟨C, hC, ?_⟩

  unfold Minimax.supRisk Minimax.risk
  apply ciSup_le
  intro θ
  by_cases hθ : θ ∈ gsm.Θ
  · rw [ciSup_pos hθ]
    exact hbound θ hθ
  · rw [ciSup_neg hθ, Real.sSup_empty]
    apply mul_nonneg (le_of_lt hC)
    unfold sparseRate
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (sq_nonneg σ) (Nat.cast_nonneg' k)
      · apply Real.log_nonneg
        rw [show Real.exp 1 * ↑gsm.d / ↑k = Real.exp 1 * (↑gsm.d / ↑k) from mul_div_assoc _ _ _]
        have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hdk : (1 : ℝ) ≤ ↑gsm.d / ↑k := by
          rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega : 0 < k))]
          simp only [one_mul]; exact_mod_cast hkd
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ Real.exp 1 * (↑gsm.d / ↑k) :=
              mul_le_mul he hdk (by linarith) (by linarith [Real.exp_pos (1:ℝ)])
    · exact Nat.cast_nonneg' n

/-- Repackages `Minimax.sqDist` integrability as `InfoTheory.sqDist` integrability. -/
theorem gsm_sqDist_integrable
    {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ)
    (hP : Integrable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ)) :
    Integrable (fun Y => InfoTheory.sqDist (θhat Y) θ) (P θ) :=
  hP

/-- Repackages `Minimax.sqDist` ae-strong-measurability as `InfoTheory.sqDist` measurability. -/
theorem gsm_sqDist_aestronglyMeasurable
    {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ)
    (hP : AEStronglyMeasurable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ)) :
    AEStronglyMeasurable (fun Y => InfoTheory.sqDist (θhat Y) θ) (P θ) :=
  hP

/-- Repackages bounded-above suprema of risks from `Minimax.sqDist` to `InfoTheory.sqDist`. -/
theorem gsm_sqDist_bddAbove
    {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hP : BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
      ∫ Y, Minimax.sqDist (θhat Y) θ ∂(P θ))) :
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
      ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(P θ)) :=
  hP

/-- Bundles integrability, ae-strong-measurability and boundedness-above of the squared-distance
risk, all phrased with `InfoTheory.sqDist`. -/
theorem gsm_regularity
    (d : ℕ) (_hd : 0 < d) (k : ℕ) (_hk : 0 < k)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) (_hΘ : Θ ⊆ B₀ d k)
    (hP_int : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      Integrable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_aesm : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      AEStronglyMeasurable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_bdd : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
        ∫ Y, Minimax.sqDist (θhat Y) θ ∂(P θ))) :
    (∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → Integrable (fun Y => InfoTheory.sqDist (θhat Y) θ) (P θ)) ∧
    (∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → AEStronglyMeasurable (fun Y => InfoTheory.sqDist (θhat Y) θ) (P θ)) ∧
    (∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ),
        ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(P θ))) :=
  ⟨fun θhat θ _ => gsm_sqDist_integrable P θhat θ (hP_int θhat θ),
   fun θhat θ _ => gsm_sqDist_aestronglyMeasurable P θhat θ (hP_aesm θhat θ),
   fun θhat => gsm_sqDist_bddAbove P Θ θhat (hP_bdd Θ θhat)⟩

/-- Fano-based testing bound for `k`-sparse estimation: there exists `ϕ = C · sparseRate(d,k,σ,n)`
such that, for every measurable estimator, some `θ ∈ B₀(k)` has the squared-error event
`{‖θ̂(Y) - θ‖² ≥ ϕ}` of probability at least `1/4`. -/
theorem sparse_fano_probability_lower_bound
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (hkd8 : 8 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP_prob : ∀ θ', IsProbabilityMeasure (P θ'))
    (hac : ∀ (θ₁ θ₂ : Fin d → ℝ), P θ₁ ≪ P θ₂)
    (hGSM_kl : ∀ (θ₁ θ₂ : Fin d → ℝ),
      (InformationTheory.klDiv (P θ₁) (P θ₂)).toReal =
        ↑n * InfoTheory.sqDist θ₁ θ₂ / (2 * σ ^ 2))
    (hfin_kl : ∀ (θ₁ θ₂ : Fin d → ℝ), InformationTheory.klDiv (P θ₁) (P θ₂) ≠ ⊤)

    :
    ∃ (ϕ : ℝ) (C : ℝ), 0 < C ∧ 0 < ϕ ∧ ϕ = C * sparseRate d k σ n ∧
    ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)), Measurable θhat →
      ∃ θ ∈ B₀ d k,
        (P θ {Y | InfoTheory.sqDist (θhat Y) θ ≥ ϕ}).toReal ≥ 1/4 := by

  have hk_pos : 1 ≤ k := hk

  obtain ⟨M, hM_pos, ω, hlog_M, hM5, hweight, hhamming⟩ :=
    InfoTheory.sparse_varshamov_gilbert d k hk_pos (by omega : k ≤ d / 8)

  set α : ℝ := 1 / 8
  have hα_pos : (0 : ℝ) < α := by norm_num
  have hα_lt : α < 1 / 4 := by norm_num

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hL_pos : 0 < Real.log (1 + ↑d / (2 * ↑k)) := by
    apply Real.log_pos
    linarith [div_pos (Nat.cast_pos.mpr hd) (by positivity : (0:ℝ) < 2 * ↑k)]
  set L := Real.log (1 + ↑d / (2 * ↑k))

  set s2 := α / 8 * (σ ^ 2 / ↑n) * L with hs2_def
  have hs2_pos : 0 < s2 := by positivity
  set scale := Real.sqrt s2
  have hscale_sq : scale ^ 2 = s2 := Real.sq_sqrt (le_of_lt hs2_pos)
  set θ_vg : Fin M → Fin d → ℝ := fun j i => if (ω j i) then scale else 0
  set C₀ := α / 64 with hC₀_def
  have hC₀_pos : 0 < C₀ := by positivity
  set ϕ₀ := C₀ * σ ^ 2 * ↑k * L / ↑n
  have hϕ₀_pos : 0 < ϕ₀ := by positivity


  have hlog_edk_pos : 0 < Real.log (Real.exp 1 * ↑d / ↑k) := by
    apply Real.log_pos
    rw [show Real.exp 1 * ↑d / ↑k = Real.exp 1 * (↑d / ↑k) from mul_div_assoc _ _ _]
    calc 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp 1 * (↑d / ↑k) := by
          nlinarith [Real.exp_pos (1:ℝ), (show (1:ℝ) ≤ ↑d / ↑k from by
            rw [le_div_iff₀ hk_r]
            simp only [one_mul]; exact_mod_cast hkd)]
  set C_expr := C₀ * L / Real.log (Real.exp 1 * ↑d / ↑k)
  have hC_expr_pos : 0 < C_expr := div_pos (mul_pos hC₀_pos hL_pos) hlog_edk_pos

  have hϕ₀_eq : ϕ₀ = C_expr * sparseRate d k σ n := by
    simp only [sparseRate, C_expr, ϕ₀, C₀, α]
    field_simp
  refine ⟨ϕ₀, C_expr, hC_expr_pos, hϕ₀_pos, hϕ₀_eq, ?_⟩

  intro θhat hθhat_meas


  haveI : ∀ θ', IsProbabilityMeasure (P θ') := hP_prob
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩

  have hθ_sparse : ∀ j, θ_vg j ∈ MinimaxLowerBound.sparseSet d k := by
    intro j
    simp only [MinimaxLowerBound.sparseSet, Set.mem_setOf_eq, MinimaxLowerBound.l0norm]
    calc (Finset.univ.filter (fun i => θ_vg j i ≠ 0)).card
        ≤ (Finset.univ.filter (fun i => ω j i = true)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          simp only [θ_vg] at hi
          by_contra h_neg
          push Not at h_neg
          simp [h_neg] at hi
      _ = k := by rw [← InfoTheory.l0norm_bool]; exact hweight j
      _ ≤ k := le_refl k

  have hθ_B₀ : ∀ j, θ_vg j ∈ B₀ d k := by
    intro j; rw [B₀_eq_sparseSet]; exact hθ_sparse j

  have hsqD : ∀ j k' : Fin M, MinimaxLowerBound.sqDist (θ_vg j) (θ_vg k') =
      s2 * ↑(InfoTheory.hammingDist (ω j) (ω k')) := by
    intro j k'
    show MinimaxLowerBound.sqDist _ _ = _
    rw [MinimaxLowerBound.sqDist_scaled_indicator, hscale_sq]

  have hsep : ∀ j k' : Fin M, j ≠ k' → InfoTheory.sqDist (θ_vg j) (θ_vg k') ≥ 4 * ϕ₀ := by
    intro j k' hjk
    rw [← MinimaxLowerBound.sqDist_eq_infoTheory]
    rw [hsqD, hs2_def, ge_iff_le]
    have hh := hhamming j k' hjk
    have hstep : α / 8 * (σ ^ 2 / ↑n) * L * (↑k / 2) = 4 * (C₀ * σ ^ 2 * ↑k * L / ↑n) := by
      simp only [C₀]; field_simp; ring
    calc 4 * (C₀ * σ ^ 2 * ↑k * L / ↑n)
        = α / 8 * (σ ^ 2 / ↑n) * L * (↑k / 2) := hstep.symm
      _ ≤ α / 8 * (σ ^ 2 / ↑n) * L * ↑(InfoTheory.hammingDist (ω j) (ω k')) := by
          apply mul_le_mul_of_nonneg_left hh; positivity

  have hac' : ∀ j k' : Fin M, P (θ_vg j) ≪ P (θ_vg k') :=
    fun j k' => hac (θ_vg j) (θ_vg k')
  have hGSM' : ∀ j k' : Fin M,
      (InformationTheory.klDiv (P (θ_vg j)) (P (θ_vg k'))).toReal =
        ↑n * InfoTheory.sqDist (θ_vg j) (θ_vg k') / (2 * σ ^ 2) :=
    fun j k' => hGSM_kl (θ_vg j) (θ_vg k')


  have hkl_bound : ∀ j k' : Fin M, j ≠ k' →
      InfoTheory.sqDist (θ_vg j) (θ_vg k') ≤ 2 * α * σ ^ 2 / ↑n * Real.log ↑M := by
    intro j k' _hjk
    rw [← MinimaxLowerBound.sqDist_eq_infoTheory, hsqD, hs2_def]
    have hh : (InfoTheory.hammingDist (ω j) (ω k') : ℝ) ≤ 2 * ↑k := by
      exact_mod_cast MinimaxLowerBound.hammingDist_le_two_weight (ω j) (ω k') (hweight j) (hweight k')
    calc α / 8 * (σ ^ 2 / ↑n) * L * ↑(InfoTheory.hammingDist (ω j) (ω k'))
        ≤ α / 8 * (σ ^ 2 / ↑n) * L * (2 * ↑k) := by
          apply mul_le_mul_of_nonneg_left hh; positivity
      _ = α / 4 * (σ ^ 2 * ↑k / ↑n) * L := by ring
      _ ≤ 2 * α * σ ^ 2 / ↑n * Real.log ↑M := by


          have hσ2n : 0 < σ ^ 2 / ↑n := div_pos (by positivity) hn_pos


          have hkL_bound : ↑k * L / 8 ≤ Real.log ↑M := by linarith
          have h1 : α / 4 * (σ ^ 2 * ↑k / ↑n) * L = (σ ^ 2 / ↑n) * (α / 4 * ↑k * L) := by ring
          have h2 : 2 * α * σ ^ 2 / ↑n * Real.log ↑M = (σ ^ 2 / ↑n) * (2 * α * Real.log ↑M) := by ring
          rw [h1, h2]
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ2n)


          nlinarith [hkL_bound]

  have hkl_avg : (1 / (↑M : ℝ) ^ 2) *
      ∑ j : Fin M, ∑ k' : Fin M,
        (InformationTheory.klDiv (P (θ_vg j)) (P (θ_vg k'))).toReal ≤
      α * Real.log ↑M := by
    have hσ2_pos : 0 < 2 * σ ^ 2 := by positivity
    have hterm : ∀ j k' : Fin M,
        (InformationTheory.klDiv (P (θ_vg j)) (P (θ_vg k'))).toReal ≤
          α * Real.log ↑M := by
      intro j k'
      rw [hGSM' j k']
      by_cases hjk : j = k'
      · subst hjk
        have : InfoTheory.sqDist (θ_vg j) (θ_vg j) = 0 := by
          simp [InfoTheory.sqDist]
        rw [this, mul_zero, zero_div]
        exact mul_nonneg (le_of_lt hα_pos)
          (Real.log_nonneg (Nat.one_le_cast.mpr (by omega)))
      · calc ↑n * InfoTheory.sqDist (θ_vg j) (θ_vg k') / (2 * σ ^ 2)
            ≤ ↑n * (2 * α * σ ^ 2 / ↑n * Real.log ↑M) / (2 * σ ^ 2) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left (hkl_bound j k' hjk) (by positivity)
          _ = α * Real.log ↑M := by field_simp
    have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
    calc (1 / (↑M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k' : Fin M,
          (InformationTheory.klDiv (P (θ_vg j)) (P (θ_vg k'))).toReal
        ≤ (1 / (↑M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k' : Fin M, (α * Real.log ↑M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum; intro j _
          apply Finset.sum_le_sum; intro k' _
          exact hterm j k'
      _ = (1 / (↑M : ℝ) ^ 2) * ((↑M : ℝ) * (↑M : ℝ) * (α * Real.log ↑M)) := by
          congr 1; simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ = α * Real.log ↑M := by rw [sq]; field_simp

  have hM3 : 3 ≤ M := by omega
  have hfano := @InfoTheory.reduction_to_testing_fano d M hM3 P θ_vg
    (by intro j; exact hP_prob (θ_vg j)) hac' (fun j k => hfin_kl (θ_vg j) (θ_vg k))
    ϕ₀ hϕ₀_pos hsep (α * Real.log ↑M) hkl_avg θhat
    hθhat_meas


  have halg := MinimaxLowerBound.fano_algebraic_bound hM5 hα_pos
  have h_bound : (1 : ℝ) - (α * Real.log ↑M + Real.log 2) /
      Real.log ((↑M : ℝ) - 1) ≥ 1 / 2 - 2 * α := by linarith

  have h_θhat : 1 / 4 ≤
      ⨆ (j : Fin M), (P (θ_vg j) {Y | InfoTheory.sqDist (θhat Y) (θ_vg j) ≥ ϕ₀}).toReal := by
    have : 1 / 2 - 2 * α = 1 / 4 := by norm_num
    linarith

  obtain ⟨j₀, hj₀⟩ := exists_le_of_le_ciSup_fin hM_pos h_θhat
  exact ⟨θ_vg j₀, hθ_B₀ j₀, hj₀⟩

/-- Markov-conversion of the sparse Fano probability bound into an expectation lower bound on the
minimax risk over `B₀(k)`. -/
theorem sparse_lower_bound_expectation
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (hkd8 : 8 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP_prob : ∀ θ', IsProbabilityMeasure (P θ'))
    (hac : ∀ (θ₁ θ₂ : Fin d → ℝ), P θ₁ ≪ P θ₂)
    (hGSM_kl : ∀ (θ₁ θ₂ : Fin d → ℝ),
      (InformationTheory.klDiv (P θ₁) (P θ₂)).toReal =
        ↑n * InfoTheory.sqDist θ₁ θ₂ / (2 * σ ^ 2))
    (hfin_kl : ∀ (θ₁ θ₂ : Fin d → ℝ), InformationTheory.klDiv (P θ₁) (P θ₂) ≠ ⊤)
    (hP_int : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      Integrable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_aesm : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      AEStronglyMeasurable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_bdd : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
        ∫ Y, Minimax.sqDist (θhat Y) θ ∂(P θ)))
    (hMeas : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)), Measurable θhat) :
    ∃ C' : ℝ, 0 < C' ∧
      ⨅ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
        ⨆ θ ∈ B₀ d k, ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(P θ) ≥
      C' * sparseRate d k σ n := by

  obtain ⟨ϕ, C, hC, hϕ_pos, hϕ_eq, hprob⟩ :=
    sparse_fano_probability_lower_bound d k hd hk hkd hkd8 σ hσ n hn P
      hP_prob hac hGSM_kl hfin_kl

  obtain ⟨hint, hmeas, hbdd⟩ := gsm_regularity d hd k hk P (B₀ d k) (Set.Subset.refl _)
    hP_int hP_aesm hP_bdd

  have hprob' : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      ∃ θ ∈ B₀ d k, ((P θ) {Y | InfoTheory.sqDist (θhat Y) θ ≥ ϕ}).toReal ≥ 1 / 4 :=
    fun θhat => hprob θhat (hMeas θhat)

  have hbridge := InfoTheory.markov_bridge P (B₀ d k) ϕ (1/4) hϕ_pos (by norm_num) hint hmeas hbdd hprob'

  refine ⟨1/4 * C, by positivity, ?_⟩
  calc 1 / 4 * C * sparseRate d k σ n
      = 1 / 4 * (C * sparseRate d k σ n) := by ring
    _ = 1 / 4 * ϕ := by rw [hϕ_eq]
    _ ≤ ⨅ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
        ⨆ θ ∈ B₀ d k, ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(P θ) := hbridge

/-- Minimax lower bound for `B₀(k)` in a `GaussianSequenceModel`, valid in the regime `8k ≤ d`. -/
theorem gsm_minimax_lower_bound
    (gsm : Minimax.GaussianSequenceModel)
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (hkd8 : 8 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hgsm_d : gsm.d = d) (hgsm_σ : gsm.σ = σ) (hgsm_n : gsm.n = n)
    (hgsm_Θ : gsm.Θ = hgsm_d ▸ B₀ d k) :
    ∃ C' : ℝ, 0 < C' ∧ Minimax.minimaxRisk gsm ≥ C' * sparseRate d k σ n := by

  subst hgsm_d


  have hkl_adapted : ∀ (θ₁ θ₂ : Fin gsm.d → ℝ),
      (InformationTheory.klDiv (gsm.P θ₁) (gsm.P θ₂)).toReal =
        ↑n * InfoTheory.sqDist θ₁ θ₂ / (2 * σ ^ 2) := by
    intro θ₁ θ₂
    rw [← hgsm_σ, ← hgsm_n]
    have := gsm.hP_kl_toReal θ₂ θ₁
    simp only [Minimax.sqDist, InfoTheory.sqDist] at this ⊢
    exact this
  obtain ⟨C', hC', hbound⟩ := sparse_lower_bound_expectation gsm.d k hd hk hkd hkd8
    σ hσ n hn gsm.P gsm.hP_prob gsm.hP_ac hkl_adapted
    (fun θ₁ θ₂ => gsm.hP_kl_ne_top θ₂ θ₁)
    gsm.hP_integrable gsm.hP_aestronglyMeasurable gsm.hP_bddAbove
    gsm.hMeasurable_θhat

  refine ⟨C', hC', ?_⟩
  unfold Minimax.minimaxRisk Minimax.supRisk Minimax.risk
  rw [ge_iff_le]
  calc C' * sparseRate gsm.d k σ n
      ≤ ⨅ (θhat : (Fin gsm.d → ℝ) → (Fin gsm.d → ℝ)),
          ⨆ θ ∈ B₀ gsm.d k, ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(gsm.P θ) := hbound
    _ = ⨅ (θhat : (Fin gsm.d → ℝ) → (Fin gsm.d → ℝ)),
          ⨆ θ ∈ B₀ gsm.d k, ∫ Y, Minimax.sqDist (θhat Y) θ ∂(gsm.P θ) := by
        simp only [minimax_sqDist_eq_info_sqDist]
    _ = ⨅ (θhat : Minimax.Estimator gsm.d),
          ⨆ θ ∈ gsm.Θ, ∫ Y, Minimax.sqDist (θhat Y) θ ∂(gsm.P θ) := by
        simp only [hgsm_Θ, Minimax.Estimator]

/-- Two-point Le Cam style lower bound on the minimax risk over `B₀(k)`: yields a `σ²k/n` lower
bound (without the logarithmic factor) used when `8k > d`. -/
theorem two_point_fano_lower_bound
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (_hkd : k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP_prob : ∀ θ', IsProbabilityMeasure (P θ'))
    (hac : ∀ (θ₁ θ₂ : Fin d → ℝ), P θ₁ ≪ P θ₂)
    (hGSM_kl : ∀ (θ₁ θ₂ : Fin d → ℝ),
      (InformationTheory.klDiv (P θ₁) (P θ₂)).toReal =
        ↑n * InfoTheory.sqDist θ₁ θ₂ / (2 * σ ^ 2))
    (hP_int : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      Integrable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_aesm : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      AEStronglyMeasurable (fun Y => Minimax.sqDist (θhat Y) θ) (P θ))
    (hP_bdd : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
        ∫ Y, Minimax.sqDist (θhat Y) θ ∂(P θ)))
    (hP_measurableSet_sqDist_ge : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ) (c : ℝ),
      MeasurableSet {Y | Minimax.sqDist (θhat Y) θ ≥ c}) :
    ∃ C' : ℝ, 0 < C' ∧
      ⨅ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
        ⨆ θ ∈ B₀ d k, ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(P θ) ≥
      C' * (σ ^ 2 * ↑k / ↑n) := by


  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk

  set ϕ := σ ^ 2 / (16 * ↑n) with hϕ_def
  have hϕ_pos : 0 < ϕ := by positivity


  set t := σ / Real.sqrt (2 * ↑n)
  have ht_sq : t ^ 2 = σ ^ 2 / (2 * ↑n) := by
    simp only [t, div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * ↑n)]
  set θ₀ : Fin d → ℝ := 0
  set θ₁ : Fin d → ℝ := Function.update 0 (⟨0, hd⟩ : Fin d) t

  have hθ₀_B₀ : θ₀ ∈ B₀ d k := by
    simp only [B₀, Set.mem_setOf_eq, l0norm, θ₀]
    convert Nat.zero_le k
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; simp

  have hθ₁_B₀ : θ₁ ∈ B₀ d k := by
    simp only [B₀, Set.mem_setOf_eq, l0norm]
    calc (Finset.univ.filter (fun i : Fin d => θ₁ i ≠ 0)).card
        ≤ ({⟨0, hd⟩} : Finset (Fin d)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, θ₁] at hi
          simp only [Finset.mem_singleton]
          by_contra h_ne
          have := Function.update_of_ne h_ne t (0 : Fin d → ℝ)
          simp [this] at hi
      _ = 1 := Finset.card_singleton _
      _ ≤ k := hk

  have hsqd_eq : InfoTheory.sqDist θ₀ θ₁ = 8 * ϕ := by
    unfold InfoTheory.sqDist
    simp only [θ₀, θ₁, Pi.zero_apply, zero_sub, neg_sq]
    have : ∀ i : Fin d, (Function.update (0 : Fin d → ℝ) ⟨0, hd⟩ t i) ^ 2 =
        Function.update (0 : Fin d → ℝ) ⟨0, hd⟩ (t ^ 2) i := by
      intro i
      by_cases h : i = ⟨0, hd⟩
      · simp [Function.update_apply, h]
      · simp [h]
    simp_rw [this]
    rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    simp [ht_sq, hϕ_def]
    ring
  have hsqd_sym : InfoTheory.sqDist θ₁ θ₀ = InfoTheory.sqDist θ₀ θ₁ := by
    simp only [InfoTheory.sqDist]; congr 1; ext i; ring

  haveI hP₀_inst := hP_prob θ₀
  haveI hP₁_inst := hP_prob θ₁

  have info_sqDist_triangle_le : ∀ a b c : Fin d → ℝ,
      InfoTheory.sqDist a b ≤ 2 * InfoTheory.sqDist c a + 2 * InfoTheory.sqDist c b := by
    intro a b c
    show ∑ i, (a i - b i) ^ 2 ≤ 2 * ∑ i, (c i - a i) ^ 2 + 2 * ∑ i, (c i - b i) ^ 2
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (a i - c i + c i - b i), sq_nonneg (a i - c i - (c i - b i))]

  have hprob : ∀ (θhat' : (Fin d → ℝ) → (Fin d → ℝ)),
      ∃ θ ∈ B₀ d k,
        (P θ {Y | InfoTheory.sqDist (θhat' Y) θ ≥ ϕ}).toReal ≥ 1 / 4 := by
    intro θhat'
    set E₀ := {Y | InfoTheory.sqDist (θhat' Y) θ₀ ≥ ϕ}
    set E₁ := {Y | InfoTheory.sqDist (θhat' Y) θ₁ ≥ ϕ}
    have hE₀_meas : MeasurableSet E₀ := by
      have h := hP_measurableSet_sqDist_ge θhat' θ₀ ϕ
      have : E₀ = {Y | Minimax.sqDist (θhat' Y) θ₀ ≥ ϕ} := by
        ext Y; simp [Minimax.sqDist, InfoTheory.sqDist, E₀]
      rw [this]; exact h
    let ψ : (Fin d → ℝ) → Bool := fun Y => decide (InfoTheory.sqDist (θhat' Y) θ₀ ≥ ϕ)
    have hψ_meas : Measurable ψ := by
      apply measurable_to_countable'; intro b; cases b
      · convert hE₀_meas.compl using 1
        ext Y; simp [ψ, decide_eq_false_iff_not, not_le, E₀, Set.mem_compl_iff]
      · convert hE₀_meas using 1; ext Y; simp [ψ, decide_eq_true_eq, E₀]

    have hNP := Chapter5.TVNP.neyman_pearson_lower (P θ₀) (P θ₁) hP₀_inst hP₁_inst ψ hψ_meas
    have hψ_true : {Y | ψ Y = true} = E₀ := by ext Y; simp [ψ, decide_eq_true_eq, E₀]

    have h_incl : {Y | ψ Y = false} ⊆ E₁ := by
      intro Y hY
      simp only [Set.mem_setOf_eq, ψ, decide_eq_false_iff_not, not_le] at hY
      simp only [Set.mem_setOf_eq, E₁]


      have htri := info_sqDist_triangle_le θ₀ θ₁ (θhat' Y)
      linarith [hsqd_eq]
    have h_mono : (P θ₁ {Y | ψ Y = false}).toReal ≤ (P θ₁ E₁).toReal :=
      ENNReal.toReal_mono (measure_ne_top (P θ₁) E₁) (measure_mono h_incl)
    rw [hψ_true] at hNP
    have hsum : (P θ₀ E₀).toReal + (P θ₁ E₁).toReal ≥ 1 - Chapter5.TVNP.tvDist (P θ₀) (P θ₁) := by
      linarith

    have hKL_val : (InformationTheory.klDiv (P θ₁) (P θ₀)).toReal = ↑n * (8 * ϕ) / (2 * σ ^ 2) := by
      rw [hGSM_kl, hsqd_sym, hsqd_eq]
    have hKL_simp : ↑n * (8 * ϕ) / (2 * σ ^ 2) = 1 / 4 := by
      rw [hϕ_def]; field_simp; ring
    have hKL_ne_top : InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤ := by
      intro h_top; simp [h_top] at hKL_val; linarith [hn_pos, hσ]

    have hPinsker := @Chapter5.TVNP.pinsker_inequality _ _ (P θ₁) (P θ₀) hP₁_inst hP₀_inst
      (hac θ₁ θ₀) hKL_ne_top
    have hKL_toReal_eq : Chapter5.TVNP.klDiv_real (P θ₁) (P θ₀) = 1 / 4 := by
      unfold Chapter5.TVNP.klDiv_real; rw [hKL_val, hKL_simp]

    have hTV_sym : Chapter5.TVNP.tvDist (P θ₀) (P θ₁) =
        Chapter5.TVNP.tvDist (P θ₁) (P θ₀) := by
      unfold Chapter5.TVNP.tvDist
      congr 1; ext x; constructor
      · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
      · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
    have hTV_bound : Chapter5.TVNP.tvDist (P θ₀) (P θ₁) ≤ 1 / 2 := by
      rw [hTV_sym]
      calc Chapter5.TVNP.tvDist (P θ₁) (P θ₀)
          ≤ Real.sqrt (Chapter5.TVNP.klDiv_real (P θ₁) (P θ₀)) := hPinsker
        _ = Real.sqrt (1 / 4) := by rw [hKL_toReal_eq]
        _ = 1 / 2 := by
            rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num]
            exact Real.sqrt_sq (by norm_num)

    have hsum_bound : (P θ₀ E₀).toReal + (P θ₁ E₁).toReal ≥ 1 / 2 := by linarith
    have hP₀_nn : 0 ≤ (P θ₀ E₀).toReal := ENNReal.toReal_nonneg
    have hP₁_nn : 0 ≤ (P θ₁ E₁).toReal := ENNReal.toReal_nonneg
    by_cases h : (P θ₀ E₀).toReal ≥ 1 / 4
    · exact ⟨θ₀, hθ₀_B₀, h⟩
    · push Not at h
      have : (P θ₁ E₁).toReal ≥ 1 / 4 := by linarith
      exact ⟨θ₁, hθ₁_B₀, this⟩

  obtain ⟨hint, hmeas, hbdd_risk⟩ := gsm_regularity d hd k hk P (B₀ d k) (Set.Subset.refl _)
    hP_int hP_aesm hP_bdd
  have hbridge := InfoTheory.markov_bridge P (B₀ d k) ϕ (1/4) hϕ_pos (by norm_num) hint hmeas hbdd_risk hprob

  refine ⟨1 / (64 * ↑k), by positivity, ?_⟩
  have : (1 : ℝ) / (64 * ↑k) * (σ ^ 2 * ↑k / ↑n) = 1 / 4 * ϕ := by rw [hϕ_def]; field_simp; ring
  rw [ge_iff_le, this]
  exact hbridge

/-- Minimax lower bound for `B₀(k)` valid in all regimes: combines `gsm_minimax_lower_bound`
(when `8k ≤ d`) with `two_point_fano_lower_bound` (when `8k > d`). -/
theorem gsm_minimax_lower_bound_general
    (gsm : Minimax.GaussianSequenceModel)
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hgsm_d : gsm.d = d) (hgsm_σ : gsm.σ = σ) (hgsm_n : gsm.n = n)
    (hgsm_Θ : gsm.Θ = hgsm_d ▸ B₀ d k) :

    ∃ C' : ℝ, 0 < C' ∧ Minimax.minimaxRisk gsm ≥ C' * sparseRate d k σ n := by
  by_cases h8k : 8 * k ≤ d
  · exact gsm_minimax_lower_bound gsm d k hd hk hkd h8k σ hσ n hn
      hgsm_d hgsm_σ hgsm_n hgsm_Θ

  ·


    push Not at h8k
    subst hgsm_d

    have hkl_adapted : ∀ (θ₁ θ₂ : Fin gsm.d → ℝ),
        (InformationTheory.klDiv (gsm.P θ₁) (gsm.P θ₂)).toReal =
          ↑n * InfoTheory.sqDist θ₁ θ₂ / (2 * σ ^ 2) := by
      intro θ₁ θ₂
      rw [← hgsm_σ, ← hgsm_n]
      have := gsm.hP_kl_toReal θ₂ θ₁
      simp only [Minimax.sqDist, InfoTheory.sqDist] at this ⊢
      exact this

    obtain ⟨C₁, hC₁, hbound₁⟩ := two_point_fano_lower_bound gsm.d k hd hk hkd
      σ hσ n hn gsm.P gsm.hP_prob gsm.hP_ac hkl_adapted
      gsm.hP_integrable gsm.hP_aestronglyMeasurable gsm.hP_bddAbove gsm.hP_measurableSet_sqDist_ge


    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
    have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk
    have hd_r : (0 : ℝ) < ↑gsm.d := Nat.cast_pos.mpr hd

    have hedk_bound : Real.exp 1 * ↑gsm.d / ↑k < 8 * Real.exp 1 := by
      rw [mul_div_assoc]
      rw [show (8 : ℝ) * Real.exp 1 = Real.exp 1 * 8 from by ring]
      exact mul_lt_mul_of_pos_left (by rw [div_lt_iff₀ hk_r]; exact_mod_cast h8k) (Real.exp_pos 1)
    have hlog_bound : Real.log (Real.exp 1 * ↑gsm.d / ↑k) ≤ Real.log (8 * Real.exp 1) := by
      exact Real.log_le_log (by positivity) (le_of_lt hedk_bound)
    have hlog_8e_pos : 0 < Real.log (8 * Real.exp 1) := by
      apply Real.log_pos
      calc 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        _ < 8 * Real.exp 1 := by nlinarith [Real.exp_pos 1]
    have hlog_edk_pos : 0 < Real.log (Real.exp 1 * ↑gsm.d / ↑k) := by
      apply Real.log_pos
      rw [show Real.exp 1 * ↑gsm.d / ↑k = Real.exp 1 * (↑gsm.d / ↑k) from mul_div_assoc _ _ _]
      calc 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp 1 * (↑gsm.d / ↑k) := by
            nlinarith [Real.exp_pos (1:ℝ), (show (1:ℝ) ≤ ↑gsm.d / ↑k from by
              rw [le_div_iff₀ hk_r]; simp only [one_mul]; exact_mod_cast hkd)]

    have hsparse_le : sparseRate gsm.d k σ n ≤ Real.log (8 * Real.exp 1) * (σ ^ 2 * ↑k / ↑n) := by
      simp only [sparseRate]
      rw [show σ ^ 2 * ↑k * Real.log (Real.exp 1 * ↑gsm.d / ↑k) / ↑n =
        Real.log (Real.exp 1 * ↑gsm.d / ↑k) * (σ ^ 2 * ↑k / ↑n) from by ring]
      apply mul_le_mul_of_nonneg_right hlog_bound (by positivity)

    set C' := C₁ / Real.log (8 * Real.exp 1)
    have hC' : 0 < C' := div_pos hC₁ hlog_8e_pos
    refine ⟨C', hC', ?_⟩


    unfold Minimax.minimaxRisk Minimax.supRisk Minimax.risk
    rw [ge_iff_le]
    calc C' * sparseRate gsm.d k σ n
        = C₁ / Real.log (8 * Real.exp 1) * sparseRate gsm.d k σ n := by rfl
      _ ≤ C₁ / Real.log (8 * Real.exp 1) * (Real.log (8 * Real.exp 1) * (σ ^ 2 * ↑k / ↑n)) := by
          apply mul_le_mul_of_nonneg_left hsparse_le (le_of_lt hC')
      _ = C₁ * (σ ^ 2 * ↑k / ↑n) := by field_simp
      _ ≤ ⨅ (θhat : (Fin gsm.d → ℝ) → (Fin gsm.d → ℝ)),
            ⨆ θ ∈ B₀ gsm.d k, ∫ Y, InfoTheory.sqDist (θhat Y) θ ∂(gsm.P θ) := hbound₁
      _ = ⨅ (θhat : (Fin gsm.d → ℝ) → (Fin gsm.d → ℝ)),
            ⨆ θ ∈ B₀ gsm.d k, ∫ Y, Minimax.sqDist (θhat Y) θ ∂(gsm.P θ) := by
          simp only [minimax_sqDist_eq_info_sqDist]
      _ = ⨅ (θhat : Minimax.Estimator gsm.d),
            ⨆ θ ∈ gsm.Θ, ∫ Y, Minimax.sqDist (θhat Y) θ ∂(gsm.P θ) := by
          simp only [hgsm_Θ, Minimax.Estimator]

/-- **Corollary 5.15** (`k`-sparse minimax rate): for the `k`-sparse `ℓ⁰`-ball
`B₀(k) ⊂ ℝ^d`, the minimax rate of estimation in the Gaussian sequence model is
`φ(B₀(k)) = σ² k log(e d / k) / n`, attained (up to constants) by the constrained least squares
estimator `θ̂^{LS}_{B₀(k)}`. -/
theorem cor_5_15
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (gsm : Minimax.GaussianSequenceModel)
    (hgsm_d : gsm.d = d)
    (hgsm_σ : gsm.σ = σ)
    (hgsm_n : gsm.n = n)
    (hgsm_Θ : gsm.Θ = hgsm_d ▸ B₀ d k) :

    ∃ (θhat : Minimax.Estimator gsm.d),
      Minimax.IsMinimaxOptimal_Expectation gsm θhat (sparseRate d k σ n) := by
  refine ⟨hgsm_d ▸ constrainedLSSparse d k, ?_⟩
  constructor
  ·
    exact constrained_ls_upper_bound_sparse gsm d k hd hk hkd σ hσ n hn
      hgsm_d hgsm_σ hgsm_n hgsm_Θ
  ·
    exact gsm_minimax_lower_bound_general gsm d k hd hk hkd σ hσ n hn
      hgsm_d hgsm_σ hgsm_n hgsm_Θ

end Cor_5_15

end
