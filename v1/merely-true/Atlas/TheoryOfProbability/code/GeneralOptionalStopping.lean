/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable

set_option maxHeartbeats 4000000

open MeasureTheory Filter

/-- Helper lemma: for any extended natural `a : ℕ∞` that is not `⊤`, coercing
`a.untopA : ℕ` back into `ℕ∞` recovers `a`. -/
lemma coe_untopA_eq (a : ℕ∞) (ha : a ≠ ⊤) : (↑(a.untopA) : ℕ∞) = a := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha
  rw [← hn]
  simp only [WithTop.untopA, WithTop.untopD, WithTop.recTopCoe]
  rfl

/-- The stopped value of a process `f : ℕ → Ω → ℝ` at a stopping time `τ : Ω → ℕ∞`
that may take the value `⊤` (infinity). When `τ ω = ⊤`, the value is the limit
`lim_{n → ∞} f n ω`; otherwise it is `f (τ ω) ω`. This extends `stoppedValue` to
allow infinite stopping times, as required for the general optional stopping theorem. -/
noncomputable def stoppedValueExtended {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) : Ω → ℝ :=
  fun ω => if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
            else f (τ ω).toNat ω

/-- **Bounded general optional stopping theorem**. If `f` is a submartingale, `L ≤ M`
are stopping times with `M` bounded above by a finite `N`, then `E[f_L] ≤ E[f_M]` and
`f_L ≤ E[f_M | ℱ_L]` almost surely. This is the bounded-stopping-time form that
underpins the general optional stopping theorem. -/
theorem general_optional_stopping_bounded
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0}
    [SigmaFiniteFiltration μ ℱ]
    {f : ℕ → Ω → ℝ}
    {L M : Ω → ℕ∞}
    (hsub : Submartingale f ℱ μ)
    (hL : IsStoppingTime ℱ L)
    (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    (∫ ω, stoppedValue f L ω ∂μ ≤ ∫ ω, stoppedValue f M ω ∂μ) ∧
    (stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace]) := by
  constructor
  · exact hsub.expected_stoppedValue_mono hL hM hLM hbdd
  · have h_sp_sub : Submartingale (stoppedProcess f M) ℱ μ := hsub.stoppedProcess hM
    have hL_bdd : ∀ ω, L ω ≤ N := fun ω => (hLM ω).trans (hbdd ω)
    have hL_ne_top : ∀ ω, L ω ≠ ⊤ := fun ω =>
      ne_top_of_le_ne_top (ne_top_of_le_ne_top (by simp) (hbdd ω)) (hLM ω)
    have h_sp_N : stoppedProcess f M N = stoppedValue f M := by
      funext ω
      exact stoppedProcess_eq_of_ge (hbdd ω)
    have h_key : ∀ᵐ ω ∂μ, ∀ k : ℕ, L ω = ↑k →
        stoppedProcess f M k ω ≤
          (μ[stoppedValue f M | hL.measurableSpace]) ω := by
      rw [ae_all_iff]
      intro k
      by_cases hkN : k ≤ N
      · have h_ineq_k : stoppedProcess f M k ≤ᵐ[μ] μ[stoppedValue f M | ℱ k] := by
          have := h_sp_sub.ae_le_condExp hkN
          rwa [h_sp_N] at this
        have h_ce_restrict :
            μ[stoppedValue f M | hL.measurableSpace]
              =ᵐ[μ.restrict {ω | L ω = ↑k}]
              μ[stoppedValue f M | ℱ k] :=
          condExp_ae_eq_restrict_of_measurableSpace_eq_on
            hL.measurableSpace_le (ℱ.le k) (hL.measurableSet_eq' k)
            (fun t => by rw [Set.inter_comm]; exact hL.measurableSet_inter_eq_iff t k)
        have h_restrict := (ae_restrict_iff'
          (ℱ.le _ _ (hL.measurableSet_eq k))).mp h_ce_restrict
        filter_upwards [h_restrict, h_ineq_k] with ω hω_ce hω_ineq hLk
        calc stoppedProcess f M k ω
            ≤ (μ[stoppedValue f M | ℱ k]) ω := hω_ineq
          _ = (μ[stoppedValue f M | hL.measurableSpace]) ω := (hω_ce hLk).symm
      · have hNk : N < k := Nat.lt_of_not_le hkN
        filter_upwards with ω hLk
        exfalso
        have : L ω ≤ ↑N := hL_bdd ω
        rw [hLk] at this
        exact Nat.not_lt.mpr (mod_cast this) hNk
    filter_upwards [h_key] with ω hω
    have h_sv_eq : stoppedValue f L ω = stoppedProcess f M (L ω).untopA ω := by
      simp only [stoppedValue]
      rw [stoppedProcess_eq_of_le ((coe_untopA_eq _ (hL_ne_top ω)).le.trans (hLM ω))]
    rw [h_sv_eq]
    exact hω _ (coe_untopA_eq _ (hL_ne_top ω)).symm

