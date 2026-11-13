/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace TheoryOfProbability3

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A *decreasing filtration* on `(Ω, m0)` is a sequence of sub-σ-algebras
`ℱ n ⊆ m0` that is antitone in `n` (i.e. `ℱ 0 ⊇ ℱ 1 ⊇ ℱ 2 ⊇ ⋯`). This is the
natural index structure for backwards martingales, where conditioning
σ-algebras shrink as `n → ∞`. -/
structure DecreasingFiltration (Ω : Type*) (m0 : MeasurableSpace Ω) where
  seq : ℕ → MeasurableSpace Ω
  antitone' : Antitone seq
  le' : ∀ n, seq n ≤ m0

attribute [coe] DecreasingFiltration.seq

/-- Allow a `DecreasingFiltration` to be applied as a function `ℕ → MeasurableSpace Ω`
via its underlying sequence `seq`. -/
instance : CoeFun (DecreasingFiltration Ω m0) (fun _ => ℕ → MeasurableSpace Ω) where
  coe := DecreasingFiltration.seq

/-- The *tail σ-algebra* of a decreasing filtration `ℱ`, defined as the
intersection `⨅ n, ℱ n`. This is the σ-algebra of events that lie in every
`ℱ n`, i.e. the limit as the filtration shrinks. -/
@[reducible]
def DecreasingFiltration.tailAlgebra (ℱ : DecreasingFiltration Ω m0) :
    MeasurableSpace Ω :=
  ⨅ n, ℱ.seq n

/-- The tail σ-algebra of a decreasing filtration is contained in the ambient
σ-algebra `m0`. -/
theorem DecreasingFiltration.tailAlgebra_le (ℱ : DecreasingFiltration Ω m0) :
    ℱ.tailAlgebra ≤ m0 :=
  le_trans (iInf_le _ 0) (ℱ.le' 0)

/-- The tail σ-algebra is contained in every component `ℱ n` of the filtration. -/
theorem DecreasingFiltration.tailAlgebra_le_seq (ℱ : DecreasingFiltration Ω m0)
    (n : ℕ) : ℱ.tailAlgebra ≤ ℱ.seq n :=
  iInf_le _ n

/-- A *backwards martingale* with respect to a decreasing filtration `ℱ` and
measure `μ` is a process `M : ℕ → Ω → ℝ` such that `M 0` is integrable, each
`M n` is `ℱ n`-strongly measurable, and `M n = μ[M 0 | ℱ n]` `μ`-a.e.
Equivalently, `E(M n | ℱ n+1) = M n+1` for all `n` (with the filtration shrinking
as `n` grows). This corresponds to the setting of Durrett's backwards
martingale convergence theorem: `X_{-∞} = lim_{n → -∞} X_n` exists a.s. and in
`L¹`. -/
structure IsBackwardsMartingale (M : ℕ → Ω → ℝ) (ℱ : DecreasingFiltration Ω m0)
    (μ : Measure Ω) : Prop where
  integrable_zero : Integrable (M 0) μ
  adapted : ∀ n, StronglyMeasurable[ℱ n] (M n)
  condExp_ae_eq : ∀ n, M n =ᵐ[μ] μ[M 0 | ℱ n]

/-- Every term `M n` of a backwards martingale is integrable, since it is
`μ`-a.e. equal to the integrable conditional expectation `μ[M 0 | ℱ n]`. -/
theorem IsBackwardsMartingale.integrable [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {ℱ : DecreasingFiltration Ω m0}
    (hM : IsBackwardsMartingale M ℱ μ) (n : ℕ) : Integrable (M n) μ := by
  rw [integrable_congr (hM.condExp_ae_eq n)]
  exact integrable_condExp

/-- A backwards martingale is uniformly integrable in `L¹`: this follows from the
standard fact that the family of conditional expectations `{μ[M 0 | ℱ n]}` of a
single integrable function `M 0` is uniformly integrable. -/
theorem IsBackwardsMartingale.uniformIntegrable [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {ℱ : DecreasingFiltration Ω m0}
    (hM : IsBackwardsMartingale M ℱ μ) : UniformIntegrable M 1 μ :=
  (hM.integrable_zero.uniformIntegrable_condExp ℱ.le').ae_eq
    (fun n => (hM.condExp_ae_eq n).symm)

/-- Identification of the a.s. limit of conditional expectations along a
decreasing sequence of σ-algebras. Suppose `m n` is any sequence of
sub-σ-algebras of `m0`, `g` is integrable, and `μ[g | m n] → h` pointwise a.e.
with `h` integrable and measurable with respect to the limit σ-algebra
`⨅ n, m n`. Then `h = μ[g | ⨅ n, m n]` `μ`-a.e. This is the key step needed to
conclude Lévy's downward theorem from a.s. convergence of the conditional
expectations. -/
theorem condExp_antitone_limit_eq [IsFiniteMeasure μ]
    (g : Ω → ℝ) (m : ℕ → MeasurableSpace Ω)
    (hm_le : ∀ n, m n ≤ m0)
    (hg : Integrable g μ)
    (h : Ω → ℝ)
    (hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)))
    (hh_int : Integrable h μ)
    (hh_meas : StronglyMeasurable[⨅ n, m n] h) :
    h =ᵐ[μ] μ[g | ⨅ n, m n] := by
  have hm_inf_le : ⨅ n, m n ≤ m0 := le_trans (iInf_le _ 0) (hm_le 0)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_inf_le hg
    (fun s _ _ => hh_int.integrableOn) ?_ hh_meas.aestronglyMeasurable
  intro s hs hμs

  have hs_n : ∀ n, MeasurableSet[m n] s := fun n => (iInf_le m n) s hs

  have hint_eq : ∀ n, ∫ x in s, (μ[g | m n]) x ∂μ = ∫ x in s, g x ∂μ :=
    fun n => setIntegral_condExp (hm_le n) hg (hs_n n)

  have hui : UniformIntegrable (fun n => (μ[g | m n] : Ω → ℝ)) 1 μ :=
    hg.uniformIntegrable_condExp (ℱ := m) hm_le

  have haem : ∀ n, AEStronglyMeasurable (fun ω => (μ[g | m n]) ω) μ :=
    fun n => (stronglyMeasurable_condExp (m := m n)).aestronglyMeasurable.mono (hm_le n)

  have hL1 : Tendsto (fun n => eLpNorm ((fun ω => (μ[g | m n]) ω) - h) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
      (memLp_one_iff_integrable.mpr hh_int) hui.2.1
      (tendstoInMeasure_of_tendsto_ae haem hh_ae)

  have hL1' : Tendsto (fun n => ∫⁻ x, ‖(μ[g | m n]) x - h x‖ₑ ∂μ) atTop (𝓝 0) := by
    simp_rw [← eLpNorm_one_eq_lintegral_enorm]; convert hL1 using 1

  have hsetint := tendsto_setIntegral_of_L1 h hh_int
    (Filter.Eventually.of_forall fun n => integrable_condExp) hL1' s

  exact tendsto_nhds_unique (hsetint.congr hint_eq) tendsto_const_nhds





end TheoryOfProbability3
