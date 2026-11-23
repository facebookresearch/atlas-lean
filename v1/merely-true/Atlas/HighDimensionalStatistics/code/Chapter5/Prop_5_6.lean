/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_5
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

set_option maxHeartbeats 4800000

open MeasureTheory InformationTheory MeasureTheory.Measure

namespace Rigollet.Chapter5

/-- Invariance of KL divergence under pushforward by a measurable equivalence:
`KL(e_* μ ‖ e_* ν) = KL(μ ‖ ν)`. -/
lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  haveI : IsFiniteMeasure (μ.map e) := by
    constructor; rw [map_apply e.measurable MeasurableSet.univ]; exact measure_lt_top μ _
  haveI : IsFiniteMeasure (ν.map e) := by
    constructor; rw [map_apply e.measurable MeasurableSet.univ]; exact measure_lt_top ν _
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]

  have hac_fwd : μ ≪ ν → μ.map e ≪ ν.map e :=
    e.measurableEmbedding.absolutelyContinuous_map
  have hac_bwd : μ.map e ≪ ν.map e → μ ≪ ν := by
    intro h

    have hμ : μ = (μ.map e).map e.symm := (MeasurableEquiv.map_symm_map e).symm
    have hν : ν = (ν.map e).map e.symm := (MeasurableEquiv.map_symm_map e).symm
    rw [hμ, hν]
    exact e.symm.measurableEmbedding.absolutelyContinuous_map h
  by_cases hac : μ ≪ ν
  · simp only [hac_fwd hac, hac, if_true]

    have hmpν : MeasurePreserving e ν (ν.map e) := ⟨e.measurable, rfl⟩
    rw [← hmpν.lintegral_comp_emb e.measurableEmbedding]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have : ¬ (μ.map e ≪ ν.map e) := fun h => hac (hac_bwd h)
    simp [this, hac]

/-- Two-factor tensorisation of KL divergence for product probability measures:
`KL(P₁ × P₂ ‖ Q₁ × Q₂) = KL(P₁ ‖ Q₁) + KL(P₂ ‖ Q₂)`. -/
lemma klDiv_prod_of_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    klDiv (P₁.prod P₂) (Q₁.prod Q₂) = klDiv P₁ Q₁ + klDiv P₂ Q₂ := by

  rw [← Measure.compProd_const (μ := P₁) (ν := P₂),
      ← Measure.compProd_const (μ := Q₁) (ν := Q₂)]

  rw [InformationTheory.klDiv_compProd_eq_add]
  congr 1


  rw [Measure.compProd_const, Measure.compProd_const]


  have h1 : P₁.prod P₂ = (P₂.prod P₁).map Prod.swap :=
    (Measure.prod_swap (μ := P₂) (ν := P₁)).symm
  have h2 : P₁.prod Q₂ = (Q₂.prod P₁).map Prod.swap :=
    (Measure.prod_swap (μ := Q₂) (ν := P₁)).symm

  rw [h1, h2]
  rw [show (Prod.swap : β × α → α × β) =
    ⇑(MeasurableEquiv.prodComm (α := β) (β := α)) from rfl]
  rw [klDiv_map_measurableEquiv (MeasurableEquiv.prodComm (α := β) (β := α))]

  rw [← Measure.compProd_const (μ := P₂) (ν := P₁),
      ← Measure.compProd_const (μ := Q₂) (ν := P₁)]
  exact klDiv_compProd_left P₂ Q₂ (ProbabilityTheory.Kernel.const β P₁)

end Rigollet.Chapter5


/-- `n`-fold tensorisation of KL: for independent product probability measures
indexed by `Fin n`, `KL(∏ᵢ Pᵢ ‖ ∏ᵢ Qᵢ) = ∑ᵢ KL(Pᵢ ‖ Qᵢ)`. -/
theorem Rigollet.Chapter5.prop_5_6_tensorization_nfold
    {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)]
    (P Q : (i : Fin n) → Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i : Fin n, klDiv (P i) (Q i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have heq : Measure.pi P = Measure.pi Q := by
      have h1 := Measure.pi_of_empty (fun i : Fin 0 => P i)
      have h2 := Measure.pi_of_empty (fun i : Fin 0 => Q i)
      rw [h1, h2]
    rw [heq, klDiv_self]

  | succ n ih =>
    have hmpP := measurePreserving_piFinSuccAbove P 0
    have hmpQ := measurePreserving_piFinSuccAbove Q 0
    set e := MeasurableEquiv.piFinSuccAbove α 0

    have hP_map : Measure.pi P =
        ((P 0).prod (Measure.pi (fun j => P (Fin.succAbove 0 j)))).map e.symm := by
      have h := hmpP.map_eq
      have h2 := congr_arg (·.map e.symm) h
      simp only [Measure.map_map e.symm.measurable e.measurable] at h2
      rw [show (⇑e.symm) ∘ (⇑e) = id from funext (fun x => e.symm_apply_apply x)] at h2
      rw [Measure.map_id] at h2
      exact h2

    have hQ_map : Measure.pi Q =
        ((Q 0).prod (Measure.pi (fun j => Q (Fin.succAbove 0 j)))).map e.symm := by
      have h := hmpQ.map_eq
      have h2 := congr_arg (·.map e.symm) h
      simp only [Measure.map_map e.symm.measurable e.measurable] at h2
      rw [show (⇑e.symm) ∘ (⇑e) = id from funext (fun x => e.symm_apply_apply x)] at h2
      rw [Measure.map_id] at h2
      exact h2

    rw [hP_map, hQ_map]
    rw [klDiv_map_measurableEquiv e.symm]
    rw [klDiv_prod_of_isProbabilityMeasure]
    rw [ih (fun j => P (Fin.succAbove 0 j)) (fun j => Q (Fin.succAbove 0 j))]
    rw [Fin.sum_univ_succAbove _ 0]

noncomputable section

namespace Rigollet.Chapter5

/-- Bundled Proposition 5.6: KL divergence is nonnegative (Gibbs), satisfies
the real-valued Gibbs inequality, and tensorises across products (both binary
and `n`-fold). -/
theorem prop_5_6_bundle :

    (∀ {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω), (0 : ENNReal) ≤ klDiv P Q) ∧

    (∀ {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
      [IsFiniteMeasure P] [IsFiniteMeasure Q]
      (_ : P.AbsolutelyContinuous Q) (_ : Integrable (llr P Q) P),
      (0 : ℝ) ≤ ∫ x, llr P Q x ∂P + Q.real Set.univ - P.real Set.univ) ∧

    (∀ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
      {P1 Q1 : Measure α} {P2 Q2 : Measure β}
      (_ : IsProbabilityMeasure P1) (_ : IsProbabilityMeasure Q1)
      (_ : IsProbabilityMeasure P2) (_ : IsProbabilityMeasure Q2)
      (_ : P1.AbsolutelyContinuous Q1) (_ : P2.AbsolutelyContinuous Q2)
      (_ : Integrable (llr P1 Q1) P1) (_ : Integrable (llr P2 Q2) P2),
      klDiv (P1.prod P2) (Q1.prod Q2) = klDiv P1 Q1 + klDiv P2 Q2) ∧

    (∀ {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
      (P Q : (i : Fin n) → Measure (α i))
      [∀ i, IsProbabilityMeasure (P i)]
      [∀ i, IsProbabilityMeasure (Q i)],
      klDiv (Measure.pi P) (Measure.pi Q) = ∑ i : Fin n, klDiv (P i) (Q i)) :=
  ⟨fun P Q => prop_5_6_nonneg P Q,
   fun hPQ h_int => prop_5_6_gibbs_real hPQ h_int,
   fun hP1 hQ1 hP2 hQ2 hPQ1 hPQ2 h_int1 h_int2 =>
     prop_5_6_tensorization hP1 hQ1 hP2 hQ2 hPQ1 hPQ2 h_int1 h_int2,
   fun P Q => prop_5_6_tensorization_nfold P Q⟩

end Rigollet.Chapter5
