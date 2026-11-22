/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Atlas.BooleanFunctions.code.PCP
import Atlas.BooleanFunctions.code.UniqueGames
import Atlas.BooleanFunctions.code.MajorityStablest
import Atlas.BooleanFunctions.code.Talagrand
import Atlas.BooleanFunctions.code.Borel
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.MultilinearExtension

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option maxHeartbeats 800000

namespace Hardness

open SimpleGraph

noncomputable def dinurSafraConstant : ℝ := 10 * Real.sqrt 5 - 21

def IsPolyTimeComputable {numVerts : ℕ → ℕ}
    (_ : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m))) : Prop :=
  ∃ (steps : ℕ → ℕ), PCP.IsPolynomial steps ∧ ∀ (m : ℕ), numVerts m ≤ steps m

def IsPolyTimeVertexCoverReduction {numVerts : ℕ → ℕ}
    (reduce : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m))) : Prop :=
  PCP.IsPolynomial numVerts ∧ IsPolyTimeComputable reduce

def IsNPHardToApproximateVertexCover (α : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∀ (L : PCP.Language), PCP.InNP L →
      ∃ (numVerts : ℕ → ℕ)
        (reduce : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m)))
        (kFn : ℕ → ℕ),
        IsPolyTimeVertexCoverReduction reduce ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m →
          (reduce m x).vertexCoverNum ≤ ↑(kFn m)) ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m →
          (α - ε) * (↑(kFn m) : ℝ) ≤ ↑((reduce m x).vertexCoverNum.toNat))

end Hardness

open Finset BigOperators Real MeasureTheory ProbabilityTheory

namespace BooleanFourier

lemma gaussianNoiseOperator_monomial {n : ℕ} (ρ : ℝ) (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ w : EuclideanSpace ℝ (Fin n),
      (∏ i ∈ S, ((ρ • x + Real.sqrt (1 - ρ ^ 2) • w) i))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
    ρ ^ S.card * ∏ i ∈ S, x i := by

  rw [← map_pi_eq_stdGaussian (ι := Fin n)]
  rw [integral_map (Measurable.aemeasurable (by fun_prop))
    (by fun_prop : AEStronglyMeasurable _ _)]

  simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

  have h_eq : ∀ w : Fin n → ℝ,
      ∏ i ∈ S, (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * w i) =
      ∏ i : Fin n, (if i ∈ S then (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * w i) else 1) := by
    intro w
    rw [← Finset.prod_filter]
    congr 1; ext i; simp
  simp_rw [h_eq]

  rw [integral_fintype_prod_eq_prod
    (fun i t => if i ∈ S then (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * t) else 1)]

  have h_eval : ∀ i : Fin n,
      ∫ (t : ℝ), (if i ∈ S then ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * t else 1)
        ∂gaussianReal 0 1 = if i ∈ S then ρ * x.ofLp i else 1 := by
    intro i
    split_ifs with h
    · have h1 : Integrable (fun _ : ℝ => ρ * x.ofLp i) (gaussianReal 0 1) := integrable_const _
      have h2 : Integrable (fun t : ℝ => Real.sqrt (1 - ρ ^ 2) * t) (gaussianReal 0 1) :=
        IsGaussian.integrable_id.const_mul _
      rw [integral_add h1 h2]
      have h3 : ∫ (_ : ℝ), ρ * x.ofLp i ∂gaussianReal 0 1 = ρ * x.ofLp i := by
        simp [integral_const]
      have h4 : ∫ (a : ℝ), Real.sqrt (1 - ρ ^ 2) * a ∂gaussianReal 0 1 = 0 := by
        rw [show (fun a => Real.sqrt (1 - ρ ^ 2) * a) =
          (fun a => Real.sqrt (1 - ρ ^ 2) * id a) from rfl]
        rw [integral_const_mul]
        simp [integral_id_gaussianReal]
      rw [h3, h4, add_zero]
    · simp [integral_const]
  simp_rw [h_eval]

  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

lemma integral_sq_gaussianReal :
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1 : Measure ℝ) = 1 := by
  have hvar : Var[fun x : ℝ => x; (gaussianReal 0 1 : Measure ℝ)] = (1 : ℝ) := by
    have h := @variance_fun_id_gaussianReal (0 : ℝ) (1 : NNReal)
    norm_cast at h
  have hvar2 : Var[fun x : ℝ => x; (gaussianReal 0 1 : Measure ℝ)] =
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1 : Measure ℝ) := by
    rw [show (fun x : ℝ => x) = id from rfl,
      variance_eq_integral measurable_id.aemeasurable]
    simp only [id, integral_id_gaussianReal, sub_zero]
  linarith

lemma coord_integral_factor {n : ℕ} (S T : Finset (Fin n)) (k : Fin n) :
    ∫ t : ℝ, ((if k ∈ S then t else (1 : ℝ)) * (if k ∈ T then t else (1 : ℝ)))
      ∂(gaussianReal 0 1 : Measure ℝ) =
    if (k ∈ S ∧ k ∈ T) then 1 else if (k ∈ S ∨ k ∈ T) then 0 else 1 := by
  by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;>
    simp only [hS, hT, ite_true, ite_false, and_self, and_true, true_and, or_true, or_false]
  · have : (fun t : ℝ => t * t) = (fun t => t ^ 2) := by ext; ring
    rw [this]; exact integral_sq_gaussianReal
  · simp only [mul_one]; exact integral_id_gaussianReal
  · simp only [one_mul]; exact integral_id_gaussianReal
  · simp only [mul_one]; rw [integral_const]; simp

lemma prod_coord_factors_eq {n : ℕ} (S T : Finset (Fin n)) :
    (∏ k : Fin n,
      (if (k ∈ S ∧ k ∈ T) then (1 : ℝ) else if (k ∈ S ∨ k ∈ T) then 0 else 1)) =
    if S = T then 1 else 0 := by
  split_ifs with hST
  · subst hST
    apply Finset.prod_eq_one; intro k _; simp
  · have hex : ∃ k : Fin n, (k ∈ S ∧ k ∉ T) ∨ (k ∉ S ∧ k ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext (fun k => by specialize h k; tauto))
    obtain ⟨k, hk⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rcases hk with ⟨hkS, hkT⟩ | ⟨hkS, hkT⟩ <;> simp [hkS, hkT]

lemma integral_monomial_mul_monomial_stdGaussian {n : ℕ}
    (S T : Finset (Fin n)) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      (∏ i ∈ S, x i) * (∏ j ∈ T, x j)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
    if S = T then 1 else 0 := by

  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb]

  have h_rw : ∀ v : Fin n → ℝ, (∏ i ∈ S, v i) * (∏ j ∈ T, v j) =
      ∏ k : Fin n, ((if k ∈ S then v k else 1) * (if k ∈ T then v k else 1)) := by
    intro v
    have hS : (∏ i ∈ S, v i) = ∏ k : Fin n, (if k ∈ S then v k else 1) := by
      symm
      rw [show (∏ k : Fin n, (if k ∈ S then v k else 1)) =
        (∏ k ∈ Finset.univ, (if k ∈ S then v k else 1)) from rfl,
        Finset.prod_ite_mem Finset.univ S (fun i => v i)]; simp
    have hT : (∏ j ∈ T, v j) = ∏ k : Fin n, (if k ∈ T then v k else 1) := by
      symm
      rw [show (∏ k : Fin n, (if k ∈ T then v k else 1)) =
        (∏ k ∈ Finset.univ, (if k ∈ T then v k else 1)) from rfl,
        Finset.prod_ite_mem Finset.univ T (fun i => v i)]; simp
    rw [hS, hT, ← Finset.prod_mul_distrib]
  simp_rw [h_rw]

  rw [integral_fintype_prod_eq_prod
    (fun k (t : ℝ) => (if k ∈ S then t else 1) * (if k ∈ T then t else 1))]

  simp_rw [coord_integral_factor S T]

  exact prod_coord_factors_eq S T

lemma integrable_monomial_noise_pi {n : ℕ} (S : Finset (Fin n))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun w : Fin n → ℝ =>
      ∏ i ∈ S, (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * w i))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have h_eq : (fun w : Fin n → ℝ => ∏ i ∈ S, (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * w i)) =
      (fun w => ∏ i : Fin n,
        (fun (j : Fin n) => (fun (t : ℝ) => if j ∈ S then (ρ * x.ofLp j + Real.sqrt (1 - ρ ^ 2) * t)
          else 1)) i (w i)) := by
    ext w; simp only
    rw [← Finset.prod_filter]; congr 1; ext i; simp
  rw [h_eq]
  exact Integrable.fintype_prod (f := fun j t => if j ∈ S then (ρ * x.ofLp j + Real.sqrt (1 - ρ ^ 2) * t) else 1)
    (fun i => by
      by_cases hi : i ∈ S
      · simp [hi]; exact (integrable_const _).add (IsGaussian.integrable_id.const_mul _)
      · simp [hi])

lemma integrable_monomial_noise_stdGaussian {n : ℕ} (S : Finset (Fin n))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      ∏ i ∈ S, ((ρ • x + Real.sqrt (1 - ρ ^ 2) • w) i))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [show (fun w : EuclideanSpace ℝ (Fin n) => ∏ i ∈ S, ((ρ • x + Real.sqrt (1 - ρ ^ 2) • w) i)) =
    (fun w : EuclideanSpace ℝ (Fin n) => ∏ i ∈ S, (ρ * x.ofLp i + Real.sqrt (1 - ρ ^ 2) * w.ofLp i))
    from by ext w; simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]]
  exact (hmp.integrable_comp_emb hemb).mp (integrable_monomial_noise_pi S ρ x)

theorem noiseStability_eq_gaussianNoiseStability_multilinear
    {n : ℕ} {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ_lt : ρ < 1)
    (f : (Fin n → Bool) → ℝ)
    (hbv : IsBooleanValued f) (hbal : IsBalanced f) :
    noiseStability ρ f =
      GaussianStability.gaussianNoiseStability ρ hρ_nonneg (le_of_lt hρ_lt)
        (fun x : EuclideanSpace ℝ (Fin n) =>
          multilinearExtension f (fun i => x i)) := by

  rw [noiseStability_eq_sum]
  symm

  simp only [GaussianStability.gaussianNoiseStability, GaussianStability.gaussianNoiseOperator,
    multilinearExtension]

  have h_inner : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ w : EuclideanSpace ℝ (Fin n),
        (∑ S : Finset (Fin n), fourierCoeff f S * ∏ i ∈ S, (ρ • x + Real.sqrt (1 - ρ ^ 2) • w) i)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      ∑ S : Finset (Fin n), fourierCoeff f S * (ρ ^ S.card * ∏ i ∈ S, x i) := by
    intro x
    rw [integral_finset_sum _ (fun S _ =>
      Integrable.const_mul (integrable_monomial_noise_stdGaussian S ρ x) _)]
    congr 1; ext S
    rw [integral_const_mul]
    congr 1
    exact gaussianNoiseOperator_monomial ρ S x
  simp_rw [h_inner]

  have h_prod : ∀ x : EuclideanSpace ℝ (Fin n),
      (∑ S : Finset (Fin n), fourierCoeff f S * ∏ i ∈ S, x i) *
      (∑ S : Finset (Fin n), fourierCoeff f S * (ρ ^ S.card * ∏ i ∈ S, x i)) =
      ∑ T : Finset (Fin n), ∑ S : Finset (Fin n),
        fourierCoeff f T * fourierCoeff f S * ρ ^ S.card *
          ((∏ i ∈ T, x i) * (∏ i ∈ S, x i)) := by
    intro x; simp_rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext T; congr 1; ext S; ring
  simp_rw [h_prod]

  have hint_prod : ∀ (T S : Finset (Fin n)),
      Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (∏ i ∈ T, x i) * (∏ i ∈ S, x i))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro T S
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
    have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    rw [show (fun x : EuclideanSpace ℝ (Fin n) => (∏ i ∈ T, x i) * (∏ i ∈ S, x i)) =
        (fun x : EuclideanSpace ℝ (Fin n) => (∏ i ∈ T, x.ofLp i) * (∏ i ∈ S, x.ofLp i))
      from rfl]
    exact (hmp.integrable_comp_emb hemb).mp
      (by
        have h_rw2 : ∀ v : Fin n → ℝ, (∏ i ∈ T, v i) * (∏ i ∈ S, v i) =
            ∏ k : Fin n, ((if k ∈ T then v k else 1) * (if k ∈ S then v k else 1)) := by
          intro v
          have hT : (∏ i ∈ T, v i) = ∏ k : Fin n, (if k ∈ T then v k else 1) := by
            symm; rw [show (∏ k : Fin n, (if k ∈ T then v k else 1)) =
              (∏ k ∈ Finset.univ, (if k ∈ T then v k else 1)) from rfl,
              Finset.prod_ite_mem Finset.univ T (fun i => v i)]; simp
          have hS : (∏ j ∈ S, v j) = ∏ k : Fin n, (if k ∈ S then v k else 1) := by
            symm; rw [show (∏ k : Fin n, (if k ∈ S then v k else 1)) =
              (∏ k ∈ Finset.univ, (if k ∈ S then v k else 1)) from rfl,
              Finset.prod_ite_mem Finset.univ S (fun i => v i)]; simp
          rw [hT, hS, ← Finset.prod_mul_distrib]
        simp_rw [h_rw2]
        exact Integrable.fintype_prod
          (f := fun k t => (if k ∈ T then t else 1) * (if k ∈ S then t else 1))
          (fun k => by
            by_cases hT : k ∈ T <;> by_cases hS : k ∈ S <;> simp [hT, hS]
            ·

              have hmem : MemLp (fun (x : ℝ) => x) 2 (gaussianReal 0 1) :=
                memLp_id_gaussianReal (p := 2) (μ := 0) (v := 1)
              have h2 := hmem.integrable_sq
              exact h2.congr (by filter_upwards; intro t; show t ^ 2 = t * t; ring)
            · exact IsGaussian.integrable_id
            · exact IsGaussian.integrable_id))
  rw [integral_finset_sum _ (fun T _ => integrable_finset_sum _ (fun S _ =>
    (hint_prod T S).const_mul _))]
  simp_rw [integral_finset_sum _ (fun S _ =>
    (hint_prod _ S).const_mul _)]
  simp_rw [integral_const_mul]

  simp_rw [integral_monomial_mul_monomial_stdGaussian]

  simp_rw [mul_ite, mul_one, mul_zero]

  rw [Finset.sum_comm]
  congr 1; ext S
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma multilinearExtension_integral_stdGaussian_eq_zero
    {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hbal : IsBalanced f) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      multilinearExtension f (fun i => x i)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) = 0 := by
  simp only [multilinearExtension]
  have hint : ∀ S : Finset (Fin n),
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => fourierCoeff f S * ∏ i ∈ S, x i)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro S
    apply Integrable.const_mul
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
    have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    rw [show (fun x : EuclideanSpace ℝ (Fin n) => ∏ i ∈ S, x i) =
        (fun x : EuclideanSpace ℝ (Fin n) => ∏ i ∈ S, x.ofLp i) from rfl]
    exact (hmp.integrable_comp_emb hemb).mp (by
      show Integrable (fun w : Fin n → ℝ => ∏ i ∈ S, w i)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      have h_eq2 : (fun w : Fin n → ℝ => ∏ i ∈ S, w i) =
          (fun w => ∏ i : Fin n,
            (fun (j : Fin n) => (fun (t : ℝ) => if j ∈ S then t else 1)) i (w i)) := by
        ext w
        simp only
        rw [← Finset.prod_filter]
        congr 1
        ext i
        simp
      rw [h_eq2]
      exact Integrable.fintype_prod
        (f := fun j t => if j ∈ S then t else 1)
        (fun i => by
          by_cases hi : i ∈ S
          · simp only [hi, ↓reduceIte]
            exact IsGaussian.integrable_id
          · simp only [hi, ↓reduceIte]
            exact integrable_const _))
  rw [integral_finset_sum _ (fun S _ => hint S)]
  simp_rw [integral_const_mul]
  have h_mono : ∀ S : Finset (Fin n),
      (∫ x : EuclideanSpace ℝ (Fin n), ∏ i ∈ S, x i
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) = if S = ∅ then 1 else 0 := by
    intro S
    have h := integral_monomial_mul_monomial_stdGaussian S ∅
    simp only [Finset.prod_empty, mul_one] at h
    linarith
  simp_rw [h_mono]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h_empty : fourierCoeff f ∅ = boolExpectation f := by
    simp only [fourierCoeff, boolExpectation, chi, Finset.prod_empty, mul_one]
  rw [h_empty]
  exact hbal

noncomputable def lowDegreePart {n : ℕ} (d : ℕ) (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), levelComponent k f x

end BooleanFourier
