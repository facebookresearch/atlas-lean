/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville

import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal

namespace GaussianLinearTransform

theorem gaussian_linear_transform_converse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (μ_Y μ_Z : Measure E) [IsGaussian μ_Y] [IsGaussian μ_Z]
    (hmean : ∀ L : StrongDual ℝ E, (μ_Y)[L] = (μ_Z)[L])
    (hvar : ∀ L : StrongDual ℝ E, Var[L; μ_Y] = Var[L; μ_Z]) :
    μ_Y = μ_Z := by
  have hchar : charFunDual μ_Y = charFunDual μ_Z := by
    ext L
    rw [IsGaussian.charFunDual_eq L, IsGaussian.charFunDual_eq L]
    simp only [integral_complex_ofReal]
    rw [hmean L, hvar L]
  have hcf : charFun μ_Y = charFun μ_Z := by
    ext t
    simp only [charFun_eq_charFunDual_toDualMap]
    exact congr_fun hchar (InnerProductSpace.toDualMap ℝ E t)
  exact Measure.ext_of_charFun hcf

section ConcreteRm

open WithLp Finset
open scoped MatrixOrder RealInnerProductSpace

variable {m : ℕ}

lemma coord_eq_inner_basisFun (i : Fin m) :
    (fun x : EuclideanSpace ℝ (Fin m) => WithLp.ofLp x i) =
    fun x => @inner ℝ _ _ ((EuclideanSpace.basisFun (Fin m) ℝ i : EuclideanSpace ℝ (Fin m))) x := by
  ext x
  simp only [EuclideanSpace.basisFun_apply, inner]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

lemma adjoint_toEuclideanCLM (A : Matrix (Fin m) (Fin m) ℝ) :
    ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A) =
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) Aᴴ := by
  change star (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A) = _
  rw [show Aᴴ = star A from rfl]
  exact ((Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).map_star' A).symm

lemma mulVec_ofLp_dotProduct_eq (A V : Matrix (Fin m) (Fin m) ℝ) (i k : Fin m) :
    Aᴴ.mulVec (EuclideanSpace.single i (1 : ℝ)).ofLp ⬝ᵥ
      V.mulVec (Aᴴ.mulVec (EuclideanSpace.single k (1 : ℝ)).ofLp) =
    (A * V * Aᴴ) i k := by
  have h_ofLp : ∀ (p : Fin m), (EuclideanSpace.single p (1 : ℝ)).ofLp = Pi.single p 1 := by
    intro p; ext j; simp [EuclideanSpace.single, Pi.single_apply]
  rw [h_ofLp, h_ofLp, mulVec_mulVec, mulVec_single, mulVec_single]
  have hop : ∀ (v : Fin m → ℝ), MulOpposite.op (1 : ℝ) • v = v := by
    intro v; ext j; show MulOpposite.op (1 : ℝ) • v j = v j; simp
  simp_rw [hop]
  simp only [dotProduct, col_apply, mul_apply, conjTranspose_apply, star_trivial]
  simp_rw [mul_sum, sum_mul]; rw [Finset.sum_comm]
  congr 1; ext x; congr 1; ext j; ring

theorem concrete_converse_covariance_entries
    (μ_Y μ_Z : Measure (EuclideanSpace ℝ (Fin m)))
    [IsGaussian μ_Y] [IsGaussian μ_Z]
    (hmY : ∫ x, id x ∂μ_Y = 0) (hmZ : ∫ x, id x ∂μ_Z = 0)
    (hcov : ∀ i k : Fin m,
      cov[fun x : EuclideanSpace ℝ (Fin m) => WithLp.ofLp x i,
          fun x => WithLp.ofLp x k; μ_Y] =
      cov[fun x : EuclideanSpace ℝ (Fin m) => WithLp.ofLp x i,
          fun x => WithLp.ofLp x k; μ_Z]) :
    μ_Y = μ_Z := by
  apply IsGaussian.ext
  · rw [hmY, hmZ]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
        covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
        covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    simp_rw [coord_eq_inner_basisFun] at hcov
    exact hcov i j

end ConcreteRm

end GaussianLinearTransform

namespace BetaIntegralBound

open MeasureTheory Set intervalIntegral Filter

noncomputable def R_beta (β : ℝ) (m : ℕ) : ℝ :=
  ∫ r in (0:ℝ)..1, r ^ m * (1 - r) ^ β

lemma Gamma_succ_le_two (β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    Real.Gamma (β + 1) ≤ 2 := by
  by_cases hβ0' : β = 0
  · subst hβ0'; simp only [zero_add]
    have : Real.Gamma 1 = 1 := by
      have h := Real.Gamma_nat_eq_factorial 0
      simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one] at h; exact h
    linarith
  by_cases hβ2' : β = 2
  · subst hβ2'
    have hG3 : Real.Gamma 3 = 2 := by
      have h := Real.Gamma_nat_eq_factorial 2; push_cast at h; convert h using 1; norm_num
    show Real.Gamma (2 + 1) ≤ 2
    rw [show (2 : ℝ) + 1 = 3 from by norm_num, hG3]
  have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ0')
  have hβ_lt2 : β < 2 := lt_of_le_of_ne hβ2 hβ2'
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma one_pos
    (by norm_num : (0:ℝ) < 3) (by linarith : 0 < 1 - β/2) (by linarith : 0 < β/2)
    (by ring : (1 - β/2) + β/2 = 1)
  rw [show (1 - β/2) * 1 + (β/2) * 3 = β + 1 from by ring] at h
  have hG1 : Real.Gamma 1 = 1 := by
    have h := Real.Gamma_nat_eq_factorial 0
    simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one] at h; exact h
  have hG3 : Real.Gamma 3 = 2 := by
    have h := Real.Gamma_nat_eq_factorial 2; push_cast at h; convert h using 1; norm_num
  rw [hG1, hG3] at h; simp only [Real.one_rpow, one_mul] at h
  calc Real.Gamma (β + 1) ≤ (2:ℝ) ^ (β/2) := h
    _ ≤ (2:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := by norm_num

theorem beta_integral_bound (m : ℕ) (hm : 1 ≤ m) (β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    R_beta β m ≤ 100 * (m : ℝ) ^ (-(1 + β)) := by
  unfold R_beta
  have hm_pos : (0 : ℝ) < ↑m := by positivity
  have hm_rpow_nonneg : (0 : ℝ) ≤ (↑m : ℝ) ^ (-(β + 1)) := Real.rpow_nonneg (le_of_lt hm_pos) _

  have hint_f : IntervalIntegrable (fun r => r ^ m * (1 - r) ^ β) volume 0 1 :=
    (ContinuousOn.mul (continuous_pow m).continuousOn
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun x _ => Or.inr hβ0))).intervalIntegrable_of_Icc (by norm_num)

  have hint_g : IntervalIntegrable (fun r => Real.exp (-(↑m * (1 - r))) * (1 - r) ^ β) volume 0 1 :=
    (ContinuousOn.mul
      (Continuous.continuousOn (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id) |>.neg)))
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun x _ => Or.inr hβ0))).intervalIntegrable_of_Icc (by norm_num)

  have step1 : ∫ r in (0:ℝ)..1, r ^ m * (1 - r) ^ β ≤
      ∫ r in (0:ℝ)..1, Real.exp (-(↑m * (1 - r))) * (1 - r) ^ β := by
    apply integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hint_f hint_g
    intro r hr; simp only [mem_Icc] at hr
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    calc r ^ m ≤ (Real.exp (-(1 - r))) ^ m := by
          apply pow_le_pow_left₀ hr.1
          have := Real.add_one_le_exp (-(1 - r)); linarith
        _ = Real.exp (-(↑m * (1 - r))) := by rw [← Real.exp_nat_mul]; ring_nf

  have step2 : ∫ r in (0:ℝ)..1, Real.exp (-(↑m * (1 - r))) * (1 - r) ^ β =
      ∫ u in (0:ℝ)..1, Real.exp (-(↑m * u)) * u ^ β := by
    convert integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun x => Real.exp (-(↑m * x)) * x ^ β) 1 using 1; norm_num

  have step3 : ∫ u in (0:ℝ)..1, Real.exp (-(↑m * u)) * u ^ β ≤
      ∫ u in Ioi (0:ℝ), u ^ β * Real.exp (-(↑m * u)) := by
    rw [integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp_rw [show ∀ x : ℝ, Real.exp (-(↑m * x)) * x ^ β = x ^ β * Real.exp (-(↑m * x))
      from fun x => mul_comm _ _]
    apply setIntegral_mono_set
    · have := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < β) le_rfl hm_pos
      simp only [neg_mul, Real.rpow_one] at this; exact this
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all; intro x hx; simp only [Pi.zero_apply]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (le_of_lt (Real.exp_pos _))
    · exact HasSubset.Subset.eventuallyLE Ioc_subset_Ioi_self

  have step4 : ∫ u in Ioi (0:ℝ), u ^ β * Real.exp (-(↑m * u)) =
      (↑m : ℝ) ^ (-(β + 1)) * Real.Gamma (β + 1) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith : -1 < β) hm_pos
    simp only [Real.rpow_one, div_one] at h
    simp_rw [show ∀ x : ℝ, Real.exp (-↑m * x) = Real.exp (-(↑m * x)) from fun x => by ring_nf] at h
    linarith

  have step5 : Real.Gamma (β + 1) ≤ 2 := Gamma_succ_le_two β hβ0 hβ2

  calc ∫ r in (0:ℝ)..1, r ^ m * (1 - r) ^ β
      ≤ ∫ r in (0:ℝ)..1, Real.exp (-(↑m * (1 - r))) * (1 - r) ^ β := step1
    _ = ∫ u in (0:ℝ)..1, Real.exp (-(↑m * u)) * u ^ β := step2
    _ ≤ ∫ u in Ioi (0:ℝ), u ^ β * Real.exp (-(↑m * u)) := step3
    _ = (↑m : ℝ) ^ (-(β + 1)) * Real.Gamma (β + 1) := step4
    _ ≤ (↑m : ℝ) ^ (-(β + 1)) * 2 := by nlinarith
    _ ≤ (↑m : ℝ) ^ (-(β + 1)) * 100 := by nlinarith
    _ = 100 * (↑m : ℝ) ^ (-(1 + β)) := by ring

end BetaIntegralBound

namespace BrownianCharacterization

structure HasIndependentGaussianIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  indep_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    iIndepFun (m := fun (_ : Fin n) => inferInstance)
      (fun (j : Fin n) (ω : Ω) => B (t j.succ) ω - B (t j.castSucc) ω) P
  gaussian_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    ∀ (j : Fin n), HasLaw
      (fun ω => B (t j.succ) ω - B (t j.castSucc) ω)
      (gaussianReal 0 (t j.succ - t j.castSucc)) P

structure HasBrownianCharacterization
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  gaussian_process : IsGaussianProcess B P
  mean_zero : ∀ (t : NNReal), ∫ ω, B t ω ∂P = 0
  covariance : ∀ (s t : NNReal), ∫ ω, B s ω * B t ω ∂P = min (s : ℝ) (t : ℝ)

lemma integral_eq_zero_of_hasLaw_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, X ω ∂P = 0 := by
  have key : ∫ x, id x ∂(P.map X) = ∫ ω, id (X ω) ∂P :=
    integral_map hX.aemeasurable (aestronglyMeasurable_id)
  simp only [id] at key
  rw [← key, hX.map_eq, integral_id_gaussianReal]

lemma integral_mul_self_of_hasLaw_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : NNReal}
    (hlaw : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω * X ω ∂P = (v : ℝ) := by
  have hmean : ∫ ω, X ω ∂P = 0 := integral_eq_zero_of_hasLaw_gaussianReal hlaw
  have hvar : Var[X; P] = (v : ℝ) := by
    rw [show Var[X; P] = Var[id ∘ X; P] from by simp,
        ← variance_map (by rw [hlaw.map_eq]; exact aemeasurable_id) hlaw.aemeasurable,
        hlaw.map_eq, variance_id_gaussianReal]
  rw [show (fun ω => X ω * X ω) = (fun ω => X ω ^ 2) from by ext; ring]
  linarith [variance_of_integral_eq_zero hlaw.aemeasurable hmean]


theorem isGaussianProcess_uncorrelated_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {X : ι → Ω → ℝ} {P : Measure Ω}
    (hgauss : IsGaussianProcess X P)
    (huncorr : ∀ i j, i ≠ j →
      ∫ ω, X i ω * X j ω ∂P = (∫ ω, X i ω ∂P) * ∫ ω, X j ω ∂P) :
    iIndepFun (m := fun _ => inferInstance) X P := by

  have hP : IsProbabilityMeasure P := hgauss.isProbabilityMeasure


  have hjoint_sub := hgauss.hasGaussianLaw Finset.univ

  let e : ↑(Finset.univ : Finset ι) ≃ ι := Equiv.subtypeUnivEquiv (Finset.mem_univ)

  have hjoint : HasGaussianLaw (fun ω ↦ (X · ω)) P := by
    have := hjoint_sub.map_equiv_fun
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun (_ : ι) ↦ ℝ) e)
    convert this using 1

  have hcov : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0 := by
    intro i j hij
    rw [ProbabilityTheory.covariance_eq_sub
      (hgauss.hasGaussianLaw_eval i).memLp_two
      (hgauss.hasGaussianLaw_eval j).memLp_two]
    simp only [Pi.mul_apply]
    linarith [huncorr i j hij]
  exact hjoint.iIndepFun_of_covariance_eq_zero hcov

noncomputable def partialSumCLM {α : Type*} [Fintype α] (n : ℕ) (pos : α → Fin (n + 1)) :
    (Fin n → ℝ) →L[ℝ] (α → ℝ) where
  toFun v a := ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < (pos a).val), v k
  map_add' x y := by ext a; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    ext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [Finset.mul_sum]
  cont := by
    apply continuous_pi; intro a; apply continuous_finset_sum; intro k _
    exact (ContinuousLinearMap.proj (R := ℝ) k).continuous

lemma fin_telescope_sum {n : ℕ} (f : Fin (n + 1) → ℝ) (hf0 : f 0 = 0) (j : Fin (n + 1)) :
    f j = ∑ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k.val < j.val),
      (f k.succ - f k.castSucc) := by
  rcases j with ⟨j, hj⟩
  induction j with
  | zero => simp [hf0]
  | succ m ih =>
    have hm : m < n + 1 := by omega
    rw [show (Finset.univ : Finset (Fin n)).filter (fun k => k.val < m + 1) =
      ((Finset.univ : Finset (Fin n)).filter (fun k => k.val < m)) ∪
        ({⟨m, by omega⟩} : Finset (Fin n)) from by
      ext ⟨k, hk⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton, Fin.mk.injEq]
      omega]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]; intro ⟨k, _⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.mk.injEq]
      omega)]
    rw [Finset.sum_singleton, ← ih hm]
    have h1 : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, hj⟩ := by ext; simp
    have h2 : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, hm⟩ := by ext; simp [Fin.castSucc]
    rw [h1, h2]; ring

theorem indepGaussInc_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasIndependentGaussianIncrements B P) :
    IsGaussianProcess B P where
  hasGaussianLaw I := by
    classical

    let J := insert (0 : NNReal) I
    have hJ_card_pos : 0 < J.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
    set m := J.card - 1 with hm_def
    have hm1 : J.card = m + 1 := (Nat.succ_pred_eq_of_pos hJ_card_pos).symm

    let t : Fin (m + 1) → NNReal := J.orderEmbOfFin hm1
    have ht_mono : StrictMono t := (J.orderEmbOfFin hm1).strictMono
    have ht_zero : t 0 = 0 := by
      show (J.orderEmbOfFin hm1) ⟨0, _⟩ = 0
      rw [Finset.orderEmbOfFin_zero]
      exact (Finset.min'_le _ 0 (Finset.mem_insert_self _ _)).antisymm (zero_le _)

    have hΔ_gauss : HasGaussianLaw (fun ω (j : Fin m) =>
        B (t j.succ) ω - B (t j.castSucc) ω) P := by
      apply iIndepFun.hasGaussianLaw
      · intro j
        exact ⟨by rw [(h.gaussian_increments m t ht_mono ht_zero j).map_eq]; infer_instance⟩
      · exact h.indep_increments m t ht_mono ht_zero

    let e := J.orderIsoOfFin hm1
    let pos : ↑I → Fin (m + 1) :=
      fun ⟨x, hx⟩ => e.symm ⟨x, Finset.mem_insert_of_mem hx⟩
    let L := partialSumCLM m pos

    suffices hsuff : ⇑L ∘ (fun ω (j : Fin m) => B (t j.succ) ω - B (t j.castSucc) ω) =
        fun ω => I.restrict (B · ω) by
      rw [← hsuff]; exact hΔ_gauss.map L
    ext ω ⟨x, hx⟩
    simp only [Function.comp_apply, Finset.restrict_def]

    have hpos : t (pos ⟨x, hx⟩) = x := by
      show (J.orderEmbOfFin hm1) (e.symm ⟨x, Finset.mem_insert_of_mem hx⟩) = x
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    have key := fin_telescope_sum (fun j => B (t j) ω)
      (by simp [ht_zero, h.zero_at_origin]) (pos ⟨x, hx⟩)
    rw [hpos] at key
    exact key.symm

theorem indepGaussInc_covariance_le
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasIndependentGaussianIncrements B P)
    (s t : NNReal) (hst : s ≤ t) :
    ∫ ω, B s ω * B t ω ∂P = (s : ℝ) := by
  by_cases hs : s = 0
  · subst hs; simp [h.zero_at_origin]
  · have hs_pos : (0 : NNReal) < s := pos_iff_ne_zero.mpr hs
    have hBs_eq : ∀ ω, B s ω = B s ω - B 0 ω := fun ω => by simp [h.zero_at_origin]
    have hlaw_Bs : HasLaw (P := P) (fun ω => B s ω - B 0 ω) (gaussianReal 0 s) := by
      have hinc := h.gaussian_increments 1 ![0, s]
        (by intro i j hij; fin_cases i <;> fin_cases j <;>
            simp_all [Matrix.cons_val_zero, Matrix.cons_val_one])
        (by simp [Matrix.cons_val_zero]) ⟨0, by omega⟩
      simp only [Fin.succ_mk, Fin.castSucc_mk] at hinc
      simp only [show (![0, s] : Fin 2 → NNReal) ⟨1, by omega⟩ = s from by simp,
                 show (![0, s] : Fin 2 → NNReal) ⟨0, by omega⟩ = 0 from by simp,
                 tsub_zero] at hinc
      exact hinc
    haveI : IsProbabilityMeasure P := hlaw_Bs.isProbabilityMeasure
    have hBs_sq : ∫ ω, B s ω * B s ω ∂P = (s : ℝ) := by
      rw [show (fun ω => B s ω * B s ω) =
          (fun ω => (B s ω - B 0 ω) * (B s ω - B 0 ω)) from by ext ω; simp [h.zero_at_origin]]
      exact integral_mul_self_of_hasLaw_gaussianReal hlaw_Bs
    by_cases hst_eq : s = t
    · subst hst_eq; exact hBs_sq
    · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      have hpart_mono : StrictMono (![0, s, t] : Fin 3 → NNReal) := by
        intro a b hab
        have ha := a.isLt; have hb := b.isLt; have hab' : a.val < b.val := hab
        fin_cases a <;> fin_cases b <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
          first | omega | exact hs_pos | exact lt_trans hs_pos hst_lt | exact hst_lt | linarith
      have hiIndep := h.indep_increments 2 ![0, s, t] hpart_mono rfl
      have hindep_raw := hiIndep.indepFun
        (show (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ from by decide)
      have hf0_eq : (fun ω => B ((![0, s, t] : Fin 3 → NNReal)
          (Fin.succ ⟨0, by omega⟩)) ω -
          B ((![0, s, t] : Fin 3 → NNReal) (Fin.castSucc ⟨0, by omega⟩)) ω) =
          (fun ω => B s ω - B 0 ω) := by
        ext ω; simp [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ, Fin.castSucc]
      have hf1_eq : (fun ω => B ((![0, s, t] : Fin 3 → NNReal)
          (Fin.succ ⟨1, by omega⟩)) ω -
          B ((![0, s, t] : Fin 3 → NNReal) (Fin.castSucc ⟨1, by omega⟩)) ω) =
          (fun ω => B t ω - B s ω) := by
        ext ω; simp [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ, Fin.castSucc]
      have hindep : IndepFun (fun ω => B s ω) (fun ω => B t ω - B s ω) P := by
        rw [show (fun ω => B s ω) = (fun ω => B s ω - B 0 ω) from funext hBs_eq,
            ← hf0_eq, ← hf1_eq]; exact hindep_raw
      have hlaw_inc : HasLaw (P := P) (fun ω => B t ω - B s ω)
          (gaussianReal 0 (t - s)) := by
        rw [← hf1_eq]; exact h.gaussian_increments 2 ![0, s, t] hpart_mono rfl ⟨1, by omega⟩
      have hmemLp_Bs := hlaw_Bs.hasGaussianLaw.memLp_two
      have hmemLp_inc := hlaw_inc.hasGaussianLaw.memLp_two
      have hasm_Bs : AEStronglyMeasurable (fun ω => B s ω) P :=
        hmemLp_Bs.aestronglyMeasurable.congr (.symm (.of_forall hBs_eq))
      have hasm_inc : AEStronglyMeasurable (fun ω => B t ω - B s ω) P :=
        hmemLp_inc.aestronglyMeasurable
      have hint_sq : Integrable (fun ω => B s ω * B s ω) P := by
        rw [show (fun ω => B s ω * B s ω) = (fun ω => (B s ω - B 0 ω) * (B s ω - B 0 ω)) from
            by ext ω; simp [h.zero_at_origin]]
        exact MemLp.integrable_mul (p := 2) (q := 2) hmemLp_Bs hmemLp_Bs
      have hint_cross : Integrable (fun ω => B s ω * (B t ω - B s ω)) P := by
        rw [show (fun ω => B s ω * (B t ω - B s ω)) = (fun ω => (B s ω - B 0 ω) *
            (B t ω - B s ω)) from by ext ω; simp [h.zero_at_origin]]
        exact MemLp.integrable_mul (p := 2) (q := 2) hmemLp_Bs hmemLp_inc
      rw [show (fun ω => B s ω * B t ω) =
          (fun ω => B s ω * B s ω + B s ω * (B t ω - B s ω)) from by ext ω; ring,
          integral_add hint_sq hint_cross,
          show ∫ ω, B s ω * (B t ω - B s ω) ∂P = 0 from by
            rw [hindep.integral_fun_mul_eq_mul_integral hasm_Bs hasm_inc,
                show ∫ ω, B s ω ∂P = 0 from by
                  rw [show (fun ω => B s ω) = (fun ω => B s ω - B 0 ω) from funext hBs_eq]
                  exact integral_eq_zero_of_hasLaw_gaussianReal hlaw_Bs,
                zero_mul],
          hBs_sq, add_zero]

theorem indepGaussInc_covariance
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasIndependentGaussianIncrements B P)
    (s t : NNReal) :
    ∫ ω, B s ω * B t ω ∂P = min (s : ℝ) (t : ℝ) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left (by exact_mod_cast hst)]
    exact indepGaussInc_covariance_le h s t hst
  · rw [show (fun ω => B s ω * B t ω) = (fun ω => B t ω * B s ω) from by ext ω; ring,
        min_comm, min_eq_left (by exact_mod_cast hts)]
    exact indepGaussInc_covariance_le h t s hts


theorem brownianChar_indep_increments
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasBrownianCharacterization B P)
    (n : ℕ) (t : Fin (n + 1) → NNReal)
    (ht : StrictMono t) (ht0 : t 0 = 0) :
    iIndepFun (m := fun (_ : Fin n) => inferInstance)
      (fun (j : Fin n) (ω : Ω) => B (t j.succ) ω - B (t j.castSucc) ω) P := by

  have hgp_inc : IsGaussianProcess
      (fun (j : Fin n) (ω : Ω) => B (t j.succ) ω - B (t j.castSucc) ω) P :=
    h.gaussian_process.of_isGaussianProcess fun j => ⟨{t j.castSucc, t j.succ},
      { toFun x := x ⟨t j.succ, by simp⟩ - x ⟨t j.castSucc, by simp⟩
        map_add' x y := by simp [sub_add_sub_comm]
        map_smul' c x := by simp [smul_sub, mul_sub]
        cont := by fun_prop },
      by intro ω; simp [Finset.restrict_def]⟩

  apply isGaussianProcess_uncorrelated_iIndepFun hgp_inc
  intro i j hij
  haveI : IsProbabilityMeasure P := h.gaussian_process.isProbabilityMeasure


  have hmemLp := fun (k : Fin n) =>
    (h.gaussian_process.hasGaussianLaw_fun_sub (s := t k.succ) (t := t k.castSucc)).memLp_two
  have hint := fun (k : Fin n) => (hmemLp k).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmean_k : ∀ (k : Fin n), ∫ ω, (B (t k.succ) ω - B (t k.castSucc) ω) ∂P = 0 := by
    intro k
    rw [integral_sub
      ((h.gaussian_process.hasGaussianLaw_eval (t k.succ)).memLp_two.integrable (by norm_num))
      ((h.gaussian_process.hasGaussianLaw_eval (t k.castSucc)).memLp_two.integrable (by norm_num)),
      h.mean_zero, h.mean_zero, sub_self]

  rw [hmean_k i, hmean_k j, mul_zero]

  have h_expand : ∀ ω, (B (t i.succ) ω - B (t i.castSucc) ω) *
      (B (t j.succ) ω - B (t j.castSucc) ω) =
      B (t i.succ) ω * B (t j.succ) ω - B (t i.succ) ω * B (t j.castSucc) ω -
      B (t i.castSucc) ω * B (t j.succ) ω + B (t i.castSucc) ω * B (t j.castSucc) ω :=
    fun ω => by ring
  simp_rw [h_expand]

  have hint_is_js := MemLp.integrable_mul (p := 2) (q := 2)
    (h.gaussian_process.hasGaussianLaw_eval (t i.succ)).memLp_two
    (h.gaussian_process.hasGaussianLaw_eval (t j.succ)).memLp_two
  have hint_is_jc := MemLp.integrable_mul (p := 2) (q := 2)
    (h.gaussian_process.hasGaussianLaw_eval (t i.succ)).memLp_two
    (h.gaussian_process.hasGaussianLaw_eval (t j.castSucc)).memLp_two
  have hint_ic_js := MemLp.integrable_mul (p := 2) (q := 2)
    (h.gaussian_process.hasGaussianLaw_eval (t i.castSucc)).memLp_two
    (h.gaussian_process.hasGaussianLaw_eval (t j.succ)).memLp_two
  have hint_ic_jc := MemLp.integrable_mul (p := 2) (q := 2)
    (h.gaussian_process.hasGaussianLaw_eval (t i.castSucc)).memLp_two
    (h.gaussian_process.hasGaussianLaw_eval (t j.castSucc)).memLp_two

  have step1 : ∫ ω, (B (t i.succ) ω * B (t j.succ) ω - B (t i.succ) ω * B (t j.castSucc) ω -
      B (t i.castSucc) ω * B (t j.succ) ω + B (t i.castSucc) ω * B (t j.castSucc) ω) ∂P =
      ∫ ω, (B (t i.succ) ω * B (t j.succ) ω + B (t i.castSucc) ω * B (t j.castSucc) ω) ∂P -
      ∫ ω, (B (t i.succ) ω * B (t j.castSucc) ω + B (t i.castSucc) ω * B (t j.succ) ω) ∂P := by
    have : (fun ω => B (t i.succ) ω * B (t j.succ) ω - B (t i.succ) ω * B (t j.castSucc) ω -
        B (t i.castSucc) ω * B (t j.succ) ω + B (t i.castSucc) ω * B (t j.castSucc) ω) =
        (fun ω => B (t i.succ) ω * B (t j.succ) ω + B (t i.castSucc) ω * B (t j.castSucc) ω) -
        (fun ω => B (t i.succ) ω * B (t j.castSucc) ω + B (t i.castSucc) ω * B (t j.succ) ω) := by
      funext ω; simp [Pi.sub_apply]; ring
    rw [this]; exact integral_sub (hint_is_js.add hint_ic_jc) (hint_is_jc.add hint_ic_js)
  have step2 : ∫ ω, (B (t i.succ) ω * B (t j.succ) ω +
      B (t i.castSucc) ω * B (t j.castSucc) ω) ∂P =
      ∫ ω, B (t i.succ) ω * B (t j.succ) ω ∂P +
      ∫ ω, B (t i.castSucc) ω * B (t j.castSucc) ω ∂P :=
    integral_add hint_is_js hint_ic_jc
  have step3 : ∫ ω, (B (t i.succ) ω * B (t j.castSucc) ω +
      B (t i.castSucc) ω * B (t j.succ) ω) ∂P =
      ∫ ω, B (t i.succ) ω * B (t j.castSucc) ω ∂P +
      ∫ ω, B (t i.castSucc) ω * B (t j.succ) ω ∂P :=
    integral_add hint_is_jc hint_ic_js

  rw [step1, step2, step3,
      h.covariance (t i.succ) (t j.succ),
      h.covariance (t i.succ) (t j.castSucc),
      h.covariance (t i.castSucc) (t j.succ),
      h.covariance (t i.castSucc) (t j.castSucc)]


  rcases lt_or_gt_of_ne hij with h_lt | h_gt
  ·
    have h_is_le_jc : (t i.succ : ℝ) ≤ (t j.castSucc : ℝ) := by
      exact_mod_cast ht.monotone (Fin.succ_le_castSucc_iff.mpr h_lt)
    have h_ic_le_jc : (t i.castSucc : ℝ) ≤ (t j.castSucc : ℝ) := by
      exact_mod_cast le_trans (le_of_lt (ht Fin.castSucc_lt_succ))
        (ht.monotone (Fin.succ_le_castSucc_iff.mpr h_lt))
    have h_jc_le_js : (t j.castSucc : ℝ) ≤ (t j.succ : ℝ) := by
      exact_mod_cast le_of_lt (ht Fin.castSucc_lt_succ)
    rw [min_eq_left (le_trans h_is_le_jc h_jc_le_js),
        min_eq_left h_is_le_jc,
        min_eq_left (le_trans h_ic_le_jc h_jc_le_js),
        min_eq_left h_ic_le_jc]
    ring
  ·
    have h_js_le_ic : (t j.succ : ℝ) ≤ (t i.castSucc : ℝ) := by
      exact_mod_cast ht.monotone (Fin.succ_le_castSucc_iff.mpr h_gt)
    have h_jc_le_ic : (t j.castSucc : ℝ) ≤ (t i.castSucc : ℝ) := by
      exact_mod_cast le_trans (le_of_lt (ht Fin.castSucc_lt_succ))
        (ht.monotone (Fin.succ_le_castSucc_iff.mpr h_gt))
    have h_ic_le_is : (t i.castSucc : ℝ) ≤ (t i.succ : ℝ) := by
      exact_mod_cast le_of_lt (ht Fin.castSucc_lt_succ)
    rw [min_eq_right (le_trans h_js_le_ic h_ic_le_is),
        min_eq_right (le_trans h_jc_le_ic h_ic_le_is),
        min_eq_right h_js_le_ic,
        min_eq_right h_jc_le_ic]
    ring


set_option maxHeartbeats 1600000 in
theorem brownianChar_gaussian_increments
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasBrownianCharacterization B P)
    (n : ℕ) (t : Fin (n + 1) → NNReal)
    (ht : StrictMono t) (ht0 : t 0 = 0)
    (j : Fin n) :
    HasLaw
      (fun ω => B (t j.succ) ω - B (t j.castSucc) ω)
      (gaussianReal 0 (t j.succ - t j.castSucc)) P := by
  set s := t j.castSucc; set u := t j.succ
  have hsu : s ≤ u := le_of_lt (ht (Fin.castSucc_lt_succ))
  have hsu_real : (s : ℝ) ≤ (u : ℝ) := by exact_mod_cast hsu
  have hgauss : HasGaussianLaw (fun ω => B u ω - B s ω) P := h.gaussian_process.hasGaussianLaw_fun_sub
  haveI : IsProbabilityMeasure P := h.gaussian_process.isProbabilityMeasure
  have hmemLp_u := (h.gaussian_process.hasGaussianLaw_eval u).memLp_two
  have hmemLp_s := (h.gaussian_process.hasGaussianLaw_eval s).memLp_two
  have hint_u : Integrable (fun ω => B u ω) P := hmemLp_u.integrable (by norm_num)
  have hint_s : Integrable (fun ω => B s ω) P := hmemLp_s.integrable (by norm_num)

  have hmean_inc : ∫ ω, (B u ω - B s ω) ∂P = 0 := by
    rw [integral_sub hint_u hint_s, h.mean_zero u, h.mean_zero s, sub_self]

  have hint_uu := MemLp.integrable_mul (p := 2) (q := 2) hmemLp_u hmemLp_u
  have hint_us := MemLp.integrable_mul (p := 2) (q := 2) hmemLp_u hmemLp_s
  have hint_su := MemLp.integrable_mul (p := 2) (q := 2) hmemLp_s hmemLp_u
  have hint_ss := MemLp.integrable_mul (p := 2) (q := 2) hmemLp_s hmemLp_s
  have h_uu : ∫ ω, B u ω * B u ω ∂P = (u : ℝ) := by rw [h.covariance u u, min_self]
  have h_us : ∫ ω, B u ω * B s ω ∂P = (s : ℝ) := by rw [h.covariance u s, min_eq_right hsu_real]
  have h_ss : ∫ ω, B s ω * B s ω ∂P = (s : ℝ) := by rw [h.covariance s s, min_self]
  have h_su : ∫ ω, B s ω * B u ω ∂P = (s : ℝ) := by rw [h.covariance s u, min_eq_left hsu_real]

  have hE_sq : ∫ ω, (B u ω - B s ω) ^ 2 ∂P = (u : ℝ) - (s : ℝ) := by
    simp_rw [show ∀ ω, (B u ω - B s ω) ^ 2 =
      B u ω * B u ω + B s ω * B s ω - (B u ω * B s ω + B s ω * B u ω) from fun ω => by ring]
    have step1 : ∫ ω, (B u ω * B u ω + B s ω * B s ω -
        (B u ω * B s ω + B s ω * B u ω)) ∂P =
        ∫ ω, (B u ω * B u ω + B s ω * B s ω) ∂P -
        ∫ ω, (B u ω * B s ω + B s ω * B u ω) ∂P :=
      integral_sub (hint_uu.add hint_ss) (hint_us.add hint_su)
    have step2 : ∫ ω, (B u ω * B u ω + B s ω * B s ω) ∂P =
        ∫ ω, B u ω * B u ω ∂P + ∫ ω, B s ω * B s ω ∂P :=
      integral_add hint_uu hint_ss
    have step3 : ∫ ω, (B u ω * B s ω + B s ω * B u ω) ∂P =
        ∫ ω, B u ω * B s ω ∂P + ∫ ω, B s ω * B u ω ∂P :=
      integral_add hint_us hint_su
    linarith
  have hvar_inc : Var[fun ω => B u ω - B s ω; P] = ((u : ℝ) - (s : ℝ)) := by
    rw [variance_of_integral_eq_zero hgauss.aemeasurable hmean_inc, hE_sq]
  have hv_nn : (0 : ℝ) ≤ (u : ℝ) - (s : ℝ) := sub_nonneg.mpr hsu_real

  constructor
  · exact hgauss.aemeasurable
  · rw [hgauss.isGaussian_map.eq_gaussianReal (P.map (fun ω => B u ω - B s ω))]
    congr 1
    · rw [integral_map hgauss.aemeasurable aestronglyMeasurable_id]; simp [hmean_inc]
    · rw [variance_map aemeasurable_id hgauss.aemeasurable, Function.id_comp, hvar_inc]
      ext; simp only [NNReal.coe_sub hsu, Real.coe_toNNReal _ hv_nn]

theorem indepGaussianIncrements_implies_characterization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasIndependentGaussianIncrements B P) :
    HasBrownianCharacterization B P where
  zero_at_origin := h.zero_at_origin
  gaussian_process := indepGaussInc_isGaussianProcess h
  mean_zero := by
    intro s
    by_cases hs : s = 0
    · simp [hs, h.zero_at_origin]
    · have hs_pos : (0 : NNReal) < s := pos_iff_ne_zero.mpr hs
      have hinc := h.gaussian_increments 1 ![0, s]
        (by intro i j hij; fin_cases i <;> fin_cases j <;>
            simp_all [Matrix.cons_val_zero, Matrix.cons_val_one])
        (by simp [Matrix.cons_val_zero])
        ⟨0, by omega⟩
      simp only [Fin.succ_mk, Fin.castSucc_mk] at hinc
      simp only [show (![0, s] : Fin 2 → NNReal) ⟨1, by omega⟩ = s from by simp,
                 show (![0, s] : Fin 2 → NNReal) ⟨0, by omega⟩ = 0 from by simp,
                 tsub_zero] at hinc
      have key : (fun ω => B s ω) = (fun ω => B s ω - B 0 ω) := by
        ext ω; simp [h.zero_at_origin]
      rw [key]
      exact integral_eq_zero_of_hasLaw_gaussianReal hinc
  covariance := indepGaussInc_covariance h

theorem characterization_implies_indepGaussianIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (h : HasBrownianCharacterization B P) :
    HasIndependentGaussianIncrements B P where
  zero_at_origin := h.zero_at_origin
  indep_increments := brownianChar_indep_increments h
  gaussian_increments := brownianChar_gaussian_increments h

theorem brownian_characterization_iff
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {P : Measure Ω} :
    HasIndependentGaussianIncrements B P ↔ HasBrownianCharacterization B P :=
  ⟨indepGaussianIncrements_implies_characterization,
   characterization_implies_indepGaussianIncrements⟩

end BrownianCharacterization

namespace GradientIntegrability

open BetaIntegralBound MeasureTheory Set intervalIntegral

structure IsIIDStdGaussian {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (P : Measure Ω) : Prop where
  indep : iIndepFun (m := fun _ => inferInstance) a P
  std_gaussian : ∀ k, HasLaw (a k) (gaussianReal 0 1) P

noncomputable def randomPowerSeries {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' k : ℕ, (a (k + 1) ω : ℂ) * z ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ)

noncomputable def powerSeriesDeriv {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' j : ℕ, (a (j + 1) ω : ℂ) * z ^ j

noncomputable def weightedGradientIntegral {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi),
    ∫ r in (0 : ℝ)..1,
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r

noncomputable def weightedGradientIntegralENNReal {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Set.Icc 0 (2 * Real.pi),
    ∫⁻ r : ℝ in Set.Icc 0 1,
      ENNReal.ofReal
        ((4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
         (1 - r) ^ β * r)


lemma measurableSet_summable_complex {Ω : Type*} [MeasurableSpace Ω]
    {f : ℕ → Ω → ℂ} (hf : ∀ j, Measurable (f j)) :
    MeasurableSet {ω | Summable (fun j => f j ω)} := by


  have equiv : ∀ ω, Summable (fun j => f j ω) ↔
    ∃ C : ℝ, ∀ n, ∑ i ∈ Finset.range n, ‖f i ω‖ ≤ C := by
    intro ω
    rw [← summable_norm_iff]
    constructor
    · intro hs
      exact ⟨∑' i, ‖f i ω‖, fun n => Summable.sum_le_tsum _ (fun i _ => norm_nonneg _) hs⟩
    · intro ⟨C, hC⟩
      exact summable_of_sum_range_le (fun _ => norm_nonneg _) hC
  have heq : {ω | Summable (fun j => f j ω)} =
    ⋃ q : ℕ, ⋂ n : ℕ, {ω | ∑ i ∈ Finset.range n, ‖f i ω‖ ≤ (q : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [equiv]
    constructor
    · rintro ⟨C, hC⟩
      exact ⟨Nat.ceil C, fun n => (hC n).trans (Nat.le_ceil C)⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le (Finset.measurable_sum _ (fun j _ => (hf j).norm)) measurable_const


lemma measurable_tsum_complex {Ω : Type*} [MeasurableSpace Ω]
    {f : ℕ → Ω → ℂ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun ω => ∑' j, f j ω) := by

  set Sn : ℕ → Ω → ℂ := fun n ω => ∑ j ∈ Finset.range n, f j ω
  have hSn : ∀ n, Measurable (Sn n) := fun n => Finset.measurable_sum _ (fun j _ => hf j)

  set SumSet := {ω : Ω | Summable (fun j => f j ω)}
  have hSumSet : MeasurableSet SumSet := measurableSet_summable_complex hf

  set T : ℕ → Ω → ℂ := fun n ω => SumSet.indicator (Sn n) ω
  have hT : ∀ n, Measurable (T n) := fun n => (hSn n).indicator hSumSet

  have hconv : ∀ ω, Filter.Tendsto (fun n => T n ω) Filter.atTop (nhds (∑' j, f j ω)) := by
    intro ω
    by_cases hω : ω ∈ SumSet
    ·
      simp only [T, Set.indicator_of_mem hω]
      exact hω.hasSum.tendsto_sum_nat
    ·
      simp only [T, Set.indicator_of_notMem hω]
      rw [tsum_eq_zero_of_not_summable hω]
      exact tendsto_const_nhds


  exact measurable_of_tendsto_metrizable hT (tendsto_pi_nhds.mpr hconv)


theorem measurable_weightedGradientIntegralENNReal
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ha : ∀ k, Measurable (a k)) (β : ℝ) :
    Measurable (weightedGradientIntegralENNReal a β) := by

  have h_meas_psd : ∀ z : ℂ, Measurable (fun ω => powerSeriesDeriv a z ω) := by
    intro z
    exact measurable_tsum_complex (fun j =>
      (Complex.measurable_ofReal.comp (ha (j + 1))).mul_const (z ^ j))


  unfold weightedGradientIntegralENNReal
  apply Measurable.lintegral_prod_right
  apply Measurable.lintegral_prod_right

  apply Measurable.ennreal_ofReal


  set_option maxHeartbeats 400000 in
  have h_joint : Measurable (fun (x : (Ω × ℝ) × ℝ) =>
      powerSeriesDeriv a (↑x.2 * Complex.exp (↑x.1.2 * Complex.I)) x.1.1) := by
    unfold powerSeriesDeriv
    exact measurable_tsum_complex (fun j => by
      apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp ((ha (j + 1)).comp measurable_fst.fst))
      · exact (((Complex.measurable_ofReal.comp measurable_snd).mul
            (Complex.continuous_exp.measurable.comp
              ((Complex.measurable_ofReal.comp measurable_fst.snd).mul
                measurable_const))).pow measurable_const))
  exact ((measurable_const.mul (h_joint.norm.pow measurable_const)).mul
    ((measurable_const.sub measurable_snd).pow measurable_const)).mul measurable_snd

lemma weightedGradientIntegralENNReal_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} (ha : ∀ k, AEMeasurable (a k) P) (β : ℝ) :
    AEMeasurable (weightedGradientIntegralENNReal a β) P := by


  set a' : ℕ → Ω → ℝ := fun k => (ha k).mk (a k)
  have ha' : ∀ k, Measurable (a' k) := fun k => (ha k).measurable_mk
  have hae : ∀ k, a k =ᵐ[P] a' k := fun k => (ha k).ae_eq_mk

  have hN : ∀ᵐ ω ∂P, ∀ k, a k ω = a' k ω :=
    eventually_countable_forall.mpr hae

  refine ⟨weightedGradientIntegralENNReal a' β,
    measurable_weightedGradientIntegralENNReal a' ha' β, ?_⟩
  filter_upwards [hN] with ω hω
  show weightedGradientIntegralENNReal a β ω = weightedGradientIntegralENNReal a' β ω
  unfold weightedGradientIntegralENNReal powerSeriesDeriv
  simp_rw [hω]


theorem setLIntegral_Icc_ofReal_eq_ofReal_intervalIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn f (Icc a b) MeasureTheory.volume)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ∫⁻ x in Icc a b, ENNReal.ofReal (f x) =
    ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (ofReal_integral_eq_lintegral_ofReal hint (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hnn x hx)).symm


theorem continuous_gradient_integrand
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω)
    (hcont_ps : Continuous (fun z => powerSeriesDeriv a z ω))
    (hβ : 0 ≤ β) :
    Continuous (Function.uncurry (fun (t : ℝ) (r : ℝ) =>
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
        (1 - r) ^ β * r)) := by

  show Continuous fun p : ℝ × ℝ =>
    (4 * ‖powerSeriesDeriv a (↑p.2 * Complex.exp (↑p.1 * Complex.I)) ω‖ ^ 4) *
      (1 - p.2) ^ β * p.2

  have h_z : Continuous (fun p : ℝ × ℝ => (↑p.2 : ℂ) * Complex.exp (↑p.1 * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))

  have h_ps : Continuous (fun p : ℝ × ℝ =>
      powerSeriesDeriv a (↑p.2 * Complex.exp (↑p.1 * Complex.I)) ω) :=
    hcont_ps.comp h_z

  have h_norm4 : Continuous (fun p : ℝ × ℝ =>
      ‖powerSeriesDeriv a (↑p.2 * Complex.exp (↑p.1 * Complex.I)) ω‖ ^ 4) :=
    (continuous_norm.comp h_ps).pow 4

  have h_4norm4 : Continuous (fun p : ℝ × ℝ =>
      4 * ‖powerSeriesDeriv a (↑p.2 * Complex.exp (↑p.1 * Complex.I)) ω‖ ^ 4) :=
    continuous_const.mul h_norm4

  have h_rpow : Continuous (fun p : ℝ × ℝ => (1 - p.2) ^ β) :=
    (continuous_const.sub continuous_snd).rpow_const (fun _ => Or.inr hβ)

  exact (h_4norm4.mul h_rpow).mul continuous_snd

theorem integrableOn_inner_gradient_integrand
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) (t : ℝ)
    (hcont_ps : Continuous (fun z => powerSeriesDeriv a z ω))
    (hβ : 0 ≤ β) :
    IntegrableOn
      (fun (r : ℝ) => (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
        (1 - r) ^ β * r)
      (Icc (0 : ℝ) 1) MeasureTheory.volume := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact ((continuous_gradient_integrand a β ω hcont_ps hβ).comp
    (Continuous.prodMk continuous_const continuous_id)).continuousOn


theorem integrableOn_outer_gradient_integrand
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω)
    (hcont_ps : Continuous (fun z => powerSeriesDeriv a z ω))
    (hβ : 0 ≤ β) :
    IntegrableOn
      (fun (t : ℝ) => ∫ r in (0 : ℝ)..1,
        (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
        (1 - r) ^ β * r)
      (Icc (0 : ℝ) (2 * Real.pi)) MeasureTheory.volume := by
  have hcont : Continuous (fun (t : ℝ) => ∫ r in (0 : ℝ)..1,
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r) :=
    continuous_parametric_intervalIntegral_of_continuous'
      (continuous_gradient_integrand a β ω hcont_ps hβ) 0 1
  exact hcont.integrableOn_Icc


theorem weightedGradientIntegralENNReal_eq_ofReal
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω)
    (hcont_ps : Continuous (fun z => powerSeriesDeriv a z ω))
    (hβ : 0 ≤ β) :
    weightedGradientIntegralENNReal a β ω =
    ENNReal.ofReal (weightedGradientIntegral a β ω) := by
  simp only [weightedGradientIntegralENNReal, weightedGradientIntegral]

  have integrand_nonneg : ∀ (t : ℝ) (r : ℝ), r ∈ Icc (0 : ℝ) 1 →
      0 ≤ (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
        (1 - r) ^ β * r := by
    intro t r hr
    simp only [mem_Icc] at hr
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (pow_nonneg (norm_nonneg _) 4)) (Real.rpow_nonneg (by linarith) β))
      hr.1


  have inner_eq : EqOn
      (fun (t : ℝ) => ∫⁻ (r : ℝ) in Icc (0 : ℝ) 1,
        ENNReal.ofReal
          ((4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
           (1 - r) ^ β * r))
      (fun (t : ℝ) => ENNReal.ofReal (∫ r in (0 : ℝ)..1,
        (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
        (1 - r) ^ β * r))
      (Icc (0 : ℝ) (2 * Real.pi)) := by
    intro t _ht
    exact setLIntegral_Icc_ofReal_eq_ofReal_intervalIntegral (by norm_num : (0 : ℝ) ≤ 1)
      (integrableOn_inner_gradient_integrand a β ω t hcont_ps hβ)
      (fun r hr => integrand_nonneg t r hr)

  rw [setLIntegral_congr_fun measurableSet_Icc inner_eq]

  rw [integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← integral_Icc_eq_integral_Ioc]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_outer_gradient_integrand a β ω hcont_ps hβ)
    (Filter.Eventually.of_forall (fun t => by
      apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      intro u hu
      exact integrand_nonneg t u hu))).symm




theorem weightedGradientIntegral_eq_toReal_of_lt_top
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω)
    (hcont_ps : Continuous (fun z => powerSeriesDeriv a z ω))
    (hβ : 0 ≤ β)
    (hfin : weightedGradientIntegralENNReal a β ω < ⊤) :
    weightedGradientIntegral a β ω =
    (weightedGradientIntegralENNReal a β ω).toReal := by
  rw [weightedGradientIntegralENNReal_eq_ofReal a β ω hcont_ps hβ]
  symm
  apply ENNReal.toReal_ofReal
  unfold weightedGradientIntegral
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro t _ht
  apply intervalIntegral.integral_nonneg (by linarith)
  intro r hr
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r ≤ 1 := hr.2
  have h1mr : 0 ≤ 1 - r := by linarith
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h1mr _)) hr0

lemma summable_odd_rpow_inv (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => ((2 * (n : ℝ) + 1) ^ p)⁻¹) := by
  have h : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ p)⁻¹) := by
    convert (Real.summable_nat_rpow_inv.mpr hp).comp_injective Nat.succ_injective using 1
    ext n; simp [Nat.cast_succ]
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => inv_anti₀ (by positivity)
      (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith))) h

lemma product_rpow_le (j k : ℕ) (β : ℝ) (hβ : 1 < β) :
    ((2 * (j : ℝ) + 1) * (2 * (k : ℝ) + 1)) ^ ((1 + β) / 2) ≤
    (2 * (j : ℝ) + 2 * k + 1) ^ (1 + β) := by
  calc ((2 * (j : ℝ) + 1) * (2 * k + 1)) ^ ((1 + β) / 2)
      ≤ ((2 * j + 2 * k + 1) ^ 2) ^ ((1 + β) / 2) :=
        Real.rpow_le_rpow (by positivity)
          (by nlinarith [sq_nonneg ((j : ℝ) - k)]) (by linarith)
    _ = (2 * j + 2 * k + 1) ^ (2 * ((1 + β) / 2)) := by
        rw [← Real.rpow_natCast (2 * (j : ℝ) + 2 * k + 1) 2,
            ← Real.rpow_mul (by positivity)]
        norm_cast
    _ = (2 * j + 2 * k + 1) ^ (1 + β) := by congr 1; ring

theorem summable_double_sum_rpow (β : ℝ) (hβ : 1 < β) :
    Summable (fun jk : ℕ × ℕ =>
      ((2 * (jk.1 : ℝ) + 2 * jk.2 + 1) ^ (1 + β))⁻¹) := by
  have hp : 1 < (1 + β) / 2 := by linarith
  have hsum := summable_odd_rpow_inv _ hp
  have hprod := Summable.mul_of_nonneg hsum hsum
    (fun n => by positivity) (fun n => by positivity)
  apply Summable.of_nonneg_of_le
    (f := fun jk : ℕ × ℕ =>
      ((2 * (jk.1 : ℝ) + 1) ^ ((1 + β) / 2))⁻¹ *
      ((2 * (jk.2 : ℝ) + 1) ^ ((1 + β) / 2))⁻¹)
    (fun _ => by positivity)
  · intro ⟨j, k⟩
    show ((2 * (j : ℝ) + 2 * k + 1) ^ (1 + β))⁻¹ ≤
      ((2 * (j : ℝ) + 1) ^ ((1 + β) / 2))⁻¹ *
      ((2 * (k : ℝ) + 1) ^ ((1 + β) / 2))⁻¹
    rw [← mul_inv,
        ← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*j+1)
          (by positivity : (0:ℝ) ≤ 2*k+1)]
    exact inv_anti₀ (by positivity) (product_rpow_le j k β hβ)
  · exact hprod

lemma R_beta_nonneg (β : ℝ) (_hβ : 0 ≤ β) (m : ℕ) : 0 ≤ R_beta β m := by
  unfold R_beta
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr; simp only [Set.mem_Icc] at hr
  exact mul_nonneg (pow_nonneg hr.1 m) (Real.rpow_nonneg (by linarith) β)

lemma R_beta_antitone {β₁ β₂ : ℝ} (hle : β₁ ≤ β₂) (hβ₁ : 0 < β₁) (m : ℕ) :
    R_beta β₂ m ≤ R_beta β₁ m := by
  unfold R_beta
  apply integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · exact (ContinuousOn.mul (continuous_pow m).continuousOn
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun x _ => Or.inr (le_of_lt (lt_of_lt_of_le hβ₁ hle))))).intervalIntegrable_of_Icc
      (by norm_num)
  · exact (ContinuousOn.mul (continuous_pow m).continuousOn
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun x _ => Or.inr (le_of_lt hβ₁)))).intervalIntegrable_of_Icc (by norm_num)
  · intro r hr
    simp only [Set.mem_Icc] at hr
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.1 m)
    by_cases h0 : r = 1
    · subst h0
      simp [Real.zero_rpow (ne_of_gt hβ₁),
            Real.zero_rpow (ne_of_gt (lt_of_lt_of_le hβ₁ hle))]
    · exact Real.rpow_le_rpow_of_exponent_ge
        (by linarith [lt_of_le_of_ne hr.2 h0]) (by linarith) hle

lemma cast_index_eq (j k : ℕ) :
    ((2 * j + 2 * k + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 2 * k + 1 := by
  push_cast; ring

theorem summable_beta_integrals_le2 (β : ℝ) (hβ1 : 1 < β) (hβ2 : β ≤ 2) :
    Summable (fun jk : ℕ × ℕ => R_beta β (2 * jk.1 + 2 * jk.2 + 1)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hds := summable_double_sum_rpow β hβ1
  apply Summable.of_nonneg_of_le
    (f := fun jk : ℕ × ℕ =>
      100 * ((2 * (jk.1 : ℝ) + 2 * jk.2 + 1) ^ (1 + β))⁻¹)
    (fun jk => R_beta_nonneg β hβ0 _)
  · intro ⟨j, k⟩
    have hm : 1 ≤ 2 * j + 2 * k + 1 := by omega
    have hbound := beta_integral_bound (2 * j + 2 * k + 1) hm β hβ0 hβ2
    simp only at hbound ⊢
    rw [cast_index_eq] at hbound
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * j + 2 * k + 1)] at hbound
    exact hbound
  · convert hds.const_smul (100 : ℝ) using 1

theorem summable_beta_integrals (β : ℝ) (hβ : 1 < β) :
    Summable (fun jk : ℕ × ℕ => R_beta β (2 * jk.1 + 2 * jk.2 + 1)) := by
  by_cases hβ2 : β ≤ 2
  · exact summable_beta_integrals_le2 β hβ hβ2
  · have hβ2' : 2 < β := by linarith [not_le.mp hβ2]
    have h2 := summable_beta_integrals_le2 2 (by norm_num) le_rfl
    exact Summable.of_nonneg_of_le (fun jk => R_beta_nonneg β (by linarith) _)
      (fun jk => R_beta_antitone (le_of_lt hβ2') (by norm_num : (0:ℝ) < 2) _) h2


lemma rhs_integrand_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℕ → Ω → ℝ) (_β : ℝ) (r : ℝ) :
    0 ≤ (∫ t in (0:ℝ)..(2 * Real.pi),
        ∫ ω, (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) ∂P) := by
  apply integral_nonneg_of_forall (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  intro t
  apply MeasureTheory.integral_nonneg
  intro ω
  positivity


lemma rhs_full_integrand_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℕ → Ω → ℝ) (β : ℝ) (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    0 ≤ (∫ t in (0:ℝ)..(2 * Real.pi),
        ∫ ω, (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) ∂P) *
      ((1 - r) ^ β * r) := by
  apply mul_nonneg
  · exact rhs_integrand_nonneg P a β r
  · exact mul_nonneg (Real.rpow_nonneg (by linarith [hr.1, hr.2]) β) hr.1


lemma rhs_integral_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℕ → Ω → ℝ) (β : ℝ) :
    0 ≤ ∫ r in (0:ℝ)..1,
      (∫ t in (0:ℝ)..(2 * Real.pi),
        ∫ ω, (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) ∂P) *
      ((1 - r) ^ β * r) := by
  apply integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro r hr
  exact rhs_full_integrand_nonneg P a β r hr


lemma weightedGradientIntegral_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) :
    0 ≤ weightedGradientIntegral a β ω := by
  unfold weightedGradientIntegral
  apply integral_nonneg_of_forall (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  intro t
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro r hr
  simp only [mem_Icc] at hr
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · exact Real.rpow_nonneg (by linarith) β
  · linarith


set_option maxHeartbeats 800000 in
theorem aesm_integrand_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) :
    AEStronglyMeasurable
      (fun (p : (ℝ × ℝ) × Ω) =>
        (4 * ‖powerSeriesDeriv a (↑p.1.1 * Complex.exp (↑p.1.2 * Complex.I)) p.2‖ ^ 4 : ℝ))
      ((volume.prod volume).prod P) := by
  have ha_aem : ∀ k, AEMeasurable (a k) P := fun k => (ha.std_gaussian k).aemeasurable
  set a' : ℕ → Ω → ℝ := fun k => (ha_aem k).mk (a k)
  have ha' : ∀ k, Measurable (a' k) := fun k => (ha_aem k).measurable_mk
  have hae : ∀ k, a k =ᵐ[P] a' k := fun k => (ha_aem k).ae_eq_mk
  have h_joint : Measurable (fun (p : (ℝ × ℝ) × Ω) =>
      powerSeriesDeriv a' (↑p.1.1 * Complex.exp (↑p.1.2 * Complex.I)) p.2) := by
    unfold powerSeriesDeriv
    exact measurable_tsum_complex (fun j => by
      apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp ((ha' (j + 1)).comp measurable_snd))
      · exact (((Complex.measurable_ofReal.comp measurable_fst.fst).mul
            (Complex.continuous_exp.measurable.comp
              ((Complex.measurable_ofReal.comp measurable_fst.snd).mul
                measurable_const))).pow measurable_const))
  have h_full_meas : Measurable (fun (p : (ℝ × ℝ) × Ω) =>
      (4 * ‖powerSeriesDeriv a' (↑p.1.1 * Complex.exp (↑p.1.2 * Complex.I)) p.2‖ ^ 4 : ℝ)) :=
    measurable_const.mul (h_joint.norm.pow measurable_const)
  refine h_full_meas.aestronglyMeasurable.congr ?_
  have hN : ∀ᵐ ω ∂P, ∀ k, a k ω = a' k ω := eventually_countable_forall.mpr hae
  have hN_prod : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).prod P), ∀ k, a k p.2 = a' k p.2 := by
    have : ((volume : Measure (ℝ × ℝ)).prod P) {x | ¬ ∀ k, a k x.2 = a' k x.2} = 0 := by
      have heq : {x : (ℝ × ℝ) × Ω | ¬ ∀ k, a k x.2 = a' k x.2} =
          univ ×ˢ {ω | ¬ ∀ k, a k ω = a' k ω} := by ext; simp
      rw [heq, Measure.prod_prod]
      simp only [mul_eq_zero]
      exact Or.inr hN
    exact this
  filter_upwards [hN_prod] with p hp
  congr 1; congr 1; congr 1
  unfold powerSeriesDeriv
  exact tsum_congr (fun j => by rw [hp (j + 1)])


set_option maxHeartbeats 800000 in
theorem aesm_fubini_omega_t
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) (β : ℝ) (hβ : 1 < β) :
    AEStronglyMeasurable
      (Function.uncurry (fun (ω : Ω) (t : ℝ) =>
        ∫ r in Ioc (0:ℝ) 1,
          (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
          (1 - r) ^ β * r))
      (P.prod volume) := by

  have ha_aem : ∀ k, AEMeasurable (a k) P := fun k => (ha.std_gaussian k).aemeasurable
  set a' : ℕ → Ω → ℝ := fun k => (ha_aem k).mk (a k)
  have ha' : ∀ k, Measurable (a' k) := fun k => (ha_aem k).measurable_mk
  have hae : ∀ k, a k =ᵐ[P] a' k := fun k => (ha_aem k).ae_eq_mk

  have h_psd_meas : Measurable (fun (p : (Ω × ℝ) × ℝ) =>
      powerSeriesDeriv a' (↑p.2 * Complex.exp (↑p.1.2 * Complex.I)) p.1.1) := by
    unfold powerSeriesDeriv
    exact measurable_tsum_complex (fun j => by
      apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp ((ha' (j + 1)).comp measurable_fst.fst))
      · exact (((Complex.measurable_ofReal.comp measurable_snd).mul
            (Complex.continuous_exp.measurable.comp
              ((Complex.measurable_ofReal.comp measurable_fst.snd).mul
                measurable_const))).pow measurable_const))
  have h_full_meas : Measurable (fun (p : (Ω × ℝ) × ℝ) =>
      (4 * ‖powerSeriesDeriv a' (↑p.2 * Complex.exp (↑p.1.2 * Complex.I)) p.1.1‖ ^ 4) *
      (1 - p.2) ^ β * p.2) := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact measurable_const.mul (h_psd_meas.norm.pow measurable_const)
      · exact (measurable_const.sub measurable_snd).pow_const β
    · exact measurable_snd

  set ν := (volume : Measure ℝ).restrict (Ioc (0:ℝ) 1)
  have h_int_aesm : AEStronglyMeasurable
      (fun (x : Ω × ℝ) => ∫ r in Ioc (0:ℝ) 1,
        (4 * ‖powerSeriesDeriv a' (↑r * Complex.exp (↑x.2 * Complex.I)) x.1‖ ^ 4) *
        (1 - r) ^ β * r)
      (P.prod volume) :=
    (h_full_meas.aestronglyMeasurable (μ := (P.prod volume).prod ν)).integral_prod_right'

  refine h_int_aesm.congr ?_
  have hN : ∀ᵐ ω ∂P, ∀ k, a k ω = a' k ω := eventually_countable_forall.mpr hae
  have hN_prod : ∀ᵐ p ∂(P.prod (volume : Measure ℝ)), ∀ k, a k p.1 = a' k p.1 := by
    show (P.prod (volume : Measure ℝ)) {x | ¬ ∀ k, a k x.1 = a' k x.1} = 0
    have heq : {x : Ω × ℝ | ¬ ∀ k, a k x.1 = a' k x.1} =
        {ω | ¬ ∀ k, a k ω = a' k ω} ×ˢ univ := by ext; simp
    rw [heq, Measure.prod_prod]
    simp only [mul_eq_zero, Measure.measure_univ_eq_zero]
    exact Or.inl hN
  filter_upwards [hN_prod] with ⟨ω, t⟩ hp
  simp only [Function.uncurry]
  congr 1
  ext r
  have : powerSeriesDeriv a' (↑r * Complex.exp (↑t * Complex.I)) ω =
      powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω := by
    unfold powerSeriesDeriv
    exact tsum_congr (fun j => by rw [hp (j + 1)])
  rw [this]






set_option maxHeartbeats 800000 in
theorem aEStronglyMeasurable_integrand_omega_r
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) :
    AEStronglyMeasurable (Function.uncurry (fun (ω : Ω) (r : ℝ) =>
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r))
    (P.prod (volume.restrict (Ioc 0 1))) := by

  have ha_aem : ∀ k, AEMeasurable (a k) P := fun k => (ha.std_gaussian k).aemeasurable
  set a' : ℕ → Ω → ℝ := fun k => (ha_aem k).mk (a k)
  have ha' : ∀ k, Measurable (a' k) := fun k => (ha_aem k).measurable_mk
  have hae : ∀ k, a k =ᵐ[P] a' k := fun k => (ha_aem k).ae_eq_mk

  have h_joint : Measurable (fun (p : Ω × ℝ) =>
      powerSeriesDeriv a' (↑p.2 * Complex.exp (↑t * Complex.I)) p.1) := by
    unfold powerSeriesDeriv
    exact measurable_tsum_complex (fun j => by
      apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp ((ha' (j + 1)).comp measurable_fst))
      · exact (((Complex.measurable_ofReal.comp measurable_snd).mul
            measurable_const).pow measurable_const))

  have h_full_meas : Measurable (fun (p : Ω × ℝ) =>
      (4 * ‖powerSeriesDeriv a' (↑p.2 * Complex.exp (↑t * Complex.I)) p.1‖ ^ 4) *
      (1 - p.2) ^ β * p.2) :=
    ((measurable_const.mul (h_joint.norm.pow measurable_const)).mul
      ((measurable_const.sub measurable_snd).pow measurable_const)).mul measurable_snd

  have h_aesm_full : AEStronglyMeasurable (Function.uncurry (fun (ω : Ω) (r : ℝ) =>
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r))
      (P.prod volume) := by
    refine h_full_meas.aestronglyMeasurable.congr ?_
    have hN : ∀ᵐ ω ∂P, ∀ k, a k ω = a' k ω := eventually_countable_forall.mpr hae
    have hN_prod : ∀ᵐ p ∂(P.prod (volume : Measure ℝ)), ∀ k, a k p.1 = a' k p.1 := by
      have : (P.prod (volume : Measure ℝ)) {x | ¬ ∀ k, a k x.1 = a' k x.1} = 0 := by
        have heq : {x : Ω × ℝ | ¬ ∀ k, a k x.1 = a' k x.1} =
            {ω | ¬ ∀ k, a k ω = a' k ω} ×ˢ univ := by ext; simp
        rw [heq, Measure.prod_prod]
        simp only [mul_eq_zero]
        exact Or.inl hN
      exact this
    filter_upwards [hN_prod] with p hp
    simp only [Function.uncurry]
    have heq_psd : powerSeriesDeriv a' (↑p.2 * Complex.exp (↑t * Complex.I)) p.1 =
        powerSeriesDeriv a (↑p.2 * Complex.exp (↑t * Complex.I)) p.1 := by
      unfold powerSeriesDeriv
      exact tsum_congr (fun j => by rw [hp (j + 1)])
    rw [heq_psd]

  exact h_aesm_full.mono_ac (Measure.AbsolutelyContinuous.prod
    Measure.AbsolutelyContinuous.rfl (Measure.absolutelyContinuous_restrict))





theorem aesm_integrand_prod_fwd
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) :
    MeasureTheory.AEStronglyMeasurable
      (fun (p : (ℝ × ℝ) × Ω) =>
        (4 * ‖powerSeriesDeriv a (↑p.1.1 * Complex.exp (↑p.1.2 * Complex.I)) p.2‖ ^ 4 : ℝ))
      ((MeasureTheory.volume.prod MeasureTheory.volume).prod P) :=
  aesm_integrand_prod ha


set_option maxHeartbeats 800000 in
theorem rhs_bound_integrable_fwd (β : ℝ) (hβ : 1 < β) :
    IntervalIntegrable (fun r =>
      (24 * Real.pi * ∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2)) *
      ((1 - r) ^ β * r)) MeasureTheory.volume 0 1 := by
  have hβ' : 0 < β := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]

  have h_eq : (fun r : ℝ =>
      (24 * Real.pi * ∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2)) *
      ((1 - r) ^ β * r)) =
    (fun r : ℝ => 24 * Real.pi *
      (∑' jk : ℕ × ℕ, (r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)))) := by
    ext r; simp only [mul_assoc]; rw [tsum_mul_right]
  rw [h_eq]
  apply Integrable.const_mul

  have h_cont : ∀ m : ℕ, Continuous (fun r : ℝ => r ^ m * ((1 - r) ^ β * r)) :=
    fun m => Continuous.mul (continuous_pow _)
      (Continuous.mul ((continuous_const.sub continuous_id).rpow continuous_const
        (fun _ => Or.inr hβ')) continuous_id)

  have h_intOn : ∀ m : ℕ, IntegrableOn (fun r : ℝ => r ^ m * ((1 - r) ^ β * r))
      (Ioc (0:ℝ) 1) volume :=
    fun m => ((h_cont m).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self

  have h_meas : ∀ jk : ℕ × ℕ, AEStronglyMeasurable
      (fun r => r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    fun jk => (h_cont (2 * jk.1 + 2 * jk.2)).aestronglyMeasurable

  have h_nonneg : ∀ jk : ℕ × ℕ, ∀ r ∈ Ioc (0:ℝ) 1,
      0 ≤ r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r) :=
    fun jk r hr => mul_nonneg (pow_nonneg (le_of_lt hr.1) _)
      (mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (le_of_lt hr.1))

  have hf'' : ∀ jk : ℕ × ℕ, AEMeasurable
      (fun r => ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ)
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    fun jk => (h_meas jk).enorm

  have h_lint_eq : ∀ jk : ℕ × ℕ,
      ∫⁻ r in Ioc (0:ℝ) 1, ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ =
      ENNReal.ofReal (∫ r in Ioc (0:ℝ) 1, r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) := by
    intro jk
    rw [← ofReal_integral_norm_eq_lintegral_enorm (h_intOn (2 * jk.1 + 2 * jk.2))]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr; dsimp only
    exact Real.norm_of_nonneg (h_nonneg jk r hr)

  have h_int_eq : ∀ jk : ℕ × ℕ,
      ∫ r in Ioc (0:ℝ) 1, r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r) =
      R_beta β (2 * jk.1 + 2 * jk.2 + 1) := by
    intro jk
    rw [show (∫ r in Ioc (0:ℝ) 1,
        r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) =
      (∫ r in (0:ℝ)..1,
        r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) from
      (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm]
    unfold R_beta; congr 1; ext r; ring

  have h_ne_top : ∑' jk : ℕ × ℕ,
      ∫⁻ r in Ioc (0:ℝ) 1, ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ ≠ ⊤ := by
    simp_rw [h_lint_eq, h_int_eq]
    exact (summable_beta_integrals β hβ).tsum_ofReal_ne_top

  refine ⟨?_, ?_⟩
  ·
    have h_nnnorm_meas : ∀ jk : ℕ × ℕ, AEMeasurable (fun r =>
        ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖₊)
        (volume.restrict (Ioc (0:ℝ) 1)) :=
      fun jk => (h_meas jk).aemeasurable.nnnorm
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply ((AEMeasurable.nnreal_tsum h_nnnorm_meas).coe_nnreal_real).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [NNReal.coe_tsum]; congr 1; ext jk
    rw [coe_nnnorm, Real.norm_of_nonneg (h_nonneg jk r hr)]
  ·
    rw [HasFiniteIntegral]
    calc ∫⁻ r in Ioc (0:ℝ) 1,
          ‖∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ
        ≤ ∫⁻ r in Ioc (0:ℝ) 1,
          ∑' jk : ℕ × ℕ, ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ := by
          apply lintegral_mono; intro r; exact enorm_tsum_le_tsum_enorm
      _ < ⊤ := by rw [lintegral_tsum hf'']; exact lt_top_iff_ne_top.mpr h_ne_top





lemma hasDerivAt_exp_sq_half' (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have h := (hasDerivAt_pow 2 t).div_const 2
    simp only [Nat.cast_ofNat] at h; convert h using 1; ring
  have h2 := ((Real.hasDerivAt_exp _).comp t h1)
  simp only [Function.comp_def] at h2; convert h2 using 1; ring

lemma hda_poly1 (t : ℝ) : HasDerivAt (fun t => t * Real.exp (t ^ 2 / 2))
    ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
  convert (hasDerivAt_id t).mul (hasDerivAt_exp_sq_half' t) using 1
  simp [id]; ring

lemma hda_poly2 (t : ℝ) : HasDerivAt (fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
    ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    convert (hasDerivAt_pow 2 t).const_add 1 using 1
    simp only [Nat.cast_ofNat]; ring
  convert hp.mul (hasDerivAt_exp_sq_half' t) using 1; ring

lemma hda_poly3 (t : ℝ) :
    HasDerivAt (fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
    ((3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t := by
    convert ((hasDerivAt_id t).const_mul 3).add (hasDerivAt_pow 3 t) using 1
    simp only [Nat.cast_ofNat]; ring
  convert hp.mul (hasDerivAt_exp_sq_half' t) using 1; ring

lemma fourth_deriv_exp_sq_half_zero :
    iteratedDeriv 4 (fun (t : ℝ) => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have h1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    ext t; exact (hasDerivAt_exp_sq_half' t).deriv
  rw [h1]
  have h2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t; exact (hda_poly1 t).deriv
  rw [h2]
  have h3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t; exact (hda_poly2 t).deriv
  rw [h3]
  rw [(hda_poly3 0).deriv]
  simp [Real.exp_zero]

lemma mgf_std_gaussian_eq :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 1) =
    fun t => Real.exp (t ^ 2 / 2) := by
  have : ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 1) =
      fun t => Real.exp ((0 : ℝ) * t + ↑(1:NNReal) * t ^ 2 / 2) :=
    ProbabilityTheory.mgf_id_gaussianReal
  ext t; rw [show (ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 1)) t = _ from
    congr_fun this t]; simp






lemma IsIIDStdGaussian.aestronglyMeasurable_coeff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) (k : ℕ) :
    AEStronglyMeasurable (a k) P :=
  (ha.std_gaussian k).aemeasurable.aestronglyMeasurable

theorem aesm_lhs_integrand
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) (β : ℝ) (hβ : 1 < β) :
    AEStronglyMeasurable (fun (r : ℝ) =>
      (∫ t in (0:ℝ)..(2 * Real.pi),
        ∫ ω, (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) ∂P) *
      ((1 - r) ^ β * r)) (volume.restrict (Set.uIoc 0 1)) := by

  apply AEStronglyMeasurable.mul
  ·


    have h_joint := aesm_integrand_prod ha

    have h_rt : AEStronglyMeasurable
        (fun rt : ℝ × ℝ =>
          ∫ ω, (4 * ‖powerSeriesDeriv a (↑rt.1 * Complex.exp (↑rt.2 * Complex.I)) ω‖ ^ 4) ∂P)
        (volume.prod volume) := h_joint.integral_prod_right'

    have h_rt_restr : AEStronglyMeasurable
        (fun rt : ℝ × ℝ =>
          ∫ ω, (4 * ‖powerSeriesDeriv a (↑rt.1 * Complex.exp (↑rt.2 * Complex.I)) ω‖ ^ 4) ∂P)
        (volume.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
      h_rt.mono_ac (Measure.AbsolutelyContinuous.prod
        Measure.AbsolutelyContinuous.rfl Measure.absolutelyContinuous_restrict)

    have h_r := h_rt_restr.integral_prod_right'

    apply (h_r.congr (Filter.Eventually.of_forall (fun r => ?_))).mono_measure
      Measure.restrict_le_self
    simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  ·
    exact (Continuous.mul
      ((continuous_const.sub continuous_id).rpow continuous_const
        (fun _ => Or.inr (by linarith : 0 < β)))
      continuous_id).aestronglyMeasurable


lemma continuous_pow_mul_rpow_mul' (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    Continuous (fun r : ℝ => r ^ m * ((1 - r) ^ β * r)) :=
  Continuous.mul (continuous_pow _)
    (Continuous.mul ((continuous_const.sub continuous_id).rpow continuous_const
      (fun _ => Or.inr hβ)) continuous_id)

lemma integrableOn_Ioc_pow_rpow_mul' (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ m * ((1 - r) ^ β * r)) (Ioc (0:ℝ) 1) volume :=
  ((continuous_pow_mul_rpow_mul' β hβ m).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Ioc_subset_Icc_self

lemma lintegral_enorm_eq_ofReal'' (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∫⁻ r in Ioc (0:ℝ) 1, ‖r ^ m * ((1 - r) ^ β * r)‖ₑ =
    ENNReal.ofReal (∫ r in Ioc (0:ℝ) 1, r ^ m * ((1 - r) ^ β * r)) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_Ioc_pow_rpow_mul' β hβ m)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr; simp only
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (pow_nonneg (le_of_lt hr.1) _)
    (mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (le_of_lt hr.1))

lemma integrableOn_tsum_nonneg {f : ℕ × ℕ → ℝ → ℝ}
    (h_meas : ∀ jk : ℕ × ℕ, AEStronglyMeasurable (f jk) (volume.restrict (Ioc (0:ℝ) 1)))
    (h_nonneg : ∀ jk : ℕ × ℕ, ∀ r ∈ Ioc (0:ℝ) 1, 0 ≤ f jk r)
    (h_ne_top : ∑' jk : ℕ × ℕ, ∫⁻ r in Ioc (0:ℝ) 1, ‖f jk r‖ₑ ≠ ⊤) :
    IntegrableOn (fun r => ∑' jk : ℕ × ℕ, f jk r) (Ioc (0:ℝ) 1) volume := by
  have hf'' : ∀ jk, AEMeasurable (fun r => ‖f jk r‖ₑ) (volume.restrict (Ioc (0:ℝ) 1)) :=
    fun jk => (h_meas jk).enorm
  refine ⟨?_, ?_⟩
  ·
    have h_nnnorm_meas : ∀ jk, AEMeasurable (fun r => ‖f jk r‖₊)
        (volume.restrict (Ioc (0:ℝ) 1)) :=
      fun jk => (h_meas jk).aemeasurable.nnnorm
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply ((AEMeasurable.nnreal_tsum h_nnnorm_meas).coe_nnreal_real).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [NNReal.coe_tsum]; congr 1; ext jk
    rw [coe_nnnorm, Real.norm_of_nonneg (h_nonneg jk r hr)]
  ·
    rw [HasFiniteIntegral]
    calc ∫⁻ r in Ioc (0:ℝ) 1, ‖∑' jk, f jk r‖ₑ
        ≤ ∫⁻ r in Ioc (0:ℝ) 1, ∑' jk, ‖f jk r‖ₑ := by
          apply lintegral_mono; intro r; exact enorm_tsum_le_tsum_enorm
        _ < ⊤ := by rw [lintegral_tsum hf'']; exact lt_top_iff_ne_top.mpr h_ne_top

theorem rhs_bound_integrable (β : ℝ) (hβ : 1 < β) :
    IntervalIntegrable (fun r =>
      (24 * Real.pi * ∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2)) *
      ((1 - r) ^ β * r)) MeasureTheory.volume 0 1 := by
  have hβ' : 0 < β := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]

  have h_eq : (fun r : ℝ =>
      (24 * Real.pi * ∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2)) *
      ((1 - r) ^ β * r)) =
    (fun r : ℝ => 24 * Real.pi *
      (∑' jk : ℕ × ℕ, (r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)))) := by
    ext r; simp only [mul_assoc]; rw [tsum_mul_right]
  rw [h_eq]

  apply Integrable.const_mul

  apply integrableOn_tsum_nonneg
  ·
    exact fun jk => (continuous_pow_mul_rpow_mul' β hβ' _).aestronglyMeasurable
  ·
    intro jk r hr
    exact mul_nonneg (pow_nonneg (le_of_lt hr.1) _)
      (mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (le_of_lt hr.1))
  ·
    simp_rw [lintegral_enorm_eq_ofReal'' β hβ',
      show ∀ jk : ℕ × ℕ,
        ∫ r in Ioc (0:ℝ) 1, r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r) =
        R_beta β (2 * jk.1 + 2 * jk.2 + 1) from fun jk => by
        rw [show (∫ r in Ioc (0:ℝ) 1,
            r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) =
          (∫ r in (0:ℝ)..1,
            r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) from
          (integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm]
        unfold R_beta; congr 1; ext r; ring]
    exact (summable_beta_integrals β hβ).tsum_ofReal_ne_top




lemma continuous_pow_mul_rpow_mul (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    Continuous (fun r : ℝ => r ^ m * ((1 - r) ^ β * r)) :=
  Continuous.mul (continuous_pow _)
    (Continuous.mul ((continuous_const.sub continuous_id).rpow continuous_const
      (fun _ => Or.inr hβ)) continuous_id)

lemma integrableOn_Ioc_pow_rpow_mul (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ m * ((1 - r) ^ β * r)) (Ioc (0:ℝ) 1) volume :=
  ((continuous_pow_mul_rpow_mul β hβ m).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Ioc_subset_Icc_self

lemma lintegral_enorm_eq_ofReal' (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∫⁻ r in Ioc (0:ℝ) 1, ‖r ^ m * ((1 - r) ^ β * r)‖ₑ =
    ENNReal.ofReal (∫ r in Ioc (0:ℝ) 1, r ^ m * ((1 - r) ^ β * r)) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_Ioc_pow_rpow_mul β hβ m)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr; simp only
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (pow_nonneg (le_of_lt hr.1) _)
    (mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (le_of_lt hr.1))

theorem radial_tsum_integral_eq (β : ℝ) (hβ : 1 < β) :
    ∫ r in (0:ℝ)..1,
      (∑' jk : ℕ × ℕ, r ^ (2 * jk.1 + 2 * jk.2)) * (1 - r) ^ β * r =
    ∑' jk : ℕ × ℕ, R_beta β (2 * jk.1 + 2 * jk.2 + 1) := by
  have hβ' : 0 < β := by linarith

  rw [integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

  simp_rw [mul_assoc, tsum_mul_right.symm]

  have h_meas : ∀ (jk : ℕ × ℕ), AEStronglyMeasurable
      (fun r => r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    fun jk => (continuous_pow_mul_rpow_mul β hβ' _).aestronglyMeasurable
  have h_ne_top : ∑' (jk : ℕ × ℕ), ∫⁻ r in Ioc (0:ℝ) 1,
      ‖r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)‖ₑ ≠ ⊤ := by
    simp_rw [lintegral_enorm_eq_ofReal' β hβ',
      show ∀ jk : ℕ × ℕ,
        ∫ r in Ioc (0:ℝ) 1, r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r) =
        R_beta β (2 * jk.1 + 2 * jk.2 + 1) from fun jk => by
        rw [show (∫ r in Ioc (0:ℝ) 1,
            r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) =
          (∫ r in (0:ℝ)..1,
            r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) from
          (integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm]
        unfold R_beta; congr 1; ext r; ring]
    exact (summable_beta_integrals β hβ).tsum_ofReal_ne_top
  rw [integral_tsum h_meas h_ne_top]

  congr 1; ext jk
  rw [show (∫ r in Ioc (0:ℝ) 1,
      r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) =
    (∫ r in (0:ℝ)..1,
      r ^ (2 * jk.1 + 2 * jk.2) * ((1 - r) ^ β * r)) from
    (integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm]
  unfold R_beta; congr 1; ext r; ring






end GradientIntegrability

namespace SumIndependentGaussians

open Filter Finset

/-- If $X$ has law $\mathcal{N}(0, v)$ under $P$, then $\operatorname{Var}[X; P] = v$. -/
lemma variance_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    Var[X; P] = ↑v := by
  have h1 : Var[X; P] = Var[id ∘ X; P] := by simp
  rw [h1, ← variance_map (by rw [hlaw.map_eq]; exact aemeasurable_id) hlaw.aemeasurable,
      hlaw.map_eq]
  exact variance_id_gaussianReal

/-- If $X$ has law $\mathcal{N}(0, v)$ under $P$, then $\mathbb{E}[X] = \int_\Omega X \,\mathrm{d}P = 0$. -/
lemma integral_eq_zero_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ∂P = 0 := by
  have h1 : ∫ ω, X ω ∂P = ∫ x, x ∂(P.map X) := by
    symm; exact integral_map hlaw.aemeasurable aestronglyMeasurable_id
  rw [h1, hlaw.map_eq, integral_id_gaussianReal]

/-- If $X$ has law $\mathcal{N}(0, v)$ under $P$, then $X$ has a Gaussian law under $P$. -/
lemma hasGaussianLaw_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    HasGaussianLaw X P :=
  hlaw.hasGaussianLaw

/-- A real-valued Gaussian random variable with law $\mathcal{N}(0, v)$ lies in $L^2(P)$. -/
lemma memLp_two_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp X 2 P :=
  hlaw.hasGaussianLaw.memLp_two

/-- The partial sum $S_n = \sum_{k < n} X_k$ of Gaussian random variables lies in $L^2(P)$. -/
lemma memLp_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P :=
  memLp_finset_sum _ (fun k _ => memLp_two_of_hasLaw (hgauss k))


/-- The partial sum $S_n = \sum_{k < n} X_k$ viewed as an element of $L^2(P)$. -/
noncomputable def partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_partialSum hgauss n).toLp _


set_option maxHeartbeats 800000 in
/-- For a centered $L^2$ random variable $f$ on a probability space,
$\|f\|_{L^2}^2 = \operatorname{Var}(f)$. -/
lemma eLpNorm_sq_eq_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) (hm : ∫ ω, f ω ∂P = 0) :
    (eLpNorm f 2 P).toReal ^ 2 = variance f P := by
  rw [variance_eq_sub hf, hm]
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num


set_option maxHeartbeats 800000 in
/-- For independent Gaussian random variables $X_k \sim \mathcal{N}(0, v_k)$,
the variance of the block sum $\sum_{k \in [n, m)} X_k$ equals $\sum_{k \in [n, m)} v_k$. -/
lemma variance_icoSum_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n m : ℕ) :
    variance (fun ω => ∑ k ∈ Ico n m, X k ω) P = ∑ k ∈ Ico n m, (v k : ℝ) := by
  have hf : (fun ω => ∑ k ∈ Ico n m, X k ω) = ∑ k ∈ Ico n m, X k := by
    ext ω; simp [Finset.sum_apply]
  rw [hf, IndepFun.variance_sum
    (fun k _ => memLp_two_of_hasLaw (hgauss k))
    (fun i _ j _ hij => hindep.indepFun hij)]
  exact Finset.sum_congr rfl (fun k _ => variance_of_hasLaw (hgauss k))


set_option maxHeartbeats 1600000 in
/-- For a summable nonnegative sequence $v$, the block sum is bounded by the tail of the series:
$\sum_{k \in [n, m)} v_k \leq \sum_{k \geq 0} v_{k + n}$. -/
lemma sum_Ico_le_tsum_tail (v : ℕ → ℝ≥0) (hsum : Summable v) (n m : ℕ) :
    ∑ k ∈ Ico n m, (v k : ℝ) ≤ ∑' k, (v (k + n) : ℝ) := by
  have hsv : Summable (fun k => v (k + n)) := NNReal.summable_nat_add v hsum n
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [show ∀ k, v (n + k) = v (k + n) from fun k => by rw [add_comm]]
  have : ∀ i ∉ Finset.range (m - n), (0 : ℝ) ≤ (v (i + n) : ℝ) := fun i _ => NNReal.coe_nonneg _
  exact sum_le_hasSum _ this (NNReal.summable_coe.mpr hsv).hasSum


set_option maxHeartbeats 2400000 in
/-- The $L^2$-distance between partial sums $S_n$ and $S_m$ (with $n \leq m$) is bounded by
$\sqrt{\sum_{k \geq 0} v_{k + n}}$, the square root of the tail of the variance series. -/
lemma dist_partialSumLp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) {n m : ℕ} (hnm : n ≤ m) :
    dist (partialSumLp hgauss n) (partialSumLp hgauss m) ≤
      Real.sqrt (∑' k, (v (k + n) : ℝ)) := by
  rw [dist_comm, Lp.dist_def]
  set f := fun ω => ∑ k ∈ Ico n m, X k ω
  have hae : (↑↑(partialSumLp hgauss m) - ↑↑(partialSumLp hgauss n) : Ω → ℝ) =ᵐ[P] f := by
    simp only [partialSumLp]
    filter_upwards [(memLp_partialSum hgauss n).coeFn_toLp,
      (memLp_partialSum hgauss m).coeFn_toLp] with ω hωn hωm
    simp only [Pi.sub_apply, hωm, hωn, f, ← sum_sdiff_eq_sub (range_mono hnm)]
    congr 1
    ext k; simp only [Finset.mem_sdiff, mem_range, mem_Ico, not_lt]; omega
  rw [eLpNorm_congr_ae hae]
  have hf_lp : MemLp f 2 P :=
    memLp_finset_sum _ (fun k _ => memLp_two_of_hasLaw (hgauss k))
  have hf_mean : ∫ ω, f ω ∂P = 0 := by
    show ∫ ω, ∑ k ∈ Ico n m, X k ω ∂P = 0
    rw [integral_finset_sum _ (fun k _ =>
      (memLp_two_of_hasLaw (hgauss k)).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun k _ => integral_eq_zero_of_hasLaw (hgauss k))
  have h_sq_le : (eLpNorm f 2 P).toReal ^ 2 ≤ ∑' k, (v (k + n) : ℝ) := by
    rw [eLpNorm_sq_eq_variance hf_lp hf_mean, variance_icoSum_eq hindep hgauss n m]
    exact sum_Ico_le_tsum_tail v hsum n m
  calc (eLpNorm f 2 P).toReal
      = Real.sqrt ((eLpNorm f 2 P).toReal ^ 2) := (Real.sqrt_sq ENNReal.toReal_nonneg).symm
    _ ≤ Real.sqrt (∑' k, (v (k + n) : ℝ)) := Real.sqrt_le_sqrt h_sq_le

/-- If $\sum_k v_k < \infty$, then the partial sums $S_n = \sum_{k < n} X_k$ form
a Cauchy sequence in $L^2(P)$. -/
theorem cauchySeq_partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) :
    CauchySeq (partialSumLp hgauss) := by
  apply cauchySeq_of_le_tendsto_0' (fun N => Real.sqrt (∑' k, (v (k + N) : ℝ)))
  · intro n m hnm
    exact dist_partialSumLp_le hindep hgauss hsum hnm
  · rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
    exact (Real.continuous_sqrt.tendsto 0).comp (tendsto_sum_nat_add (fun k => (v k : ℝ)))

/-- Existence of the $L^2$-limit: completeness of $L^2(P)$ gives an $S \in L^2(P)$ such that
the partial sums $S_n = \sum_{k < n} X_k$ converge to $S$ in $L^2(P)$. -/
theorem exists_L2_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) :
    ∃ S : Ω → ℝ, MemLp S 2 P ∧
      Tendsto (fun n => eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P)
        atTop (nhds 0) := by

  have hcauchy := cauchySeq_partialSumLp X v hindep hgauss hsum

  have hfact : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy

  set S := (L : Ω → ℝ)
  have hS_mem : MemLp S 2 P := Lp.memLp L
  refine ⟨S, hS_mem, ?_⟩

  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hL
  refine hL.congr (fun n => ?_)


  apply eLpNorm_congr_ae
  have h1 := (memLp_partialSum hgauss n).coeFn_toLp


  filter_upwards [h1] with ω hω
  simp only [partialSumLp, Pi.sub_apply]
  rw [hω]


/-- The partial sum of independent Gaussian random variables has a Gaussian law:
if each $X_k \sim \mathcal{N}(0, v_k)$ and the $X_k$ are independent, then
$\sum_{k < n} X_k$ has a Gaussian law on $\mathbb{R}$. -/
theorem hasGaussianLaw_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (n : ℕ) :
    HasGaussianLaw (fun ω => ∑ k ∈ range n, X k ω) P := by

  have hindep_n : iIndepFun ((range n).restrict X) P :=
    iIndepFun_iff_finset.mp hindep (range n)
  have hgauss_n : ∀ i : ↥(range n), HasGaussianLaw (((range n).restrict X) i) P :=
    fun i => hasGaussianLaw_of_hasLaw (hgauss i.val)
  have hG := iIndepFun.hasGaussianLaw_fun_sum hgauss_n hindep_n

  have heq : (fun ω => ∑ i, ((range n).restrict X) i ω) =
      (fun ω => ∑ k ∈ range n, X k ω) := by
    ext ω
    simp only [Finset.restrict]
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (range n) (fun k => X k ω)
  rwa [heq] at hG


/-- Identification of the law of the partial sum: if $X_k \sim \mathcal{N}(0, v_k)$ are
independent, then $\sum_{k < n} X_k \sim \mathcal{N}\bigl(0, \sum_{k < n} v_k\bigr)$. -/
lemma hasLaw_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (n : ℕ) :
    HasLaw (fun ω => ∑ k ∈ range n, X k ω) (gaussianReal 0 (∑ k ∈ range n, v k)) P := by
  have hG := hasGaussianLaw_partialSum X v hindep hgauss n
  have hIsG : IsGaussian (P.map (fun ω => ∑ k ∈ range n, X k ω)) := hG.isGaussian_map
  have hmean : ∫ ω, (∑ k ∈ range n, X k ω) ∂P = 0 := by
    rw [integral_finset_sum _ (fun k _ => (memLp_two_of_hasLaw (hgauss k)).integrable one_le_two)]
    simp only [integral_eq_zero_of_hasLaw (hgauss _), Finset.sum_const_zero]

  constructor
  · exact hG.aemeasurable
  · have h1 := hIsG.eq_gaussianReal (P.map (fun ω => ∑ k ∈ range n, X k ω))
    rw [h1]
    congr 1
    ·
      rw [integral_map hG.aemeasurable aestronglyMeasurable_id]
      simp only [id]
      exact hmean
    ·
      rw [variance_map aemeasurable_id hG.aemeasurable, Function.id_comp]
      rw [show (fun ω => ∑ k ∈ range n, X k ω) = (∑ k ∈ range n, X k) from
        funext (fun ω => (Finset.sum_apply ω (range n) X).symm)]
      rw [IndepFun.variance_sum
        (fun k _ => memLp_two_of_hasLaw (hgauss k))
        (fun i hi j hj hij => hindep.indepFun hij)]
      simp only [variance_of_hasLaw (hgauss _)]
      simp only [← NNReal.coe_sum]
      exact Real.toNNReal_coe

/-- The $L^2$-limit $S$ inherits the Gaussian law: if $S_n = \sum_{k < n} X_k \to S$ in
$L^2(P)$, then $S \sim \mathcal{N}\bigl(0, \sum_k v_k\bigr)$. The proof uses convergence
in measure $\Rightarrow$ convergence in distribution together with continuity of the
characteristic function $\mathcal{N}(0, \sum_{k<n} v_k) \to \mathcal{N}(0, \sum_k v_k)$. -/
theorem hasLaw_of_L2_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v)
    (S : Ω → ℝ) (hS_mem : MemLp S 2 P)
    (hS_lim : Tendsto (fun n => eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P)
        atTop (nhds 0)) :
    HasLaw S (gaussianReal 0 (∑' k, v k)) P := by

  have hSn_aesm : ∀ n, AEStronglyMeasurable (fun ω => ∑ k ∈ range n, X k ω) P :=
    fun n => (memLp_partialSum hgauss n).aestronglyMeasurable
  have hS_aesm : AEStronglyMeasurable S P := hS_mem.aestronglyMeasurable
  have hS_lim' : Tendsto (fun n => eLpNorm ((fun ω => ∑ k ∈ range n, X k ω) - S) 2 P)
      atTop (nhds 0) := hS_lim
  have hTIM : TendstoInMeasure P (fun n => fun ω => ∑ k ∈ range n, X k ω) atTop S :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hSn_aesm hS_aesm hS_lim'

  have hTID := hTIM.tendstoInDistribution (fun n => (hSn_aesm n).aemeasurable)
  have hconv1 := hTID.tendsto

  have hlaw_n := hasLaw_partialSum X v hindep hgauss

  set σsq := ∑' k, v k
  have hσ_prob : IsProbabilityMeasure (gaussianReal (0 : ℝ) σsq) :=
    (isGaussian_gaussianReal 0 σsq).toIsProbabilityMeasure
  set μ_target : ProbabilityMeasure ℝ := ⟨gaussianReal 0 σsq, hσ_prob⟩
  have hGn_prob : ∀ n, IsProbabilityMeasure (gaussianReal (0 : ℝ) (∑ k ∈ range n, v k)) :=
    fun n => (isGaussian_gaussianReal 0 _).toIsProbabilityMeasure
  set μ_seq : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨gaussianReal 0 (∑ k ∈ range n, v k), hGn_prob n⟩
  have hconv_gauss : Tendsto μ_seq atTop (nhds μ_target) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    simp only [μ_seq, μ_target, ProbabilityMeasure.coe_mk]
    simp only [charFun_gaussianReal]
    apply Filter.Tendsto.cexp
    apply Filter.Tendsto.sub
    · exact tendsto_const_nhds
    · apply Filter.Tendsto.div_const
      apply Filter.Tendsto.mul_const
      apply (Complex.continuous_ofReal.tendsto _).comp
      apply (continuous_subtype_val.tendsto _).comp
      exact hsum.hasSum.tendsto_sum_nat

  have hseq_eq : ∀ n, (⟨P.map (fun ω => ∑ k ∈ range n, X k ω),
      Measure.isProbabilityMeasure_map (hSn_aesm n).aemeasurable⟩ : ProbabilityMeasure ℝ) =
      μ_seq n := by
    intro n
    ext : 1
    simp only [μ_seq]
    exact (hlaw_n n).map_eq
  have hS_prob := Measure.isProbabilityMeasure_map hS_aesm.aemeasurable
  set limit_pm : ProbabilityMeasure ℝ := ⟨P.map S, hS_prob⟩
  have hconv1' : Tendsto μ_seq atTop (nhds limit_pm) := by
    refine (hconv1.congr fun n => ?_)
    exact hseq_eq n
  have heq : limit_pm = μ_target := tendsto_nhds_unique hconv1' hconv_gauss
  have hmap_eq : P.map S = gaussianReal 0 σsq := by
    have h := congr_arg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) heq
    simp only [limit_pm, μ_target, ProbabilityMeasure.coe_mk] at h
    exact h
  exact ⟨hS_mem.aestronglyMeasurable.aemeasurable, hmap_eq⟩

/-- **Proposition 1 (Brownian Motion).** Let $(X_k)_{k \geq 0}$ be independent real-valued
Gaussian random variables on a probability space $(\Omega, P)$ with $X_k \sim \mathcal{N}(0, v_k)$
and $\sigma^2 := \sum_k v_k < \infty$. Then there exists a random variable $S$ such that the
partial sums $\sum_{k < n} X_k$ converge to $S$ in $L^2(P)$ and $S \sim \mathcal{N}(0, \sigma^2)$. -/
theorem sum_independent_gaussians
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0)
    (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hsum : Summable v) :
    ∃ S : Ω → ℝ,
      Tendsto (fun n => eLpNorm (fun ω => S ω - ∑ k ∈ range n, X k ω) 2 P) atTop (nhds 0) ∧
      HasLaw S (gaussianReal 0 (∑' k, v k)) P := by
  obtain ⟨S, hS_mem, hS_lim⟩ := exists_L2_limit X v hindep hgauss hsum
  refine ⟨S, ?_, hasLaw_of_L2_limit X v hindep hgauss hsum S hS_mem hS_lim⟩

  have hsymm : ∀ n, eLpNorm (fun ω => S ω - ∑ k ∈ range n, X k ω) 2 P =
      eLpNorm (fun ω => (∑ k ∈ range n, X k ω) - S ω) 2 P := fun n => by
    simp_rw [show ∀ ω, S ω - ∑ k ∈ range n, X k ω =
      -(((∑ k ∈ range n, X k ω) - S ω)) from fun ω => by ring]
    exact eLpNorm_neg ..
  simp_rw [hsymm]
  exact hS_lim

end SumIndependentGaussians

namespace BrownianFDD

open Finset Filter
open scoped Topology

/-- Predicate characterizing a Rademacher-type random variable $R : Ω → ℝ$ on
$(Ω, P)$: $R$ is measurable, has mean zero $\mathbb{E}[R] = \int R\,\mathrm{d}P = 0$,
and unit variance $\mathbb{E}[R^2] = \int R^2\,\mathrm{d}P = 1$. The canonical
example is the symmetric $\pm 1$ Bernoulli (Rademacher) variable. -/
structure IsRademacher {Ω : Type*} [MeasurableSpace Ω] (R : Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : Measurable R
  mean_zero : ∫ ω, R ω ∂P = 0
  variance_one : ∫ ω, (R ω) ^ 2 ∂P = 1

/-- The $k$-th partial sum (random walk) of a sequence $(R_i)_{i \in ℕ}$ of random
variables: $S_k(ω) = \sum_{i < k} R_i(ω)$. -/
noncomputable def randomWalk {Ω : Type*} (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range k, R i ω

/-- The Donsker-scaled increment of the random walk between indices $k_{\text{prev}}$
and $k_{\text{next}}$:
$$\frac{S_{k_{\text{next}}}(ω) - S_{k_{\text{prev}}}(ω)}{\sqrt{n}}.$$
This is the basic building block whose distribution converges to a Gaussian as
$n \to \infty$. -/
noncomputable def scaledIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (k_prev k_next : ℕ) (ω : Ω) : ℝ :=
  (randomWalk R k_next ω - randomWalk R k_prev ω) / Real.sqrt n

/-- The discrete grid index associated with a continuous time $t_j$ at scale $n$:
$\lfloor n \cdot t_j \rfloor$. Converts a continuous time partition into the nearest
discrete step on the random walk. -/
noncomputable def gridIndex (n : ℕ) (t : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℕ :=
  ⌊(n : ℝ) * t j⌋₊

/-- The vector of variances $\sigma_j^2 = t_{j+1} - t_j$ for $j = 0, \dots, m-1$
associated with a strictly increasing time partition $t : \mathrm{Fin}(m+1) \to ℝ$.
These are the variances of the limiting independent Gaussian increments in Brownian
finite-dimensional distribution convergence. -/
noncomputable def varianceVector {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) :
    Fin m → NNReal :=
  fun j => ⟨t j.succ - t j.castSucc,
    le_of_lt (sub_pos.mpr (ht Fin.castSucc_lt_succ))⟩

/-- Monotonicity of the grid index: for a strictly monotone time partition $t$ and
fixed scale $n$, the discrete grid indices $j \mapsto \lfloor n \cdot t_j \rfloor$
form a monotone sequence. -/
lemma gridIndex_mono {m : ℕ} (n : ℕ) {t : Fin (m + 1) → ℝ}
    (ht : StrictMono t) :
    Monotone (fun j => gridIndex n t j) := by
  intro a b hab
  simp only [gridIndex]
  apply Nat.floor_le_floor
  exact mul_le_mul_of_nonneg_left (ht.monotone hab) (Nat.cast_nonneg n)

/-- The block size $\lfloor n \cdot t_{j+1} \rfloor - \lfloor n \cdot t_j \rfloor$
tends to infinity as $n \to \infty$, since $t_{j+1} - t_j > 0$. This is what allows
the central limit theorem to apply on each block. -/
lemma tendsto_gridIndex_sub_atTop {m : ℕ}
    {t : Fin (m + 1) → ℝ} (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    (j : Fin m) :
    Filter.Tendsto (fun n : ℕ => gridIndex n t j.succ - gridIndex n t j.castSucc)
      Filter.atTop Filter.atTop := by
  have hlt : t j.castSucc < t j.succ := ht Fin.castSucc_lt_succ
  have hle_cs : 0 ≤ t j.castSucc :=
    le_trans ht0 (ht.monotone (Fin.zero_le j.castSucc))
  rw [Filter.tendsto_atTop_atTop]
  intro C
  have hd : 0 < t j.succ - t j.castSucc := sub_pos.mpr hlt
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1 : ℝ) / (t j.succ - t j.castSucc))
  use N
  intro n hn
  simp only [gridIndex]
  have hle : ⌊(n : ℝ) * t j.castSucc⌋₊ ≤ ⌊(n : ℝ) * t j.succ⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left (le_of_lt hlt) (Nat.cast_nonneg n))
  suffices h : (C : ℝ) ≤ ↑(⌊(n : ℝ) * t j.succ⌋₊ - ⌊(n : ℝ) * t j.castSucc⌋₊) by
    exact_mod_cast h
  rw [Nat.cast_sub hle]
  have h1 : (n : ℝ) * t j.succ - 1 < ↑⌊(n : ℝ) * t j.succ⌋₊ := by
    have := Nat.lt_floor_add_one ((n : ℝ) * t j.succ)
    push_cast at this ⊢; linarith
  have h2 : (↑⌊(n : ℝ) * t j.castSucc⌋₊ : ℝ) ≤ (n : ℝ) * t j.castSucc :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hle_cs)
  have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn_large : (C + 1 : ℝ) / (t j.succ - t j.castSucc) < (n : ℝ) :=
    lt_of_lt_of_le hN hN'
  have key : (C + 1 : ℝ) < (n : ℝ) * (t j.succ - t j.castSucc) := by
    rwa [div_lt_iff₀ hd] at hn_large
  linarith

/-- The difference of partial sums equals the sum over the half-open interval:
$S_b(ω) - S_a(ω) = \sum_{i \in [a, b)} R_i(ω)$ for $a \le b$. -/
lemma randomWalk_diff_eq_sum_Ico {Ω : Type*} (R : ℕ → Ω → ℝ)
    {a b : ℕ} (hab : a ≤ b) (ω : Ω) :
    randomWalk R b ω - randomWalk R a ω = ∑ i ∈ Finset.Ico a b, R i ω := by
  simp only [randomWalk]
  have := Finset.sum_Ico_eq_sub (f := fun i => R i ω) hab
  linarith

/-- Rewrite the scaled increment as a normalized sum over a block:
$\dfrac{S_{k_{\text{next}}} - S_{k_{\text{prev}}}}{\sqrt{n}} =
\dfrac{1}{\sqrt{n}} \sum_{i \in [k_{\text{prev}}, k_{\text{next}})} R_i(ω)$. -/
lemma scaledIncrement_eq_sum_div {Ω : Type*} (R : ℕ → Ω → ℝ)
    (n : ℕ) {k_prev k_next : ℕ} (h : k_prev ≤ k_next) (ω : Ω) :
    scaledIncrement R n k_prev k_next ω =
      (∑ i ∈ Finset.Ico k_prev k_next, R i ω) / Real.sqrt n := by
  simp only [scaledIncrement]
  rw [randomWalk_diff_eq_sum_Ico R h ω]


/-- The ratio of block size to total scale converges to the time difference:
$$\frac{\lfloor n \cdot t_{j+1} \rfloor - \lfloor n \cdot t_j \rfloor}{n}
\;\longrightarrow\; t_{j+1} - t_j \quad (n \to \infty).$$
This is the key asymptotic that lets the rescaled increments carry the correct
Brownian variance in the limit. -/
theorem gridIndex_block_ratio_tendsto
    {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    (j : Fin m) :
    Tendsto (fun n : ℕ => ((gridIndex n t j.succ - gridIndex n t j.castSucc : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (t j.succ - t j.castSucc)) := by
  have hmono : ∀ n, gridIndex n t j.castSucc ≤ gridIndex n t j.succ := by
    intro n
    exact gridIndex_mono n ht (Fin.castSucc_lt_succ.le)

  have heq : (fun n : ℕ => ((gridIndex n t j.succ - gridIndex n t j.castSucc : ℕ) : ℝ) / (n : ℝ)) =
      (fun n : ℕ => (⌊(n : ℝ) * t j.succ⌋₊ : ℝ) / (n : ℝ) -
        (⌊(n : ℝ) * t j.castSucc⌋₊ : ℝ) / (n : ℝ)) := by
    ext n
    rw [Nat.cast_sub (hmono n)]
    simp only [gridIndex]
    ring
  rw [heq]

  have ht_succ : 0 ≤ t j.succ := le_trans ht0 (ht.monotone (Fin.zero_le _))
  have ht_cs : 0 ≤ t j.castSucc := le_trans ht0 (ht.monotone (Fin.zero_le _))
  have h1 : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t j.succ⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds (t j.succ)) := by
    have := (tendsto_nat_floor_mul_div_atTop ht_succ).comp tendsto_natCast_atTop_atTop
    simp only [mul_comm (t j.succ)] at this
    exact this
  have h2 : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t j.castSucc⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds (t j.castSucc)) := by
    have := (tendsto_nat_floor_mul_div_atTop ht_cs).comp tendsto_natCast_atTop_atTop
    simp only [mul_comm (t j.castSucc)] at this
    exact this
  exact h1.sub h2





/-- Independence of $\sigma$-algebras indexed by disjoint families. Given an
$ι$-indexed independent family of $\sigma$-algebras $(m_i)$ and a $κ$-indexed
family of pairwise disjoint subsets $(S_j) \subseteq ι$, the bundled $\sigma$-algebras
$\bigvee_{i \in S_j} m_i$ are independent across $j$. -/
lemma iIndep_biSup_of_disjoint
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} {κ : Type*} [DecidableEq κ]
    {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ _mΩ)
    (h_indep : iIndep m μ)
    {S : κ → Set ι} (hS : ∀ j₁ j₂ : κ, j₁ ≠ j₂ → Disjoint (S j₁) (S j₂)) :
    iIndep (fun j => ⨆ i ∈ S j, m i) μ := by
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction with
  | empty => simp [h_indep.isProbabilityMeasure.measure_univ]
  | insert j s hjs ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.prod_insert hjs]
    have ih' : μ (⋂ j' ∈ s, f j') = ∏ j' ∈ s, μ (f j') := ih hf.2
    have heq : (⋂ i ∈ insert j s, f i) = f j ∩ ⋂ i ∈ s, f i := by
      ext x; simp
    rw [heq, ← ih']
    have hdisj : Disjoint (S j) (⋃ j' ∈ (s : Set κ), S j') := by
      simp only [Set.disjoint_iUnion_right]
      intro j' hj'
      exact hS j j' (fun h => hjs (h ▸ hj'))
    have hindep_blocks : Indep (⨆ i ∈ S j, m i) (⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i) μ :=
      indep_iSup_of_disjoint hm h_indep hdisj
    have hfj : @MeasurableSet Ω (⨆ i ∈ S j, m i) (f j) := hf.1
    have hle : (⨆ j' ∈ (s : Set κ), ⨆ i ∈ S j', m i) ≤
        ⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i :=
      iSup₂_le fun j' hj' => iSup₂_le fun i hi =>
        le_iSup₂_of_le i (Set.mem_biUnion hj' hi) le_rfl
    have hfs : @MeasurableSet Ω (⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i)
        (⋂ j' ∈ s, f j') := by
      apply hle
      apply MeasurableSet.biInter (Finset.countable_toSet s)
      intro j' hj'
      exact (le_iSup₂_of_le j' hj' le_rfl : ⨆ i ∈ S j', m i ≤ _) _ (hf.2 j' hj')
    have h_prod := hindep_blocks (f j) (⋂ j' ∈ s, f j') hfj hfs
    simp only [Kernel.const_apply, ae_dirac_eq] at h_prod
    exact h_prod


/-- The collection of scaled increments
$\bigl(\mathrm{scaledIncrement}\,R\,n\,\lfloor n t_j \rfloor\,\lfloor n t_{j+1} \rfloor\bigr)_{j \in \mathrm{Fin}\,m}$
is jointly independent, because each increment is measurable with respect to the
$\sigma$-algebra generated by $(R_i)$ on a disjoint block of indices. -/
theorem increments_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : ℕ → Ω → ℝ}
    (hindep : iIndepFun (m := fun _ => inferInstance) R P)
    (hR_meas : ∀ i, Measurable (R i))
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (n : ℕ) :
    iIndepFun (m := fun (_ : Fin m) => inferInstance)
      (fun (j : Fin m) (ω : Ω) =>
        scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) P := by

  let σR : ℕ → MeasurableSpace Ω := fun i => (inferInstance : MeasurableSpace ℝ).comap (R i)

  let block : Fin m → Set ℕ := fun j =>
    ((Finset.Ico (gridIndex n t j.castSucc) (gridIndex n t j.succ) : Finset ℕ) : Set ℕ)

  have hblock_disj : ∀ j₁ j₂ : Fin m, j₁ ≠ j₂ → Disjoint (block j₁) (block j₂) := by
    intro j₁ j₂ hne
    simp only [block, Finset.coe_Ico]
    have hmono := gridIndex_mono n ht
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hne with h | h
    ·
      have hle := hmono (Fin.succ_le_castSucc_iff.mpr h)
      exact absurd (lt_of_lt_of_le hx1.2 (le_trans hle hx2.1)) (not_lt.mpr le_rfl)
    ·
      have hle := hmono (Fin.succ_le_castSucc_iff.mpr h)
      exact absurd (lt_of_lt_of_le hx2.2 (le_trans hle hx1.1)) (not_lt.mpr le_rfl)

  have hσR_le : ∀ i, σR i ≤ ‹MeasurableSpace Ω› := fun i => (hR_meas i).comap_le

  have h_block_indep : iIndep (fun j => ⨆ i ∈ block j, σR i) P :=
    iIndep_biSup_of_disjoint hσR_le hindep hblock_disj

  have hincr_le : ∀ j : Fin m,
      (inferInstance : MeasurableSpace ℝ).comap
        (fun ω => scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) ≤
      ⨆ i ∈ block j, σR i := by
    intro j
    have hle_block := gridIndex_mono n ht (@Fin.castSucc_lt_succ m j).le
    have heq : (fun ω => scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) =
               (fun ω => (∑ i ∈ Finset.Ico (gridIndex n t j.castSucc) (gridIndex n t j.succ),
                 R i ω) / Real.sqrt n) := by
      ext ω; exact scaledIncrement_eq_sum_div R n hle_block ω
    rw [heq]

    exact (Measurable.div_const (Finset.measurable_sum _ fun i hi =>
      Measurable.mono (comap_measurable (R i))
        (le_iSup₂_of_le i (Finset.mem_coe.mpr hi) le_rfl) le_rfl) _).comap_le

  exact iIndep_of_iIndep_of_le h_block_indep hincr_le


/-- **Joint convergence from marginal convergence for independent coordinates.** If for
each $j$ the marginal sequence $X_n(j)$ converges in distribution to $Z(j)$, and if
the coordinates $(X_n(j))_j$ are jointly independent for every $n$ (and the limit
coordinates $(Z(j))_j$ are independent), then the full vector $X_n(\cdot)$ converges
in distribution to $Z(\cdot)$. -/
theorem indep_marginal_tendstoInDistribution_product
    {Ω Ω' : Type*} {m : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Fin m → Ω → ℝ)
    (Z : Fin m → Ω' → ℝ)
    (hmarg : ∀ j : Fin m, TendstoInDistribution
      (fun n ω => X n j ω) atTop (Z j) (fun _ => P) P')
    (hindep : ∀ n, iIndepFun (m := fun (_ : Fin m) => inferInstance)
      (fun j ω => X n j ω) P)
    (hindep_limit : iIndepFun (m := fun (_ : Fin m) => inferInstance) Z P') :
    TendstoInDistribution
      (fun n ω => (fun j => X n j ω : Fin m → ℝ)) atTop
      (fun ω => (fun j => Z j ω : Fin m → ℝ)) (fun _ => P) P' where
  forall_aemeasurable n :=
    aemeasurable_pi_iff.mpr (fun j => (hmarg j).forall_aemeasurable n)
  aemeasurable_limit :=
    aemeasurable_pi_iff.mpr (fun j => (hmarg j).aemeasurable_limit)
  tendsto := by

    have hXaem : ∀ n j, AEMeasurable (fun ω => X n j ω) P :=
      fun n j => (hmarg j).forall_aemeasurable n
    have hZaem : ∀ j, AEMeasurable (Z j) P' :=
      fun j => (hmarg j).aemeasurable_limit

    have hmap_n : ∀ n, P.map (fun ω j => X n j ω) =
        Measure.pi (fun j => P.map (fun ω => X n j ω)) :=
      fun n => (iIndepFun_iff_map_fun_eq_pi_map (fun j => hXaem n j)).mp (hindep n)
    have hmap_lim : P'.map (fun ω j => Z j ω) =
        Measure.pi (fun j => P'.map (Z j)) :=
      (iIndepFun_iff_map_fun_eq_pi_map hZaem).mp hindep_limit

    have hpm_n : ∀ n j, IsProbabilityMeasure (P.map (fun ω => X n j ω)) :=
      fun n j => Measure.isProbabilityMeasure_map (hXaem n j)
    have hpm_lim : ∀ j, IsProbabilityMeasure (P'.map (Z j)) :=
      fun j => Measure.isProbabilityMeasure_map (hZaem j)

    let μ_n (n : ℕ) (j : Fin m) : ProbabilityMeasure ℝ :=
      ⟨P.map (fun ω => X n j ω), hpm_n n j⟩
    let μ_lim (j : Fin m) : ProbabilityMeasure ℝ :=
      ⟨P'.map (Z j), hpm_lim j⟩

    have hmarg_tendsto : ∀ j, Tendsto (fun n => μ_n n j) atTop (𝓝 (μ_lim j)) :=
      fun j => (hmarg j).tendsto

    have hpi_tendsto : Tendsto (fun n => ProbabilityMeasure.pi (μ_n n)) atTop
        (𝓝 (ProbabilityMeasure.pi μ_lim)) := by
      apply (ProbabilityMeasure.continuous_pi).continuousAt.tendsto.comp
      exact tendsto_pi_nhds.mpr hmarg_tendsto

    convert hpi_tendsto using 1
    · funext n
      exact Subtype.ext (hmap_n n)
    · congr 1
      exact Subtype.ext hmap_lim


/-- The Donsker-scale piecewise linear interpolation $f_n(t)$ of the random walk:
between integer scaled times $k/n$ and $(k+1)/n$, the function interpolates linearly
between $S_k/\sqrt{n}$ and $S_{k+1}/\sqrt{n}$. Explicitly, with $k = \lfloor n t \rfloor$
and fractional part $\{nt\} = nt - k$,
$$f_n(t)(ω) = \frac{S_k(ω)}{\sqrt{n}} + \{nt\} \cdot \frac{R_k(ω)}{\sqrt{n}}.$$
This is the continuous-time process whose finite-dimensional distributions converge to
those of Brownian motion. -/
noncomputable def piecewiseLinearInterp {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t : ℝ) (ω : Ω) : ℝ :=
  let k := ⌊(n : ℝ) * t⌋₊
  let frac := (n : ℝ) * t - ↑k
  randomWalk R k ω / Real.sqrt n + frac * R k ω / Real.sqrt n

/-- The continuous-time increment of the piecewise linear interpolation between
times $t_{\text{prev}}$ and $t_{\text{next}}$: $f_n(t_{\text{next}}) - f_n(t_{\text{prev}})$. -/
noncomputable def fnIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t_prev t_next : ℝ) (ω : Ω) : ℝ :=
  piecewiseLinearInterp R n t_next ω - piecewiseLinearInterp R n t_prev ω

/-- Decomposition of the continuous-time increment of $f_n$ into the discrete scaled
increment plus a small fractional error:
$$f_n(t_{\text{next}}) - f_n(t_{\text{prev}}) =
\mathrm{scaledIncrement}\,R\,n\,\lfloor n t_{\text{prev}} \rfloor\,\lfloor n t_{\text{next}} \rfloor
+ \frac{1}{\sqrt{n}}\Bigl(\{n t_{\text{next}}\} R_{\lfloor n t_{\text{next}} \rfloor}
- \{n t_{\text{prev}}\} R_{\lfloor n t_{\text{prev}} \rfloor}\Bigr).$$
The error term is uniformly bounded by $2/\sqrt{n}$ (provided $|R_i| \le 1$) and so
vanishes in the limit; this is the basis of the Slutsky argument for
`brownian_fdd_convergence`. -/
lemma fnIncrement_eq_scaledIncrement_add_error {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t_prev t_next : ℝ) (ω : Ω) :
    fnIncrement R n t_prev t_next ω =
      scaledIncrement R n ⌊(n : ℝ) * t_prev⌋₊ ⌊(n : ℝ) * t_next⌋₊ ω +
      (((n : ℝ) * t_next - ↑⌊(n : ℝ) * t_next⌋₊) * R ⌊(n : ℝ) * t_next⌋₊ ω -
       ((n : ℝ) * t_prev - ↑⌊(n : ℝ) * t_prev⌋₊) * R ⌊(n : ℝ) * t_prev⌋₊ ω) / Real.sqrt n := by
  simp only [fnIncrement, piecewiseLinearInterp, scaledIncrement, randomWalk]
  ring




end BrownianFDD

namespace HolderBoundary

open MeasureTheory Set

def SatisfiesGradientBound (F : ℂ → ℂ) (C : ℝ) (α : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 → ‖fderiv ℝ F z‖ ≤ C * (1 - ‖z‖) ^ (-1 + α)

theorem arc_segment_bound
    (F : ℂ → ℂ) (C₀ : ℝ) (α : ℝ) (ρ : ℝ) (t₁ t₂ : ℝ)
    (hC₀ : 0 ≤ C₀) (_hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1)
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C₀ α)
    (ht : |t₁ - t₂| ≤ ρ) :
    ‖F (circleMap 0 (1 - ρ) t₁) - F (circleMap 0 (1 - ρ) t₂)‖ ≤ C₀ * ρ ^ α := by
  have h1mρ_nn : (0 : ℝ) ≤ 1 - ρ := by linarith

  have hcb_sub_b : Metric.closedBall (0 : ℂ) (1 - ρ) ⊆ Metric.ball 0 1 := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith

  have hdiffAt : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 - ρ), DifferentiableAt ℝ F z := by
    intro z hz
    exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hcb_sub_b hz))


  have hgrad_bound : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 - ρ),
      ‖fderiv ℝ F z‖ ≤ C₀ * ρ ^ (-1 + α) := by
    intro z hz
    have hz_in_ball : ‖z‖ < 1 := by
      have := hcb_sub_b hz; simp only [Metric.mem_ball, dist_zero_right] at this; exact this
    have hz_norm_le : ‖z‖ ≤ 1 - ρ := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hz; exact hz
    calc ‖fderiv ℝ F z‖
        ≤ C₀ * (1 - ‖z‖) ^ (-1 + α) := hgrad z hz_in_ball
      _ ≤ C₀ * ρ ^ (-1 + α) := by
          apply mul_le_mul_of_nonneg_left _ hC₀
          exact Real.rpow_le_rpow_of_nonpos hρ_pos (by linarith) (by linarith)

  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    hdiffAt hgrad_bound (convex_closedBall 0 (1 - ρ))
    (circleMap_mem_closedBall 0 h1mρ_nn t₂)
    (circleMap_mem_closedBall 0 h1mρ_nn t₁)

  have hlip_bound : ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖ ≤ ρ := by
    have hlip := (lipschitzWith_circleMap 0 (1 - ρ)).dist_le_mul t₁ t₂
    rw [Complex.dist_eq, Real.dist_eq] at hlip
    calc ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖
        ≤ ↑(Real.nnabs (1 - ρ)) * |t₁ - t₂| := hlip
      _ = |1 - ρ| * |t₁ - t₂| := by simp [Real.coe_nnabs]
      _ = (1 - ρ) * |t₁ - t₂| := by rw [abs_of_nonneg h1mρ_nn]
      _ ≤ 1 * ρ := mul_le_mul (by linarith) ht (abs_nonneg _) (by linarith)
      _ = ρ := one_mul ρ

  calc ‖F (circleMap 0 (1 - ρ) t₁) - F (circleMap 0 (1 - ρ) t₂)‖
      ≤ C₀ * ρ ^ (-1 + α) * ‖circleMap 0 (1 - ρ) t₁ - circleMap 0 (1 - ρ) t₂‖ := hmvt
    _ ≤ C₀ * ρ ^ (-1 + α) * ρ := by
        apply mul_le_mul_of_nonneg_left hlip_bound
        exact mul_nonneg hC₀ (Real.rpow_nonneg (le_of_lt hρ_pos) _)
    _ = C₀ * ρ ^ α := by
        have : ρ ^ (-1 + α) * ρ ^ (1 : ℝ) = ρ ^ (-1 + α + 1) :=
          (Real.rpow_add hρ_pos (-1 + α) 1).symm
        rw [Real.rpow_one] at this
        rw [mul_assoc, this]
        congr 1
        ring

lemma hasDerivAt_circleMap_sub (t s : ℝ) :
    HasDerivAt (fun s => circleMap (0 : ℂ) (1 - s) t) (-circleMap 0 1 t) s := by
  simp_rw [circleMap_zero]
  have hd : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1 : ℝ) s := by
    simpa using (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
  have := (hd.ofReal_comp).mul_const (Complex.exp (↑t * Complex.I))
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul] at this ⊢
  exact this

theorem radial_segment_bound
    (F : ℂ → ℂ) (C₀ : ℝ) (α : ℝ) (t : ℝ)
    (hC₀ : 0 ≤ C₀)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C₀ α)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1) :
    ‖F (circleMap 0 1 t) - F (circleMap 0 (1 - ρ) t)‖ ≤ C₀ / α * ρ ^ α := by

  set g : ℝ → ℂ := fun s => F (circleMap 0 (1 - s) t) with hg_def
  have hg0 : g 0 = F (circleMap 0 1 t) := by simp [g, sub_zero]
  have hgρ : g ρ = F (circleMap 0 (1 - ρ) t) := rfl
  rw [← hg0, ← hgρ]

  have hg_cont : ContinuousOn g (Icc 0 1) := by
    apply hcont.comp (Continuous.continuousOn (by simp_rw [circleMap_zero]; fun_prop))
    intro s hs; simp only [mem_Icc] at hs
    simp only [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith)]
    linarith

  have hg_hasDerivAt : ∀ x : ℝ, 0 < x → x ≤ 1 →
      HasDerivAt g (fderiv ℝ F (circleMap 0 (1 - x) t) (-circleMap 0 1 t)) x := by
    intro x hx hx1
    have h_in : circleMap 0 (1 - x) t ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg (show (0 : ℝ) ≤ 1 - x by linarith)]
      linarith
    exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h_in)).hasFDerivAt.comp_hasDerivAt
      x (hasDerivAt_circleMap_sub t x)

  have hg_deriv_bound : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ‖fderiv ℝ F (circleMap 0 (1 - s) t) (-circleMap 0 1 t)‖ ≤ C₀ * s ^ (-1 + α) := by
    intro s hs hs1
    have h_in : ‖circleMap 0 (1 - s) t‖ < 1 := by
      rw [norm_circleMap_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith)]; linarith
    have h_op := (fderiv ℝ F (circleMap 0 (1 - s) t)).le_opNorm (-circleMap 0 1 t)
    rw [norm_neg, norm_circleMap_zero, abs_one, mul_one] at h_op
    have h_grad := hgrad _ h_in
    rw [norm_circleMap_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 - s by linarith),
      show 1 - (1 - s) = s from by ring] at h_grad
    exact le_trans h_op h_grad

  apply le_of_forall_pos_le_add
  intro δ hδ

  have hg_cwa : ContinuousWithinAt g (Icc 0 1) 0 :=
    hg_cont 0 (left_mem_Icc.mpr (by linarith : (0 : ℝ) ≤ 1))
  rw [Metric.continuousWithinAt_iff] at hg_cwa
  obtain ⟨η, hη_pos, hη⟩ := hg_cwa δ hδ
  set ε := min (η / 2) (ρ / 2) with hε_def
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_le_ρ : ε ≤ ρ := (min_le_right _ _).trans (by linarith)
  have hε_le_1 : ε ≤ 1 := hε_le_ρ.trans hρ_le
  have hg_close : dist (g 0) (g ε) < δ := by
    rw [dist_comm]
    apply hη
    · exact ⟨le_of_lt hε_pos, hε_le_1⟩
    · simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

  have htri : ‖g 0 - g ρ‖ ≤ ‖g 0 - g ε‖ + ‖g ε - g ρ‖ := by
    calc ‖g 0 - g ρ‖ = ‖(g 0 - g ε) + (g ε - g ρ)‖ := by ring_nf
      _ ≤ ‖g 0 - g ε‖ + ‖g ε - g ρ‖ := norm_add_le _ _

  have h1 : ‖g 0 - g ε‖ < δ := by rw [← dist_eq_norm]; exact hg_close

  have h2 : ‖g ε - g ρ‖ ≤ C₀ / α * ρ ^ α := by


    have hg_diff : ∀ x ∈ uIcc ε ρ, DifferentiableAt ℝ g x := by
      intro x hx; simp only [uIcc_of_le hε_le_ρ, mem_Icc] at hx
      exact (hg_hasDerivAt x (by linarith) (by linarith)).differentiableAt

    have hbd : ∀ s ∈ Ioc ε ρ, ‖deriv g s‖ ≤ C₀ * ε ^ (-1 + α) := by
      intro s hs; simp only [mem_Ioc] at hs
      rw [(hg_hasDerivAt s (by linarith) (by linarith)).deriv]
      calc ‖fderiv ℝ F (circleMap 0 (1 - s) t) (-circleMap 0 1 t)‖
          ≤ C₀ * s ^ (-1 + α) := hg_deriv_bound s (by linarith) (by linarith)
        _ ≤ C₀ * ε ^ (-1 + α) := by
            apply mul_le_mul_of_nonneg_left _ hC₀
            exact Real.rpow_le_rpow_of_nonpos hε_pos (le_of_lt hs.1) (by linarith)

    have hint : IntervalIntegrable (deriv g) volume ε ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε_le_ρ]
      exact Measure.integrableOn_of_bounded (M := C₀ * ε ^ (-1 + α))
        measure_Ioc_lt_top.ne (measurable_deriv g).aestronglyMeasurable
        (Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc) hbd)

    have hftc : ∫ s in ε..ρ, deriv g s = g ρ - g ε :=
      intervalIntegral.integral_deriv_eq_sub hg_diff hint

    rw [norm_sub_rev]
    rw [← hftc]

    calc ‖∫ s in ε..ρ, deriv g s‖
        ≤ ∫ s in ε..ρ, ‖deriv g s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hε_le_ρ
      _ ≤ ∫ s in ε..ρ, C₀ * s ^ (-1 + α) := by
          apply intervalIntegral.integral_mono_on hε_le_ρ
          · exact hint.norm
          · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -1 + α)).const_mul C₀
          · intro s hs; simp only [mem_Icc] at hs
            rw [(hg_hasDerivAt s (by linarith) (by linarith)).deriv]
            exact hg_deriv_bound s (by linarith) (by linarith)
      _ = C₀ * (ρ ^ α - ε ^ α) / α := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -1 + α))]
          ring
      _ ≤ C₀ / α * ρ ^ α := by
          have hε_rpow : 0 ≤ ε ^ α := Real.rpow_nonneg (le_of_lt hε_pos) α
          have hρ_rpow : 0 ≤ ρ ^ α := Real.rpow_nonneg (le_of_lt hρ_pos) α
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (le_of_lt hα_pos)
          nlinarith

  linarith


theorem holder_boundary_of_gradient_bound
    (F : ℂ → ℂ) (C : ℝ) (α : ℝ)
    (hC : 0 < C)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : SatisfiesGradientBound F C α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t₁ t₂ : ℝ,
      ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C' * |t₁ - t₂| ^ α := by

  refine ⟨2 * C / α + C, by positivity, fun t₁ t₂ => ?_⟩
  have hC_nn : (0 : ℝ) ≤ C := le_of_lt hC
  by_cases ht_eq : t₁ = t₂
  · simp [ht_eq]; positivity
  · have hρ_pos : 0 < |t₁ - t₂| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    by_cases hρ_le : |t₁ - t₂| ≤ 1
    ·

      have hL1 := radial_segment_bound F C α t₁ hC_nn hα_pos hα_le hcont hdiff hgrad
          |t₁ - t₂| hρ_pos hρ_le
      have hL3 := radial_segment_bound F C α t₂ hC_nn hα_pos hα_le hcont hdiff hgrad
          |t₁ - t₂| hρ_pos hρ_le
      have hL2 := arc_segment_bound F C α |t₁ - t₂| t₁ t₂ hC_nn hα_pos hα_le
          hρ_pos hρ_le hdiff hgrad le_rfl

      have htri : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤
          ‖F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)‖ +
          ‖F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)‖ +
          ‖F (circleMap 0 1 t₂) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)‖ := by
        have heq : F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂) =
          (F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)) +
          (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)) +
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂) - F (circleMap 0 1 t₂)) := by ring
        rw [heq]
        linarith [norm_add_le
          ((F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁)) +
           (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)))
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂) - F (circleMap 0 1 t₂)),
          norm_add_le
          (F (circleMap 0 1 t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₁))
          (F (circleMap 0 (1 - |t₁ - t₂|) t₁) - F (circleMap 0 (1 - |t₁ - t₂|) t₂)),
          norm_sub_rev
          (F (circleMap 0 (1 - |t₁ - t₂|) t₂)) (F (circleMap 0 1 t₂))]

      have hsum : C / α * |t₁ - t₂| ^ α + C * |t₁ - t₂| ^ α + C / α * |t₁ - t₂| ^ α
          = (2 * C / α + C) * |t₁ - t₂| ^ α := by ring
      linarith [hsum]
    ·
      push Not at hρ_le
      have hL1 := radial_segment_bound F C α t₁ hC_nn hα_pos hα_le hcont hdiff hgrad
          1 one_pos le_rfl
      have hL3 := radial_segment_bound F C α t₂ hC_nn hα_pos hα_le hcont hdiff hgrad
          1 one_pos le_rfl

      rw [show (1 : ℝ) - 1 = 0 from sub_self 1] at hL1 hL3
      rw [show ∀ t : ℝ, circleMap (0 : ℂ) 0 t = 0 from
          fun t => by simp [circleMap_zero]] at hL1 hL3
      rw [Real.one_rpow] at hL1 hL3

      have htri : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤
          ‖F (circleMap 0 1 t₁) - F 0‖ + ‖F (circleMap 0 1 t₂) - F 0‖ := by
        have heq : F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂) =
          (F (circleMap 0 1 t₁) - F 0) + (F 0 - F (circleMap 0 1 t₂)) := by ring
        rw [heq]
        linarith [norm_add_le (F (circleMap 0 1 t₁) - F 0) (F 0 - F (circleMap 0 1 t₂)),
                  norm_sub_rev (F 0) (F (circleMap 0 1 t₂))]

      have hρα_ge_1 : 1 ≤ |t₁ - t₂| ^ α :=
        Real.one_le_rpow (le_of_lt hρ_le) (le_of_lt hα_pos)

      have hbound : ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C / α * 1 + C / α * 1 :=
        by linarith
      have heq : C / α * 1 + C / α * 1 = 2 * C / α := by ring
      calc ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖
          ≤ 2 * C / α + C := by linarith [hbound, heq]
        _ = (2 * C / α + C) * 1 := by ring
        _ ≤ (2 * C / α + C) * |t₁ - t₂| ^ α := by
            apply mul_le_mul_of_nonneg_left hρα_ge_1; positivity

end HolderBoundary

namespace WienerConstruction

open GradientIntegrability HolderBoundary BrownianCharacterization
open MeasureTheory Set Filter

noncomputable def wienerC0 : ℝ := Real.sqrt (1 / Real.pi)

noncomputable def wienerC1 : ℝ := Real.sqrt (2 / Real.pi)

noncomputable def wienerProcess {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wienerC0 * a 0 ω * t +
    wienerC1 * ∑' k : ℕ, a (k + 1) ω * Real.sin ((↑(k + 1)) * t) / (↑(k + 1))

theorem wienerProcess_zero {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ω : Ω) :
    wienerProcess a 0 ω = 0 := by
  simp [wienerProcess, wienerC0, Real.sin_zero]

structure IsWienerBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, W 0 ω = 0
  mean_zero : ∀ t, 0 ≤ t → t ≤ Real.pi → ∫ ω, W t ω ∂P = 0
  gaussian_linear_comb : ∀ (n : ℕ) (t : Fin n → ℝ),
    (∀ j, 0 ≤ t j ∧ t j ≤ Real.pi) → ∀ (c : Fin n → ℝ),
    HasGaussianLaw (fun ω => ∑ j, c j * W (t j) ω) P
  covariance_eq_min : ∀ s t, 0 ≤ s → s ≤ Real.pi → 0 ≤ t → t ≤ Real.pi →
    ∫ ω, W s ω * W t ω ∂P = min s t
  ae_continuousOn : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Icc 0 Real.pi)

noncomputable def wienerCoeff (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * ∑ j : Fin n, c j * t j
  else wienerC1 * ∑ j : Fin n, c j * Real.sin (↑k * t j) / ↑k

noncomputable def wienerCoeffVar (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) : ℕ → ℝ≥0 :=
  fun k => ⟨(wienerCoeff n t c k) ^ 2, sq_nonneg _⟩

lemma hasLaw_const_mul_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) (d : ℝ) :
    HasLaw (fun ω => d * X ω) (gaussianReal 0 ⟨d ^ 2, sq_nonneg _⟩) P where
  aemeasurable := hX.aemeasurable.const_mul d
  map_eq := by
    have hXm : AEMeasurable X P := hX.aemeasurable
    change P.map ((fun x => d * x) ∘ X) = _
    rw [← AEMeasurable.map_map_of_aemeasurable
        (measurable_id'.const_mul d).aemeasurable hXm, hX.map_eq]
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) d
    simp only [mul_zero, mul_one] at h
    exact h


set_option maxHeartbeats 800000 in
theorem summable_wienerCoeffVar
    (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ j, 0 ≤ t j ∧ t j ≤ Real.pi) (c : Fin n → ℝ) :
    Summable (wienerCoeffVar n t c) := by
  rw [← NNReal.summable_coe]
  show Summable (fun k => ((wienerCoeffVar n t c k : ℝ≥0) : ℝ))
  simp only [wienerCoeffVar, NNReal.coe_mk]

  rw [← summable_nat_add_iff 1]

  have hpseries : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  set C := wienerC1 ^ 2 * (∑ j : Fin n, |c j|) ^ 2
  have hCbound : Summable (fun k : ℕ => C * ((↑(k + 1) : ℝ) ^ 2)⁻¹) :=
    ((summable_nat_add_iff 1).mpr hpseries).mul_left C
  refine Summable.of_norm_bounded hCbound (fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

  simp only [wienerCoeff, Nat.succ_ne_zero, ite_false, C]
  have hk : (0 : ℝ) < ↑(k + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)

  have hpull : ∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j) / ↑(k + 1) =
      (∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j)) / ↑(k + 1) := by
    rw [Finset.sum_div]
  rw [hpull, mul_div_assoc']

  rw [div_pow, mul_pow]

  rw [div_eq_mul_inv]
  have habs_le : |∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j)| ≤ ∑ j : Fin n, |c j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  have hsinbound : (∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j)) ^ 2 ≤
      (∑ j : Fin n, |c j|) ^ 2 := by
    apply sq_le_sq'
    · linarith [neg_abs_le (∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j))]
    · linarith [le_abs_self (∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j))]

  have hx_nonneg : (0 : ℝ) ≤ ((↑(k + 1) : ℝ) ^ 2)⁻¹ := by positivity
  calc wienerC1 ^ 2 * (∑ j : Fin n, c j * Real.sin (↑(k + 1) * t j)) ^ 2 *
      ((↑(k + 1) : ℝ) ^ 2)⁻¹
      ≤ wienerC1 ^ 2 * (∑ j : Fin n, |c j|) ^ 2 * ((↑(k + 1) : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hx_nonneg
        exact mul_le_mul_of_nonneg_left hsinbound (sq_nonneg _)

noncomputable def wienerBasisCoeff (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * s
  else wienerC1 * Real.sin (↑k * s) / ↑k


theorem wienerProcess_eq_tsum
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω)
    (hsum : Summable (fun k => wienerBasisCoeff s k * a k ω)) :
    wienerProcess a s ω = ∑' k, wienerBasisCoeff s k * a k ω := by
  unfold wienerProcess
  rw [hsum.tsum_eq_zero_add]
  simp only [wienerBasisCoeff, ite_true, Nat.succ_ne_zero, ite_false]
  congr 1
  · ring
  · rw [← tsum_mul_left]
    congr 1; ext k; ring








lemma integral_sq_of_std_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hlaw : HasLaw X (gaussianReal (0 : ℝ) (1 : ℝ≥0)) P) :
    ∫ ω, X ω ^ 2 ∂P = 1 := by
  have hmeas : AEMeasurable X P := hlaw.aemeasurable
  have hmean : (P)[X] = 0 := by
    have : ∫ x, id x ∂(P.map X) = ∫ ω, id (X ω) ∂P :=
      integral_map hlaw.aemeasurable aestronglyMeasurable_id
    simp only [id] at this
    rw [← this, hlaw.map_eq, integral_id_gaussianReal]
  have hvar : Var[X; P] = (1 : ℝ≥0) := by
    have h1 : Var[X; P] = Var[id ∘ X; P] := by simp
    rw [h1, ← variance_map (by rw [hlaw.map_eq]; exact aemeasurable_id) hlaw.aemeasurable,
        hlaw.map_eq]
    exact variance_id_gaussianReal
  rw [variance_eq_integral hmeas, hmean] at hvar
  simp only [sub_zero, NNReal.coe_one] at hvar
  exact hvar

lemma integral_mul_of_indep_std_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P)
    {j k : ℕ} (hjk : j ≠ k) :
    ∫ ω, a j ω * a k ω ∂P = 0 := by
  have hindep : (a j) ⟂ᵢ[P] (a k) := ha.indep.indepFun hjk
  have hmean_j : ∫ ω, a j ω ∂P = 0 := by
    have : ∫ x, id x ∂(P.map (a j)) = ∫ ω, id (a j ω) ∂P :=
      integral_map (ha.std_gaussian j).aemeasurable aestronglyMeasurable_id
    simp only [id] at this
    rw [← this, (ha.std_gaussian j).map_eq, integral_id_gaussianReal]
  have heq : ∫ ω, a j ω * a k ω ∂P = ∫ ω, (a j * a k) ω ∂P := by
    congr 1
  rw [heq, hindep.integral_mul_eq_mul_integral
    (ha.std_gaussian j).aemeasurable.aestronglyMeasurable
    (ha.std_gaussian k).aemeasurable.aestronglyMeasurable,
    hmean_j, zero_mul]

lemma integral_mul_self_of_std_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P) (k : ℕ) :
    ∫ ω, a k ω * a k ω ∂P = 1 := by
  have : ∫ ω, a k ω ^ 2 ∂P = 1 := integral_sq_of_std_gaussian (ha.std_gaussian k)
  simp only [sq] at this
  exact this

lemma wienerC0_sq : wienerC0 ^ 2 = 1 / Real.pi := by
  unfold wienerC0; rw [sq]
  exact Real.mul_self_sqrt (div_nonneg (by norm_num) Real.pi_nonneg)

lemma wienerC1_sq : wienerC1 ^ 2 = 2 / Real.pi := by
  unfold wienerC1; rw [sq]
  exact Real.mul_self_sqrt (div_nonneg (by norm_num) Real.pi_nonneg)


set_option maxHeartbeats 800000 in
lemma finite_parseval_iid_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P)
    (α β : ℕ → ℝ) (N : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range N, α k * a k ω) * (∑ k ∈ Finset.range N, β k * a k ω) ∂P =
    ∑ k ∈ Finset.range N, α k * β k := by

  simp_rw [Finset.sum_mul_sum]
  have hmemLp : ∀ k, MemLp (a k) 2 P :=
    fun k => (ha.std_gaussian k).hasGaussianLaw.memLp_two
  have hint_ij : ∀ i j, Integrable (fun ω => α i * a i ω * (β j * a j ω)) P := by
    intro i j
    have heq : (fun ω => α i * a i ω * (β j * a j ω)) =
        fun ω => (α i * β j) * (a i ω * a j ω) := by ext ω; ring
    rw [heq]
    apply Integrable.const_mul
    have hmul : Integrable (a i * a j) P :=
      MemLp.integrable_mul (p := 2) (q := 2) (hmemLp i) (hmemLp j)
    exact hmul.congr (by filter_upwards with ω; simp [Pi.mul_apply])
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint_ij i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hint_ij _ j)]

  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [show (fun ω => α i * a i ω * (β j * a j ω)) =
        fun ω => (α i * β j) * (a i ω * a j ω) from by ext ω; ring]
    rw [integral_const_mul]


  have heval : ∀ i j, α i * β j * ∫ ω, a i ω * a j ω ∂P =
      if i = j then α i * β i else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, integral_mul_self_of_std_gaussian ha i, mul_one]
    · rw [if_neg hij, integral_mul_of_indep_std_gaussian ha hij, mul_zero]
  simp_rw [heval, Finset.sum_ite_eq, Finset.mem_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (Finset.mem_range.mp hk)]






lemma eLpNorm_mul_le_L2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * g ω) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
    hf hg (fun a b => a * b) 1 (by filter_upwards with x; simp)
  simpa using h


set_option maxHeartbeats 800000 in
theorem tendsto_integral_prod_of_L2_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℕ → Ω → ℝ} (ha : IsIIDStdGaussian a P)
    (α β : ℕ → ℝ)
    (S T : Ω → ℝ) (hS : MemLp S 2 P) (hT : MemLp T 2 P)
    (hS_lim : Tendsto (fun n => eLpNorm
      (fun ω => (∑ k ∈ Finset.range n, α k * a k ω) - S ω) 2 P) atTop (nhds 0))
    (hT_lim : Tendsto (fun n => eLpNorm
      (fun ω => (∑ k ∈ Finset.range n, β k * a k ω) - T ω) 2 P) atTop (nhds 0)) :
    Tendsto (fun N => ∫ ω, (∑ k ∈ Finset.range N, α k * a k ω) *
      (∑ k ∈ Finset.range N, β k * a k ω) ∂P) atTop (nhds (∫ ω, S ω * T ω ∂P)) := by

  have hmemLp_a : ∀ k, MemLp (a k) 2 P :=
    fun k => (ha.std_gaussian k).hasGaussianLaw.memLp_two

  have hS_N : ∀ n, MemLp (fun ω => ∑ k ∈ Finset.range n, α k * a k ω) 2 P :=
    fun n => memLp_finset_sum _ fun k _ => (hmemLp_a k).const_mul (α k)
  have hT_N : ∀ n, MemLp (fun ω => ∑ k ∈ Finset.range n, β k * a k ω) 2 P :=
    fun n => memLp_finset_sum _ fun k _ => (hmemLp_a k).const_mul (β k)

  set S_N : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, α k * a k ω
  set T_N : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, β k * a k ω
  set dS : ℕ → Ω → ℝ := fun n ω => S_N n ω - S ω
  set dT : ℕ → Ω → ℝ := fun n ω => T_N n ω - T ω
  have hdS_meas : ∀ n, AEStronglyMeasurable (dS n) P :=
    fun n => (hS_N n).1.sub hS.1
  have hdT_meas : ∀ n, AEStronglyMeasurable (dT n) P :=
    fun n => (hT_N n).1.sub hT.1

  apply tendsto_integral_of_L1 (fun ω => S ω * T ω)
  · exact hS.integrable_mul (q := 2) hT
  · exact Eventually.of_forall fun n => (hS_N n).integrable_mul (q := 2) (hT_N n)
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm]

    have hbound : ∀ n, eLpNorm (fun ω => S_N n ω * T_N n ω - S ω * T ω) 1 P ≤
        eLpNorm (dS n) 2 P * eLpNorm (dT n) 2 P +
        eLpNorm S 2 P * eLpNorm (dT n) 2 P +
        eLpNorm (dS n) 2 P * eLpNorm T 2 P := by
      intro n
      have hdecomp : (fun ω => S_N n ω * T_N n ω - S ω * T ω) =
          fun ω => dS n ω * dT n ω + S ω * dT n ω + dS n ω * T ω := by
        ext ω; simp only [S_N, T_N, dS, dT]; ring
      rw [hdecomp]
      calc eLpNorm (fun ω => dS n ω * dT n ω + S ω * dT n ω + dS n ω * T ω) 1 P
          ≤ eLpNorm (fun ω => dS n ω * dT n ω + S ω * dT n ω) 1 P +
            eLpNorm (fun ω => dS n ω * T ω) 1 P :=
              eLpNorm_add_le (((hdS_meas n).mul (hdT_meas n)).add (hS.1.mul (hdT_meas n)))
                ((hdS_meas n).mul hT.1) le_rfl
        _ ≤ (eLpNorm (fun ω => dS n ω * dT n ω) 1 P +
              eLpNorm (fun ω => S ω * dT n ω) 1 P) +
            eLpNorm (fun ω => dS n ω * T ω) 1 P := by
              gcongr
              exact eLpNorm_add_le ((hdS_meas n).mul (hdT_meas n))
                (hS.1.mul (hdT_meas n)) le_rfl
        _ ≤ eLpNorm (dS n) 2 P * eLpNorm (dT n) 2 P +
            eLpNorm S 2 P * eLpNorm (dT n) 2 P +
            eLpNorm (dS n) 2 P * eLpNorm T 2 P := by
              gcongr
              · exact eLpNorm_mul_le_L2 (hdS_meas n) (hdT_meas n)
              · exact eLpNorm_mul_le_L2 hS.1 (hdT_meas n)
              · exact eLpNorm_mul_le_L2 (hdS_meas n) hT.1

    have htendsto_bound : Tendsto (fun n =>
        eLpNorm (dS n) 2 P * eLpNorm (dT n) 2 P +
        eLpNorm S 2 P * eLpNorm (dT n) 2 P +
        eLpNorm (dS n) 2 P * eLpNorm T 2 P) atTop (nhds 0) := by
      have h1 : Tendsto (fun n => eLpNorm (dS n) 2 P * eLpNorm (dT n) 2 P)
          atTop (nhds 0) := by
        simpa using ENNReal.Tendsto.mul hS_lim (Or.inr ENNReal.zero_ne_top)
          hT_lim (Or.inr ENNReal.zero_ne_top)
      have h2 : Tendsto (fun n => eLpNorm S 2 P * eLpNorm (dT n) 2 P)
          atTop (nhds 0) := by
        simpa using ENNReal.Tendsto.const_mul hT_lim (Or.inr hS.eLpNorm_lt_top.ne)
      have h3 : Tendsto (fun n => eLpNorm (dS n) 2 P * eLpNorm T 2 P)
          atTop (nhds 0) := by
        simpa using ENNReal.Tendsto.mul_const hS_lim (Or.inr hT.eLpNorm_lt_top.ne)
      simpa using (h1.add h2).add h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      htendsto_bound (fun _ => zero_le _) hbound




set_option maxHeartbeats 400000 in
theorem summable_wienerBasisCoeff_sq (s : ℝ) :
    Summable (fun k => wienerBasisCoeff s k ^ 2) := by
  rw [← summable_nat_add_iff 1]
  have hpseries : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  have hshifted := (summable_nat_add_iff 1).mpr hpseries

  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (hshifted.mul_left (wienerC1 ^ 2))
  simp only [wienerBasisCoeff, Nat.succ_ne_zero, ite_false]

  rw [div_eq_mul_inv]

  rw [mul_pow, mul_pow, inv_pow]


  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_of_le_one_left (by positivity)
  exact Real.sin_sq_le_one _


theorem summable_wienerBasisCoeff_mul (s t : ℝ) :
    Summable (fun k => wienerBasisCoeff s k * wienerBasisCoeff t k) := by
  have hbound : Summable (fun k => (wienerBasisCoeff s k ^ 2 + wienerBasisCoeff t k ^ 2) / 2) :=
    ((summable_wienerBasisCoeff_sq s).add (summable_wienerBasisCoeff_sq t)).div_const 2
  exact Summable.of_norm_bounded hbound (fun k => by
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := sq_abs (wienerBasisCoeff s k)
    have h2 := sq_abs (wienerBasisCoeff t k)
    nlinarith [sq_nonneg (|wienerBasisCoeff s k| - |wienerBasisCoeff t k|)])

/-- Closed-form decomposition of the coefficient pairing
$\sum_k c_k(s)\,c_k(t)$ into the constant-mode term $st/\pi$ and the sine-series
tail $\tfrac{2}{\pi}\sum_{k\ge 1}\sin(ks)\sin(kt)/k^2$, where $c_k$ are the
Wiener basis coefficients. -/
lemma tsum_wienerBasisCoeff_eq (s t : ℝ) :
    ∑' k, wienerBasisCoeff s k * wienerBasisCoeff t k =
    s * t / Real.pi +
    2 / Real.pi * ∑' k : ℕ, Real.sin (↑(k + 1) * s) * Real.sin (↑(k + 1) * t) / (↑(k + 1)) ^ 2 := by
  rw [(summable_wienerBasisCoeff_mul s t).tsum_eq_zero_add]
  congr 1
  · simp only [wienerBasisCoeff, ite_true]
    have : wienerC0 * s * (wienerC0 * t) = wienerC0 ^ 2 * (s * t) := by rw [sq]; ring
    rw [this, wienerC0_sq]; ring
  · rw [← tsum_mul_left]
    congr 1; ext k
    simp only [wienerBasisCoeff, Nat.succ_ne_zero, ite_false]
    have hc1 : wienerC1 * Real.sin (↑(k + 1) * s) / ↑(k + 1) *
      (wienerC1 * Real.sin (↑(k + 1) * t) / ↑(k + 1)) =
      wienerC1 ^ 2 * (Real.sin (↑(k + 1) * s) * Real.sin (↑(k + 1) * t) / ↑(k + 1) ^ 2) := by
      rw [sq]; ring
    rw [hc1, wienerC1_sq]


/-- Helper: evaluate the second Bernoulli polynomial under the
$\mathbb{Q}\to\mathbb{R}$ algebra map, giving $B_2(x) = x^2 - x + 1/6$. -/
lemma eval_bernoulli_2_map_real (x : ℝ) :
    Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)) =
    x ^ 2 - x + 1 / 6 := by
  simp only [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [bernoulli, Nat.choose]
  norm_num
  ring

/-- Closed-form for the Fourier cosine series with $1/k^2$ coefficients on
$[0,2\pi]$: $\sum_{n\ge 1} \cos(n\theta)/n^2 = \theta^2/4 - \pi\theta/2 + \pi^2/6$.
This is the classical Bernoulli evaluation of the second Bernoulli polynomial. -/
lemma hasSum_cos_div_sq (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (↑n * θ))
      (θ ^ 2 / 4 - Real.pi * θ / 2 + Real.pi ^ 2 / 6) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  set x := θ / (2 * Real.pi) with hx_def
  have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hθ.1 (le_of_lt h2pi_pos)
    · rw [div_le_one h2pi_pos]; exact hθ.2
  have key := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx_mem
  have h_func_eq : (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (↑n * θ)) =
      (fun n : ℕ => 1 / (n : ℝ) ^ (2 * 1) * Real.cos (2 * Real.pi * ↑n * x)) := by
    ext n
    have h1 : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 * 1) := by norm_num
    have h2 : (↑n : ℝ) * θ = 2 * Real.pi * ↑n * x := by rw [hx_def]; field_simp
    rw [h1, h2]
  rw [h_func_eq]
  convert key using 1
  have hB : Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))) =
      x ^ 2 - x + 1 / 6 := by
    show Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)) = _
    exact eval_bernoulli_2_map_real x
  rw [hB]
  simp only [Nat.factorial]
  norm_num
  rw [hx_def]
  field_simp
  ring

/-- Product-to-sum identity:
$\sin(ks)\sin(kt) = \tfrac12\bigl(\cos(k(t-s)) - \cos(k(s+t))\bigr)$. -/
lemma sin_mul_sin_eq' (k s t : ℝ) :
    Real.sin (k * s) * Real.sin (k * t) =
    (Real.cos (k * (t - s)) - Real.cos (k * (s + t))) / 2 := by
  have h1 := Real.cos_sub (k * s) (k * t)
  have h2 := Real.cos_add (k * s) (k * t)
  rw [show k * s - k * t = -(k * (t - s)) from by ring] at h1
  rw [Real.cos_neg] at h1
  rw [show k * s + k * t = k * (s + t) from by ring] at h2
  linarith

/-- Closed-form evaluation of the sine cross-product series on $[0,\pi]$:
for $0 \le s \le t \le \pi$,
$\sum_{k\ge 1}\sin(ks)\sin(kt)/k^2 = s(\pi-t)/2$.
This is the off-diagonal Fourier expansion that yields the Brownian covariance
$s \wedge t$. -/
lemma tsum_sin_product_eq
    (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ Real.pi) (ht : 0 ≤ t) (ht' : t ≤ Real.pi)
    (hst : s ≤ t) :
    ∑' k : ℕ, Real.sin (↑(k + 1) * s) * Real.sin (↑(k + 1) * t) / (↑(k + 1)) ^ 2 =
    s * (Real.pi - t) / 2 := by
  have h_eq : (fun k : ℕ => Real.sin (↑(k + 1) * s) * Real.sin (↑(k + 1) * t) / (↑(k + 1)) ^ 2) =
    (fun k : ℕ => 1 / 2 * (1 / (↑(k + 1)) ^ 2 * Real.cos (↑(k + 1) * (t - s)) -
                            1 / (↑(k + 1)) ^ 2 * Real.cos (↑(k + 1) * (s + t)))) := by
    ext k; rw [sin_mul_sin_eq']; ring
  rw [h_eq]
  have h_ts : t - s ∈ Set.Icc 0 (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have h_st : s + t ∈ Set.Icc 0 (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hs1 := hasSum_cos_div_sq (t - s) h_ts
  have hs2 := hasSum_cos_div_sq (s + t) h_st
  have h_shift1 : HasSum (fun k : ℕ => 1 / (↑(k + 1)) ^ 2 * Real.cos (↑(k + 1) * (t - s)))
    ((t - s) ^ 2 / 4 - Real.pi * (t - s) / 2 + Real.pi ^ 2 / 6) := by
    rw [hasSum_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 2 * Real.cos (↑n * (t - s))) 1]
    simp only [Finset.sum_range_one]
    norm_num
    simp only [one_div] at hs1
    exact hs1
  have h_shift2 : HasSum (fun k : ℕ => 1 / (↑(k + 1)) ^ 2 * Real.cos (↑(k + 1) * (s + t)))
    ((s + t) ^ 2 / 4 - Real.pi * (s + t) / 2 + Real.pi ^ 2 / 6) := by
    rw [hasSum_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 2 * Real.cos (↑n * (s + t))) 1]
    simp only [Finset.sum_range_one]
    norm_num
    simp only [one_div] at hs2
    exact hs2
  have h_sub := h_shift1.sub h_shift2
  have h_final := h_sub.const_smul (1 / 2 : ℝ)
  simp only [smul_eq_mul] at h_final
  rw [h_final.tsum_eq]
  ring


/-- Algebraic identity collapsing the Wiener covariance decomposition: when
$s \le t$, $st/\pi + (2/\pi)\cdot s(\pi-t)/2 = s = s \wedge t$. -/
lemma covariance_algebra_le (s t : ℝ) (hst : s ≤ t) :
    s * t / Real.pi + 2 / Real.pi * (s * (Real.pi - t) / 2) = min s t := by
  rw [min_eq_left hst]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring



/-- Cauchy-Schwarz on intervals: the square of an interval integral is bounded
by the length times the integral of the square,
$\bigl(\int_0^L g\bigr)^2 \le L\int_0^L g^2$. -/
lemma sq_intervalIntegral_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hg_int : IntervalIntegrable g volume 0 L)
    (hg2_int : IntervalIntegrable (fun t => g t ^ 2) volume 0 L) :
    (∫ t in (0 : ℝ)..L, g t) ^ 2 ≤ L * ∫ t in (0 : ℝ)..L, g t ^ 2 := by
  set I := ∫ t in (0:ℝ)..L, g t
  set I2 := ∫ t in (0:ℝ)..L, g t ^ 2
  set c := I / L
  have hc_int : IntervalIntegrable (fun _ => c) volume 0 L :=
    intervalIntegrable_const
  have h_expand : ∫ t in (0:ℝ)..L, (g t - c) ^ 2 = I2 - 2 * c * I + c ^ 2 * L := by
    have : (fun t => (g t - c) ^ 2) = fun t => g t ^ 2 - 2 * c * g t + c ^ 2 := by ext; ring
    rw [this]
    have h1 : IntervalIntegrable (fun t => g t ^ 2 - 2 * c * g t)
        volume 0 L :=
      hg2_int.sub (hg_int.const_mul _)
    rw [intervalIntegral.integral_add h1 intervalIntegrable_const]
    rw [intervalIntegral.integral_sub hg2_int (hg_int.const_mul _)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul, sub_zero]
    ring
  have h_nn : 0 ≤ ∫ t in (0:ℝ)..L, (g t - c) ^ 2 := by
    apply intervalIntegral.integral_nonneg hL.le
    intro t _; exact sq_nonneg _
  rw [h_expand] at h_nn
  have hL_ne : L ≠ 0 := ne_of_gt hL
  nlinarith [sq_nonneg I, sq_nonneg c, sq_nonneg L, div_mul_cancel₀ I hL_ne]




/-- The squared norm $\|f'(re^{it})\|^2$ of the random-power-series derivative
is interval-integrable on $[0, 2\pi]$ for any $r \in (0,1)$. -/
theorem powerSeriesDeriv_sq_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ω : Ω) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (fun t =>
      ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 2)
      volume 0 (2 * Real.pi) := by


  have h_norm_eq : ∀ (j : ℕ) (t : ℝ),
      ‖(a (j + 1) ω : ℂ) * (↑r * exp (↑t * I)) ^ j‖ = ‖(a (j + 1) ω : ℂ)‖ * r ^ j := by
    intro j t
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Complex.norm_exp_ofReal_mul_I, mul_one]


  by_cases hs : Summable (fun j => ‖(a (j + 1) ω : ℂ)‖ * r ^ j)
  ·
    have hcont_tsum : Continuous (fun (t : ℝ) =>
        ∑' j, (a (j + 1) ω : ℂ) * (↑r * exp (↑t * I)) ^ j) := by
      apply continuous_tsum
      · intro j
        exact (continuous_const.mul
          ((continuous_const.mul
            (Complex.continuous_exp.comp
              (continuous_ofReal.mul continuous_const))).pow j))
      · exact hs
      · intro j t; exact le_of_eq (h_norm_eq j t)
    exact (hcont_tsum.norm.pow 2).intervalIntegrable 0 (2 * Real.pi)
  ·
    have h_zero : ∀ t : ℝ, powerSeriesDeriv a (↑r * exp (↑t * I)) ω = 0 := by
      intro t
      unfold powerSeriesDeriv
      apply tsum_eq_zero_of_not_summable
      intro hsumm
      exact hs ((summable_norm_iff (E := ℂ)).mpr hsumm |>.congr (h_norm_eq · t))
    simp only [h_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact intervalIntegrable_const


/-- The fourth-power norm $\|f'(re^{it})\|^4$ of the random-power-series
derivative is interval-integrable on $[0, 2\pi]$ for any $r \in (0,1)$; needed
later for the Cauchy-Schwarz step in the gradient bound. -/
theorem powerSeriesDeriv_pow4_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ω : Ω) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (fun t =>
      (‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 2) ^ 2)
      volume 0 (2 * Real.pi) := by
  have h_norm_eq : ∀ (j : ℕ) (t : ℝ),
      ‖(a (j + 1) ω : ℂ) * (↑r * exp (↑t * I)) ^ j‖ = ‖(a (j + 1) ω : ℂ)‖ * r ^ j := by
    intro j t
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  by_cases hs : Summable (fun j => ‖(a (j + 1) ω : ℂ)‖ * r ^ j)
  · have hcont_tsum : Continuous (fun (t : ℝ) =>
        ∑' j, (a (j + 1) ω : ℂ) * (↑r * exp (↑t * I)) ^ j) := by
      apply continuous_tsum
      · intro j
        exact (continuous_const.mul
          ((continuous_const.mul
            (Complex.continuous_exp.comp
              (continuous_ofReal.mul continuous_const))).pow j))
      · exact hs
      · intro j t; exact le_of_eq (h_norm_eq j t)
    exact ((hcont_tsum.norm.pow 2).pow 2).intervalIntegrable 0 (2 * Real.pi)
  · have h_zero : ∀ t : ℝ, powerSeriesDeriv a (↑r * exp (↑t * I)) ω = 0 := by
      intro t
      unfold powerSeriesDeriv
      apply tsum_eq_zero_of_not_summable
      intro hsumm
      exact hs ((summable_norm_iff (E := ℂ)).mpr hsumm |>.congr (h_norm_eq · t))
    simp only [h_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact intervalIntegrable_const








/-- AM-GM bridge: if $(\|a_{k+1}(\omega)\|^2)$ is summable, then so is
$(\|a_{k+1}(\omega)\|/(k+1))$, since $|a|/(k+1) \le \tfrac12(|a|^2 + 1/(k+1)^2)$
and the $1/(k+1)^2$ series converges. -/
lemma summable_div_of_sq_summable
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ω : Ω)
    (hsq : Summable (fun k : ℕ => ‖(a (k + 1) ω : ℂ)‖ ^ 2)) :
    Summable (fun k : ℕ => ‖(a (k + 1) ω : ℂ)‖ / (↑(k + 1) : ℝ)) := by
  have h_inv : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ (2 : ℝ))⁻¹) := by
    convert (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
      Nat.succ_injective using 1
    ext n; simp [Nat.cast_succ]
  have hbound : Summable (fun k : ℕ =>
      ‖(a (k + 1) ω : ℂ)‖ ^ 2 / 2 + (((k : ℝ) + 1) ^ (2 : ℝ))⁻¹ / 2) :=
    (hsq.div_const 2).add (h_inv.div_const 2)
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hbound
  intro k
  have hk : (0 : ℝ) < (↑(k + 1) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  have hk' : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [div_eq_mul_inv]
  have h_amgm : ‖(a (k + 1) ω : ℂ)‖ * (↑(k + 1) : ℝ)⁻¹ ≤
      (‖(a (k + 1) ω : ℂ)‖ ^ 2 + (↑(k + 1) : ℝ)⁻¹ ^ 2) / 2 := by
    have := sq_nonneg (‖(a (k + 1) ω : ℂ)‖ - (↑(k + 1) : ℝ)⁻¹)
    nlinarith
  calc ‖(a (k + 1) ω : ℂ)‖ * (↑(k + 1) : ℝ)⁻¹
      ≤ (‖(a (k + 1) ω : ℂ)‖ ^ 2 + (↑(k + 1) : ℝ)⁻¹ ^ 2) / 2 := h_amgm
    _ ≤ ‖(a (k + 1) ω : ℂ)‖ ^ 2 / 2 + (((k : ℝ) + 1) ^ (2 : ℝ))⁻¹ / 2 := by
        rw [inv_pow, hk', ← Real.rpow_natCast ((k : ℝ) + 1) 2]
        ring_nf; exact le_refl _
















/-- Transfer step (Lemma 5): a Hölder estimate on the boundary trace
$t\mapsto f(e^{it})$ implies continuity of the Wiener process $t\mapsto W_t$
on $[0,\pi]$. The imaginary part of the boundary values recovers the sine
series defining $W_t$. -/
theorem holder_boundary_implies_wiener_continuousOn
    {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (ω : Ω)
    (C' : ℝ) (α : ℝ) (hC' : 0 < C') (hα : 0 < α)
    (hholder : ∀ t₁ t₂ : ℝ,
      ‖randomPowerSeries a (circleMap 0 1 t₁) ω -
       randomPowerSeries a (circleMap 0 1 t₂) ω‖ ≤ C' * |t₁ - t₂| ^ α)
    (hsummable : ∀ t : ℝ, Summable (fun k =>
      (a (k + 1) ω : ℂ) * (circleMap 0 1 t) ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ))) :
    ContinuousOn (fun t => wienerProcess a t ω) (Icc 0 Real.pi) := by
  unfold wienerProcess
  apply ContinuousOn.add
  · exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const continuousOn_const)
      continuousOn_id
  · apply ContinuousOn.mul continuousOn_const
    have hF_cont : Continuous (fun t => randomPowerSeries a (circleMap 0 1 t) ω) := by
      rw [Metric.continuous_iff]
      intro x ε hε
      refine ⟨(ε / C') ^ (1 / α), by positivity, fun y hy => ?_⟩
      simp only [dist_eq_norm] at hy ⊢
      have h1 : ‖randomPowerSeries a (circleMap 0 1 y) ω -
          randomPowerSeries a (circleMap 0 1 x) ω‖ ≤ C' * |y - x| ^ α := hholder y x
      have h3 : |y - x| < (ε / C') ^ (1 / α) := by rwa [Real.norm_eq_abs] at hy
      have h4 : C' * |y - x| ^ α < C' * ((ε / C') ^ (1 / α)) ^ α := by gcongr
      have h5 : ((ε / C') ^ (1 / α)) ^ α = ε / C' := by
        rw [← Real.rpow_mul (le_of_lt (by positivity : (0 : ℝ) < ε / C'))]
        simp only [one_div, inv_mul_cancel₀ (ne_of_gt hα)]
        exact Real.rpow_one _
      have h6 : C' * ((ε / C') ^ (1 / α)) ^ α = ε := by rw [h5]; field_simp
      linarith
    have hIm_cont : ContinuousOn
        (fun t => (randomPowerSeries a (circleMap 0 1 t) ω).im) (Icc 0 Real.pi) :=
      (Complex.continuous_im.comp hF_cont).continuousOn
    apply hIm_cont.congr
    intro t _ht
    simp only [randomPowerSeries]
    rw [Complex.im_tsum (hsummable t)]
    congr 1
    ext k
    simp only [circleMap_zero, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_nat_mul]
    have hexp : (↑(k + 1) : ℂ) * (↑t * Complex.I) =
        ↑((↑(k + 1) : ℝ) * t) * Complex.I := by push_cast; ring
    rw [hexp, Complex.exp_mul_I]
    rw [show (↑(k + 1 : ℕ) : ℂ) = (↑(↑(k + 1 : ℕ) : ℝ) : ℂ) from by push_cast; rfl]
    rw [Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_im]
    ring



end WienerConstruction
