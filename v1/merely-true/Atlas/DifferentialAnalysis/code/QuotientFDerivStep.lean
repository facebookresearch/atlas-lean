/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Complex.Basic
import Atlas.DifferentialAnalysis.code.SmoothingOperators

open MvPolynomial Complex

noncomputable section


/-- The scalar multiplication of `ℝ` on `ℂ` is continuous, exhibited as a
`ContinuousSMul` instance.  This is used downstream when differentiating
real-linear maps with complex codomain. -/
instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    simp only [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

set_option maxHeartbeats 1600000

namespace DifferentialOperators

variable {n : ℕ}

/-- The continuous real-linear map sending `ξ ∈ EuclideanSpace ℝ (Fin n)` to
its `i`-th coordinate, viewed as a complex number `(ξ i : ℂ)`. -/
noncomputable def coordCLM (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin n => ℝ) i)

/-- Evaluating `coordCLM i` at `ξ` returns `(ξ i : ℂ)`. -/
@[simp]
lemma coordCLM_apply (i : Fin n) (ξ : EuclideanSpace ℝ (Fin n)) :
    coordCLM i ξ = (ξ i : ℂ) := by simp [coordCLM, PiLp.proj]

/-- The evaluation of a multivariate complex polynomial at a real point,
viewed as a function `EuclideanSpace ℝ (Fin n) → ℂ`, is real-differentiable
everywhere. -/
lemma evalAtReal_differentiable (Q : MvPolynomial (Fin n) ℂ) :
    Differentiable ℝ (evalAtReal Q) := by
  unfold evalAtReal
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [eval_C]; exact differentiable_const c
  | add p q hp hq =>
    have h : (fun ξ : EuclideanSpace ℝ (Fin n) => (p + q).eval (fun i => (ξ i : ℂ))) =
      (fun ξ => p.eval (fun i => (ξ i : ℂ)) + q.eval (fun i => (ξ i : ℂ))) := by
      ext ξ; simp [map_add]
    rw [h]; exact hp.add hq
  | mul_X p i hp =>
    have h : (fun ξ : EuclideanSpace ℝ (Fin n) => (p * X i).eval (fun i => (ξ i : ℂ))) =
      (fun ξ => p.eval (fun i => (ξ i : ℂ)) * (ξ i : ℂ)) := by
      ext ξ; simp [eval_mul, eval_X]
    rw [h]; exact hp.mul (ofRealCLM.differentiable.comp (by fun_prop))

/-- The directional derivative of `evalAtReal Q` along the `j`-th standard
basis vector equals the evaluation of the formal partial derivative `pderiv j Q`. -/
theorem fderiv_evalAtReal_single (Q : MvPolynomial (Fin n) ℂ) (j : Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (evalAtReal Q) ξ (EuclideanSpace.single j 1) =
      evalAtReal (pderiv j Q) ξ := by
  unfold evalAtReal
  induction Q using MvPolynomial.induction_on with
  | C c =>
    have : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (C c)) =
      fun _ => c := by ext; simp [eval_C]
    rw [this]; simp
  | add p q hp hq =>
    have hfun : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (p + q)) =
      (fun ξ' => eval (fun i => (ξ' i : ℂ)) p + eval (fun i => (ξ' i : ℂ)) q) := by
      ext; simp [map_add]
    rw [hfun]
    have hdp := (evalAtReal_differentiable (n := n) p).differentiableAt (x := ξ)
    have hdq := (evalAtReal_differentiable (n := n) q).differentiableAt (x := ξ)
    have key : fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n) =>
      eval (fun i => (ξ' i : ℂ)) p + eval (fun i => (ξ' i : ℂ)) q) ξ =
      fderiv ℝ (fun ξ' => eval (fun i => (ξ' i : ℂ)) p) ξ +
      fderiv ℝ (fun ξ' => eval (fun i => (ξ' i : ℂ)) q) ξ :=
      (hdp.hasFDerivAt.add hdq.hasFDerivAt).fderiv
    rw [key, ContinuousLinearMap.add_apply, hp, hq, map_add, eval_add]
  | mul_X p i hp =>
    have hfun : (fun ξ' : EuclideanSpace ℝ (Fin n) => eval (fun i => (ξ' i : ℂ)) (p * X i)) =
      (fun ξ' => eval (fun i => (ξ' i : ℂ)) p * (ξ' i : ℂ)) := by
      ext; simp [eval_mul, eval_X]
    rw [hfun]
    have hdp := (evalAtReal_differentiable (n := n) p).differentiableAt (x := ξ)
    have hdc : HasFDerivAt (fun ξ' : EuclideanSpace ℝ (Fin n) => (ξ' i : ℂ))
      (coordCLM i) ξ := by
      have : (fun ξ' : EuclideanSpace ℝ (Fin n) => (ξ' i : ℂ)) = coordCLM i := by
        ext v; simp
      rw [this]; exact (coordCLM i).hasFDerivAt
    have key : fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n) =>
      eval (fun k => (ξ' k : ℂ)) p * (ξ' i : ℂ)) ξ =
      eval (fun k => (ξ k : ℂ)) p • coordCLM i +
      (ξ i : ℂ) • fderiv ℝ (fun ξ' => eval (fun k => (ξ' k : ℂ)) p) ξ :=
      (hdp.hasFDerivAt.mul hdc).fderiv
    rw [key, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, hp, coordCLM_apply,
        pderiv_mul, eval_add, eval_mul, eval_mul, eval_X, pderiv_X]
    simp only [Pi.single_apply, smul_eq_mul]

    simp only [EuclideanSpace.single, PiLp.single, Pi.single_apply]
    split_ifs with h
    · subst h; simp only [map_one]; push_cast; ring
    · simp only [map_zero]; push_cast; ring

/-- The straight-line curve `t ↦ ξ + t · eⱼ` from `ξ` in the direction of the
`j`-th basis vector has derivative `eⱼ` at `t = 0`. -/
lemma hasDerivAt_curve (ξ : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    HasDerivAt (fun t : ℝ => ξ + t • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) 0 := by
  have h : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ))
    ((1 : ℝ) • EuclideanSpace.single j (1 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const _
  simp only [one_smul] at h
  have := (hasDerivAt_const 0 ξ).add h
  simp only [zero_add] at this
  exact this

/-- A "quotient rule" for the directional derivative of `Q / P^k`: at any
point where `P` does not vanish, the directional derivative along `eⱼ` of
`ξ' ↦ evalAtReal Q ξ' / (evalAtReal P ξ')^k` equals
`evalAtReal (P · pderiv j Q − k · (Q · pderiv j P)) ξ / (evalAtReal P ξ)^(k+1)`.
This is the inductive step used to compute derivatives of `polyReciprocal`. -/
theorem quotient_fderiv_step (P Q : MvPolynomial (Fin n) ℂ) (k : ℕ) (j : Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) (hP : evalAtReal P ξ ≠ 0) :
    fderiv ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ
      (EuclideanSpace.single j 1) =
      evalAtReal (P * pderiv j Q - (k : ℕ) • (Q * pderiv j P)) ξ /
        (evalAtReal P ξ) ^ (k + 1) := by

  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  set γ := fun t : ℝ => ξ + t • eⱼ
  have hγ : HasDerivAt γ eⱼ 0 := hasDerivAt_curve ξ j
  have hγ0 : γ 0 = ξ := by simp [γ]
  set Qγ := fun t : ℝ => evalAtReal Q (γ t)
  set Pγ := fun t : ℝ => evalAtReal P (γ t)
  have hQ_da := (evalAtReal_differentiable Q).differentiableAt (x := ξ)
  have hP_da := (evalAtReal_differentiable P).differentiableAt (x := ξ)
  have hPk_ne : (evalAtReal P ξ) ^ k ≠ 0 := pow_ne_zero k hP

  have hQγ : HasDerivAt Qγ (evalAtReal (pderiv j Q) ξ) 0 := by
    show HasDerivAt (evalAtReal Q ∘ γ) _ 0
    have := (hγ0 ▸ hQ_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0, fderiv_evalAtReal_single] at this
  have hPγ : HasDerivAt Pγ (evalAtReal (pderiv j P) ξ) 0 := by
    show HasDerivAt (evalAtReal P ∘ γ) _ 0
    have := (hγ0 ▸ hP_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0, fderiv_evalAtReal_single] at this

  have hPkγ : HasDerivAt (fun t => Pγ t ^ k)
    ((k : ℂ) * Pγ 0 ^ (k - 1) * evalAtReal (pderiv j P) ξ) 0 :=
    hPγ.pow k

  have hPγ0 : Pγ 0 = evalAtReal P ξ := by simp [Pγ, hγ0]
  have hPk0 : Pγ 0 ^ k ≠ 0 := hPγ0 ▸ hPk_ne
  have hdiv : HasDerivAt (fun t => Qγ t / Pγ t ^ k)
    ((evalAtReal (pderiv j Q) ξ * Pγ 0 ^ k -
      Qγ 0 * ((k : ℂ) * Pγ 0 ^ (k - 1) * evalAtReal (pderiv j P) ξ)) /
     (Pγ 0 ^ k) ^ 2) 0 :=
    hQγ.div hPkγ hPk0

  have hfγ : HasDerivAt (fun t => evalAtReal Q (γ t) / (evalAtReal P (γ t)) ^ k)
    (fderiv ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ eⱼ) 0 := by
    have hf_da : DifferentiableAt ℝ (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ :=
      hQ_da.mul ((hP_da.pow k).inv hPk_ne)
    have := (hγ0 ▸ hf_da.hasFDerivAt).comp_hasDerivAt 0 hγ
    rwa [hγ0] at this

  have huniq := hfγ.unique hdiv
  rw [huniq]
  simp only [hγ0, Qγ, Pγ]

  simp only [evalAtReal, map_sub, map_mul, map_nsmul]
  have hPne : evalAtReal P ξ ≠ 0 := hP
  simp only [evalAtReal] at hPne
  set p := (eval fun i => (ξ i : ℂ)) P
  set q := (eval fun i => (ξ i : ℂ)) Q
  set dq := (eval fun i => (ξ i : ℂ)) (pderiv j Q)
  set dp := (eval fun i => (ξ i : ℂ)) (pderiv j P)
  have hp_ne : p ≠ 0 := hPne
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp_ne
  rw [nsmul_eq_mul, Nat.cast_comm]
  field_simp [hp_ne, hpk_ne]
  rcases k with _ | k
  · simp
  · simp only [Nat.succ_sub_one, pow_succ]
    ring

end DifferentialOperators

end
