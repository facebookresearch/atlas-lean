/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped ZeroAtInfty
open Filter Topology

noncomputable section

namespace TestFunctions

variable (n : ℕ)

/-- A continuous, complex-valued function on `ℝⁿ` that vanishes at infinity, is `C¹`,
and whose first-order partial derivatives also vanish at infinity. -/
structure ContDiffZeroAtInfty extends
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  contDiff_one : ContDiff ℝ 1 ⇑toZeroAtInftyContinuousMap
  partialDeriv_zero_at_infty (j : Fin n) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (⇑toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1))
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

section RestrictionOfFunctionals

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {U : Type*} [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Pullback of continuous linear functionals along a continuous linear map
`ι : V →L[𝕜] U`: sends a dual element on `U` to its restriction along `ι`. -/
def restrictDual (ι : V →L[𝕜] U) : (U →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜) :=
  (compL 𝕜 V U 𝕜).flip ι

/-- `restrictDual ι L` is just `L ∘ ι`. -/
@[simp]
theorem restrictDual_apply (ι : V →L[𝕜] U) (L : U →L[𝕜] 𝕜) :
    restrictDual ι L = L.comp ι :=
  rfl

/-- Operator-norm bound for `restrictDual`: if `‖ι‖ ≤ C`, then `‖L ∘ ι‖ ≤ C * ‖L‖`. -/
theorem norm_restrictDual_le (ι : V →L[𝕜] U) (L : U →L[𝕜] 𝕜) {C : ℝ}
    (hC : ‖ι‖ ≤ C) : ‖restrictDual ι L‖ ≤ C * ‖L‖ := by
  calc ‖restrictDual ι L‖ = ‖L.comp ι‖ := rfl
    _ ≤ ‖L‖ * ‖ι‖ := L.opNorm_comp_le ι
    _ ≤ ‖L‖ * C := by gcongr
    _ = C * ‖L‖ := mul_comm _ _

/-- If `ι` has dense range, then its dual `restrictDual ι` is injective: a continuous
functional is determined by its values on a dense subspace. -/
theorem restrictDual_injective (ι : V →L[𝕜] U) (hd : DenseRange ι) :
    Function.Injective (restrictDual ι) := by
  intro L₁ L₂ h
  simp only [restrictDual_apply] at h
  have heq : (⇑L₁) ∘ (⇑ι) = (⇑L₂) ∘ (⇑ι) := by
    ext v
    exact ContinuousLinearMap.ext_iff.mp h v
  exact ContinuousLinearMap.ext
    (fun u => congr_fun (DenseRange.equalizer hd L₁.continuous L₂.continuous heq) u)

/-- Combined statement: `restrictDual` is bounded by `C` on operator norms, and is
injective whenever `ι` has dense range. -/
theorem restrictDual_norm_bound_and_injective
    (ι : V →L[𝕜] U) (C : ℝ) (hC : ‖ι‖ ≤ C) :
    (∀ L : U →L[𝕜] 𝕜, ‖restrictDual ι L‖ ≤ C * ‖L‖) ∧
    (DenseRange ι → Function.Injective (restrictDual ι)) :=
  ⟨fun L => norm_restrictDual_le ι L hC, fun hd => restrictDual_injective ι hd⟩

end RestrictionOfFunctionals

/-- The `C^k` sup-norm of a function `f : ℝⁿ → ℂ`: sum of sup norms of all partial
derivatives up to order `k`. -/
def ckNorm (n : ℕ) : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ
  | 0, f => ⨆ x, ‖f x‖
  | k + 1, f =>
    ckNorm n k f +
      Finset.sum Finset.univ fun j : Fin n =>
        ckNorm n k fun x => fderiv ℝ f x (EuclideanSpace.single j 1)

/-- The space of `C^k` functions on `ℝⁿ` vanishing at infinity together with all of
their iterated derivatives up to order `k`. -/
structure ContDiffZeroAtInftyN (n : ℕ) (k : ℕ) extends
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  contDiff_k : ContDiff ℝ k ⇑toZeroAtInftyContinuousMap
  iteratedFDeriv_zero_at_infty (m : ℕ) (hm : m ≤ k) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ m (⇑toZeroAtInftyContinuousMap) x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

variable {n}

/-- The `C^k`-norm of an element of `ContDiffZeroAtInftyN n k`. -/
def ContDiffZeroAtInftyN.normCk {k : ℕ} (u : ContDiffZeroAtInftyN n k) : ℝ :=
  ckNorm n k ⇑u.toZeroAtInftyContinuousMap

section WeightedSpaces

variable (n : ℕ)

/-- The Japanese bracket `⟨x⟩ := √(1 + ‖x‖²)`, a smooth weight comparable to `‖x‖`
at infinity used to define weighted function spaces. -/
def japaneseBracket (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

/-- The Japanese bracket `⟨x⟩` is strictly positive. -/
theorem japaneseBracket_pos (x : EuclideanSpace ℝ (Fin n)) :
    0 < japaneseBracket n x := by
  unfold japaneseBracket
  apply Real.sqrt_pos_of_pos
  positivity

/-- The Japanese bracket `⟨x⟩` is nonzero. -/
theorem japaneseBracket_ne_zero (x : EuclideanSpace ℝ (Fin n)) :
    japaneseBracket n x ≠ 0 :=
  ne_of_gt (japaneseBracket_pos n x)

/-- Weighted `C^k`-functions on `ℝⁿ` vanishing at infinity: an element is represented
by a witness `v ∈ C^k` whose ratio against `⟨x⟩^{-l}` lies in the original space. -/
structure WeightedContDiffZeroAtInfty (n : ℕ) (k : ℕ) (l : ℕ) where
  witnessV : ContDiffZeroAtInftyN n k

/-- Underlying function `⟨x⟩^{-l} v(x)` for a weighted `C^k` element with witness `v`. -/
def WeightedContDiffZeroAtInfty.toFun {k l : ℕ}
    (u : WeightedContDiffZeroAtInfty n k l) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(japaneseBracket n x ^ l))⁻¹ * u.witnessV.toZeroAtInftyContinuousMap x

end WeightedSpaces

section SchwartzSpace

variable (n : ℕ)

/-- The Schwartz space described as functions on `ℝⁿ` lying in every weighted
`C^k`-space with weight `⟨x⟩^{-l}` (Melrose Prop 7.3 characterisation). -/
structure SchwartzTestFunctionSpace where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  mem_weightedSpace (k l : ℕ) : ∃ w : WeightedContDiffZeroAtInfty n k l,
    ∀ x, toFun x = WeightedContDiffZeroAtInfty.toFun n w x

/-- Standard Schwartz space `𝓢(ℝⁿ, ℂ)` abbreviation. -/
abbrev schwartzSpace (n : ℕ) := SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ

namespace SchwartzTestFunctionSpace

variable {n : ℕ}

/-- `SchwartzTestFunctionSpace n` coerces to functions `ℝⁿ → ℂ`. -/
instance instFunLike : FunLike (SchwartzTestFunctionSpace n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Function-extensionality for elements of `SchwartzTestFunctionSpace`. -/
@[ext]
theorem ext {f g : SchwartzTestFunctionSpace n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The coercion of `mk f hf` is just `f`. -/
@[simp]
theorem coe_mk (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf) :
    ⇑(mk f hf : SchwartzTestFunctionSpace n) = f :=
  rfl



end SchwartzTestFunctionSpace

end SchwartzSpace

section UniformConvergenceCLM

variable {n : ℕ}

/-- Each coordinate of a vector in `ℝⁿ` is bounded in absolute value by the Euclidean
norm of the vector. -/
lemma euclideanSpace_norm_coord_le (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    ‖x j‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq x]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ j)

/-- The operator norm of a continuous linear functional `T : ℝⁿ →L[ℝ] ℂ` is bounded
by the sum of its values on the standard basis. -/
lemma opNorm_le_sum_basis_norms (T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) :
    ‖T‖ ≤ ∑ j : Fin n, ‖T (EuclideanSpace.single j 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg (fun j _ => norm_nonneg _))
  intro x

  have hdecomp : x = ∑ j : Fin n, (x j) • EuclideanSpace.single j (1 : ℝ) := by
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
    exact h.symm
  conv_lhs => rw [hdecomp]
  rw [map_sum]
  calc ‖∑ j : Fin n, T ((x j) • EuclideanSpace.single j 1)‖
      ≤ ∑ j : Fin n, ‖T ((x j) • EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, ‖x j‖ * ‖T (EuclideanSpace.single j 1)‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ContinuousLinearMap.map_smul]
        exact norm_smul (x j) _
    _ ≤ ∑ j : Fin n, ‖x‖ * ‖T (EuclideanSpace.single j 1)‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (euclideanSpace_norm_coord_le x j) (norm_nonneg _)
    _ = (∑ j : Fin n, ‖T (EuclideanSpace.single j 1)‖) * ‖x‖ := by
        rw [← Finset.mul_sum]; ring

end UniformConvergenceCLM

end TestFunctions

end
