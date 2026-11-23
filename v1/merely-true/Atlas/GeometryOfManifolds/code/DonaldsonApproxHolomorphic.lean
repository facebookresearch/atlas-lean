/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false

namespace Donaldson

noncomputable section

open Real


/-- Data for a compact Kähler manifold: a metric space $M$, complex dimension $n$, a
non-degenerate antisymmetric 2-form $\omega$, an almost complex structure $J$ with $J^2 = -I$,
the Kähler metric $g(v,w) = \omega(v, J w)$, and an integrality condition on the symplectic
volume (needed for Donaldson's pre-quantization). -/
structure CompactKahlerData where
  M : Type*
  metricInst : MetricSpace M
  compactInst : @CompactSpace M metricInst.toUniformSpace.toTopologicalSpace
  complexDim : ℕ
  dim_pos : 0 < complexDim
  ω : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  ω_antisymm : ∀ p v w, ω p v w = -(ω p w v)
  J : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ)
  J_sq_neg : ∀ p v, J p (J p v) = fun i => -(v i)
  g : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  kahler_compat : ∀ p v w, g p v w = ω p v (J p w)
  symplectic_volume : ℝ
  symplectic_volume_pos : 0 < symplectic_volume
  integrality_condition : ∃ (N : ℕ), 0 < N ∧
    symplectic_volume = (2 * Real.pi) ^ complexDim * ↑N

/-- A family $\{\sigma_{k,p}\}$ of sections indexed by an integer $k$ and a basepoint $p \in M$. -/
structure SectionFamily (X : CompactKahlerData) where
  section_ : ℕ → X.M → X.M → ℂ

/-- Abstraction of the $k$-weighted $C^r$ sup-norm $\sup_x (k^{r/2}|\nabla^r s(x)|)$, with the
basic properties (non-negativity, neg-invariance, and pointwise control for $r=0$). -/
structure WeightedSupNorm (X : CompactKahlerData) where
  eval : ℕ → ℕ → (X.M → ℂ) → ℝ
  nonneg : ∀ k r s, 0 ≤ eval k r s
  neg_le : ∀ k r s, eval k r (fun x => -(s x)) ≤ eval k r s
  pointwise_control : ∀ k s (B : ℝ), 0 ≤ B → (∀ x : X.M, ‖s x‖ ≤ B) → eval k 0 s ≤ B

/-- Abstraction of an $L^2$ norm on sections, with the basic property of non-negativity. -/
structure L2Norm (X : CompactKahlerData) where
  norm : (X.M → ℂ) → ℝ
  nonneg : ∀ s, 0 ≤ norm s

/-- Abstraction of the Dolbeault operator $\bar\partial$ on sections of $L^k$, together with the
pointwise estimate that $|\bar\partial$ applied to the Gaussian peak section$|\leq C/\sqrt k$. -/
structure DelbarOp (X : CompactKahlerData) where
  delbar : (X.M → ℂ) → (X.M → ℂ)
  delbar_gaussian_pointwise_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, ∀ p x : X.M,
      ‖delbar (fun q => (Real.exp (-(↑k : ℝ) *
        (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ)) x‖ ≤
        C / Real.sqrt (↑k)


variable {X : CompactKahlerData}

/-- The family $\{\sigma_{k,p}\}$ is uniformly $C^r$-bounded for every $r$. -/
def IsUniformlyBounded (wdn : WeightedSupNorm X) (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (fam.section_ k p) ≤ C_r

/-- The family is approximately holomorphic: $\|\bar\partial \sigma_{k,p}\|_{C^r} \leq C_r/\sqrt{k}$. -/
def IsApproxHolomorphic (wdn : WeightedSupNorm X) (dol : DelbarOp X)
    (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (dol.delbar (fam.section_ k p)) ≤
      C_r / Real.sqrt (↑k)

/-- The family is uniformly Gaussian-concentrated around $p$:
$|\sigma_{k,p}(x)| \leq C \exp(-\lambda k\, d(p,x)^2)$. -/
def IsUniformlyConcentrated (fam : SectionFamily X) : Prop :=
  ∃ C lam : ℝ, C > 0 ∧ lam > 0 ∧
    ∀ k : ℕ, ∀ p x : X.M, ‖fam.section_ k p x‖ ≤
      C * Real.exp (-lam * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2)

/-- A family is truly holomorphic if $\bar\partial \sigma_{k,p} = 0$ for all $k, p$. -/
def IsHolomorphicFamily (dol : DelbarOp X) (fam : SectionFamily X) : Prop :=
  ∀ k : ℕ, ∀ p : X.M, dol.delbar (fam.section_ k p) = 0

/-- Two families are exponentially close in every $C^r$-norm:
$\|\sigma_{k,p} - \tilde\sigma_{k,p}\|_{C^r} \leq C_r \exp(-\lambda k^{1/3})$. -/
def IsExponentiallyClose (wdn : WeightedSupNorm X)
    (fam fam' : SectionFamily X) : Prop :=
  ∃ lam : ℝ, lam > 0 ∧
    ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ p : X.M,
        wdn.eval k r (fun x => fam.section_ k p x - fam'.section_ k p x) ≤
          C_r * Real.exp (-lam * (↑k) ^ ((1 : ℝ) / 3))


/-- The Gaussian peak section family $\sigma_{k,p}(q) = e^{-k\, d(p,q)^2/4}$ used as a model
for Donaldson's near-holomorphic peak sections. -/
def gaussianPeakSection (X : CompactKahlerData) : SectionFamily X :=
  { section_ := fun k p q =>
      (Real.exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ) }


/-- The Gaussian peak section is pointwise bounded by 1 since $e^{-k d^2/4} \leq 1$. -/
theorem gaussian_pointwise_le_one (X : CompactKahlerData) (k : ℕ) (p x : X.M) :
    ‖(gaussianPeakSection X).section_ k p x‖ ≤ 1 := by
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
  nlinarith [sq_nonneg (@Dist.dist X.M X.metricInst.toDist p x)]


/-- The Gaussian peak section is uniformly concentrated with constants $C = 1$, $\lambda = 1/4$. -/
theorem gaussian_peak_concentrated (X : CompactKahlerData) :
    IsUniformlyConcentrated (gaussianPeakSection X) := by
  refine ⟨(1 : ℝ), (1 : ℝ)/4, by norm_num, by norm_num, ?_⟩
  intro k p x
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

  have heq : -(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4 =
      -(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 := by ring
  linarith [exp_pos (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2),
            show exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4) =
                 exp (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2) from
              congrArg exp heq]


/-- Lower bound on the Gaussian peak section within a $1/\sqrt{k}$-ball:
$|\sigma_{k,p}(q)| \geq e^{-1/4}$ when $d(p,q) \leq 1/\sqrt{k}$. -/
theorem gaussian_peak_lower_bound (X : CompactKahlerData) :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, 1 < k → ∀ p q : X.M,
      @Dist.dist X.M X.metricInst.toDist p q ≤ 1 / Real.sqrt (↑k) →
      c ≤ ‖(gaussianPeakSection X).section_ k p q‖ := by
  refine ⟨Real.exp (-(1:ℝ)/4), exp_pos _, ?_⟩
  intro k hk p q hdist
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr

  have hk' : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hk)
  have hdist_nn : (0 : ℝ) ≤ @Dist.dist X.M X.metricInst.toDist p q :=
    @dist_nonneg X.M X.metricInst.toPseudoMetricSpace p q

  have hd_sq : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 / ↑k := by
    have h2 : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ (1 / Real.sqrt ↑k) ^ 2 :=
      sq_le_sq' (by linarith) hdist
    calc _ ≤ (1 / Real.sqrt ↑k) ^ 2 := h2
      _ = 1 / (Real.sqrt ↑k) ^ 2 := by ring
      _ = 1 / ↑k := by rw [sq_sqrt (le_of_lt hk')]

  have hkd : (↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 :=
    calc (↑k : ℝ) * _ ≤ ↑k * (1 / ↑k) := mul_le_mul_of_nonneg_left hd_sq (le_of_lt hk')
      _ = 1 := by field_simp

  nlinarith
















end

end Donaldson
