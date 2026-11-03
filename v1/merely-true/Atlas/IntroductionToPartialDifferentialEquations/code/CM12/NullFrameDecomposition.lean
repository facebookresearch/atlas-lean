/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 800000

noncomputable section

open Matrix

namespace NullFrame

/-- The Minkowski metric on $\mathbb{R}^{1+n}$ as a matrix:
$m_{\mu \nu} = \operatorname{diag}(-1, 1, 1, \ldots, 1)$. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then (if (i : ℕ) = 0 then -1 else 1) else 0

/-- The Minkowski inner product of two vectors $X, Y \in \mathbb{R}^{1+n}$:
$m(X, Y) = m_{\alpha \beta} X^{\alpha} Y^{\beta}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- The Minkowski inner product is symmetric: $m(X, Y) = m(Y, X)$. -/
theorem minkowskiInner_comm (n : ℕ) (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y = minkowskiInner n Y X := by
  simp only [minkowskiInner, minkowskiMetric, dotProduct, mulVec, of_apply]
  simp [mul_comm]

/-- A null frame for $\mathbb{R}^{1+n}$ (Definition 2.2.1): a basis
$\{L, \underline{L}, e_{(1)}, \ldots, e_{(n-1)}\}$ where $L$ and $\underline{L}$ are null
vectors normalized by $m(L, \underline{L}) = -2$, and the $e_{(i)}$ are
$m$-orthonormal vectors that span the $m$-orthogonal complement of
$\operatorname{span}(L, \underline{L})$. The `completeness` field expresses every vector
$X$ in null-frame components. -/
structure NullFrameData (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

/-- The angular (transverse) part $h(X, Y) = \sum_i m(e_{(i)}, X) \, m(e_{(i)}, Y)$ of
the Minkowski metric appearing in the null frame decomposition. -/
def angularMetric (n : ℕ) (nf : NullFrameData n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y

/-- Null frame decomposition of the Minkowski metric (Proposition 2.2.1, applied form):
$m(X, Y) = -\tfrac{1}{2} m(L, X) m(\underline{L}, Y) - \tfrac{1}{2} m(\underline{L}, X) m(L, Y)
+ h(X, Y)$ for all $X, Y \in \mathbb{R}^{1+n}$. -/
theorem nullFrame_decomposition {n : ℕ} (nf : NullFrameData n)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y =
      -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y
      - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y
      + angularMetric n nf X Y := by
  conv_lhs => rw [nf.completeness X]
  simp only [minkowskiInner, angularMetric]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
  rw [sum_dotProduct (Finset.univ)
    (fun i => (dotProduct (nf.e i) (minkowskiMetric n *ᵥ X)) • nf.e i)]
  simp only [smul_dotProduct, smul_eq_mul]
  ring

/-- The angular metric vanishes when one argument is $L$: $h(L, Y) = 0$. -/
theorem angularMetric_vanish_L {n : ℕ} (nf : NullFrameData n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.L Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.L = 0 := by
    rw [minkowskiInner_comm]; exact nf.L_e_orthog i
  simp [h]

/-- The angular metric vanishes when one argument is $\underline{L}$: $h(\underline{L}, Y) = 0$. -/
theorem angularMetric_vanish_Lb {n : ℕ} (nf : NullFrameData n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.Lb Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.Lb = 0 := by
    rw [minkowskiInner_comm]; exact nf.Lb_e_orthog i
  simp [h]

/-- The angular metric is symmetric: $h(X, Y) = h(Y, X)$. -/
theorem angularMetric_comm {n : ℕ} (nf : NullFrameData n) (X Y : Fin (n + 1) → ℝ) :
    angularMetric n nf X Y = angularMetric n nf Y X := by
  simp only [angularMetric]
  congr 1; ext i; ring

/-- The angular metric vanishes when its right argument is $L$: $h(X, L) = 0$. -/
theorem angularMetric_vanish_L_right {n : ℕ} (nf : NullFrameData n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.L = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_L nf X

/-- The angular metric vanishes when its right argument is $\underline{L}$:
$h(X, \underline{L}) = 0$. -/
theorem angularMetric_vanish_Lb_right {n : ℕ} (nf : NullFrameData n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.Lb = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_Lb nf X

/-- On the orthonormal transverse frame vectors, $h(e_{(i)}, e_{(j)}) = \delta_{ij}$. -/
theorem angularMetric_on_e {n : ℕ} (nf : NullFrameData n) (i j : Fin (n - 1)) :
    angularMetric n nf (nf.e i) (nf.e j) = if i = j then 1 else 0 := by
  simp only [angularMetric, nf.e_orthonormal]
  by_cases h : i = j
  · subst h
    simp [Finset.sum_ite_eq']
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; exact absurd rfl h
    · subst hki; simp [h]
    · simp [hki]
    · simp [hki]

/-- The angular metric is non-negative on the diagonal: $h(X, X) \geq 0$. -/
theorem angularMetric_nonneg {n : ℕ} (nf : NullFrameData n) (X : Fin (n + 1) → ℝ) :
    0 ≤ angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

/-- The angular metric is positive-definite on the $m$-orthogonal complement of
$\operatorname{span}(L, \underline{L})$: if $m(L, X) = m(\underline{L}, X) = 0$
and $X \neq 0$, then $h(X, X) > 0$. -/
theorem angularMetric_pos_def {n : ℕ} (nf : NullFrameData n)
    (X : Fin (n + 1) → ℝ) (hL : minkowskiInner n nf.L X = 0)
    (hLb : minkowskiInner n nf.Lb X = 0) (hX : X ≠ 0) :
    0 < angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · by_contra h_none
    push Not at h_none
    apply hX
    have h_zero : ∀ i : Fin (n - 1), minkowskiInner n (nf.e i) X = 0 := by
      intro i
      have h1 := h_none i (Finset.mem_univ i)
      have h2 := mul_self_nonneg (minkowskiInner n (nf.e i) X)
      exact mul_self_eq_zero.mp (le_antisymm h1 h2)
    have := nf.completeness X
    rw [hLb, hL] at this
    simp only [mul_zero, zero_smul, zero_add] at this
    rw [this]
    simp only [h_zero, zero_smul, Finset.sum_const_zero]

/-- The Minkowski metric squares to the identity: $m \cdot m = I$. -/
theorem minkowskiMetric_sq (n : ℕ) : minkowskiMetric n * minkowskiMetric n = 1 := by
  ext i j
  simp only [minkowskiMetric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij; by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · by_cases hj : (j : ℕ) = 0 <;> simp [hij, hj]

/-- The Minkowski metric is its own inverse: $m^{-1} = m$. -/
theorem minkowskiMetric_inv (n : ℕ) : (minkowskiMetric n)⁻¹ = minkowskiMetric n :=
  inv_eq_left_inv (minkowskiMetric_sq n)

/-- Multiplying the right argument by $m$ converts the Minkowski inner product into the
Euclidean dot product: $m(V, m \cdot W) = V \cdot W$. -/
theorem minkowskiInner_eta_cancel (n : ℕ) (V W : Fin (n + 1) → ℝ) :
    minkowskiInner n V (minkowskiMetric n *ᵥ W) = dotProduct V W := by
  simp only [minkowskiInner, mulVec_mulVec, minkowskiMetric_sq, one_mulVec]

/-- Null frame decomposition of the inverse Minkowski metric (Proposition 2.2.1,
raised-index form):
$(m^{-1})^{\mu \nu} = -\tfrac{1}{2} L^{\mu} \underline{L}^{\nu}
- \tfrac{1}{2} \underline{L}^{\mu} L^{\nu} + \sum_i e_{(i)}^{\mu} e_{(i)}^{\nu}$. -/
theorem nullFrame_inverse_decomposition {n : ℕ} (nf : NullFrameData n)
    (μ ν : Fin (n + 1)) :
    (minkowskiMetric n)⁻¹ μ ν =
      -(1 / 2) * nf.L μ * nf.Lb ν
      - (1 / 2) * nf.Lb μ * nf.L ν
      + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν := by

  rw [minkowskiMetric_inv]

  have h_entry : minkowskiMetric n μ ν = (minkowskiMetric n *ᵥ Pi.single ν 1) μ := by
    simp [mulVec, dotProduct, minkowskiMetric, Matrix.of_apply, Pi.single_apply]
  rw [h_entry]

  have h_comp := nf.completeness (minkowskiMetric n *ᵥ Pi.single ν 1)

  have h_μ := congr_fun h_comp μ
  rw [h_μ]

  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    minkowskiInner_eta_cancel,
    dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  congr 1
  · ring
  · congr 1; ext i; ring

/-- Combined statement of Proposition 2.2.1 (null frame decomposition of $m$): the
applied-form decomposition of $m$, positive-definiteness of $h$ on the transverse plane,
vanishing of $h$ on $L$ and $\underline{L}$, and the raised-index decomposition of
$m^{-1}$. -/
theorem nullFrame_decomposition_full {n : ℕ} (nf : NullFrameData n) :
    (∀ X Y : Fin (n + 1) → ℝ,
      minkowskiInner n X Y =
        -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y
        - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y
        + angularMetric n nf X Y) ∧
    (∀ (X : Fin (n + 1) → ℝ), minkowskiInner n nf.L X = 0 →
      minkowskiInner n nf.Lb X = 0 → X ≠ 0 → 0 < angularMetric n nf X X) ∧
    (∀ Y : Fin (n + 1) → ℝ, angularMetric n nf nf.L Y = 0) ∧
    (∀ Y : Fin (n + 1) → ℝ, angularMetric n nf nf.Lb Y = 0) ∧
    (∀ μ ν : Fin (n + 1),
      (minkowskiMetric n)⁻¹ μ ν =
        -(1 / 2) * nf.L μ * nf.Lb ν
        - (1 / 2) * nf.Lb μ * nf.L ν
        + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν) :=
  ⟨nullFrame_decomposition nf,
   angularMetric_pos_def nf,
   angularMetric_vanish_L nf,
   angularMetric_vanish_Lb nf,
   nullFrame_inverse_decomposition nf⟩

end NullFrame
