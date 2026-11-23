/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Real Set Topology

noncomputable section

namespace CM8


/-- The Euclidean norm on $\mathbb{R}^n$ written as
$\|x\| = \sqrt{\sum_i x_i^2}$. -/
def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The fundamental solution of the Laplacian in $\mathbb{R}^3$:
$\Phi(x) = -\dfrac{1}{4 \pi |x|}$, away from the origin. -/
def Phi3 (x : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * euclidNorm x)

/-- The Laplacian of $f : \mathbb{R}^n \to \mathbb{R}$ at $x$, defined in terms
of Fréchet derivatives applied to coordinate unit vectors:
$\Delta f(x) = \sum_{i = 1}^{n} \partial_i (\partial_i f)(x)$. -/
noncomputable def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)


section HarmonicProofHelpers

open Finset

/-- The squared Euclidean norm $\|y\|^2 = \sum_j y_j^2$ on $\mathbb{R}^3$. -/
private def normSq (y : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, y j ^ 2

/-- The continuous linear map representing the Fréchet derivative of
$y \mapsto \sum_j y_j^2$ at $x$: it acts as $v \mapsto 2 \sum_j x_j v_j$. -/
def normSq_CLM (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) j

/-- If $\|x\| \ne 0$ then $\sum_j x_j^2 > 0$. -/
lemma normSq_pos (x : Fin 3 → ℝ) (hx : euclidNorm x ≠ 0) : 0 < normSq x := by
  unfold normSq euclidNorm at *
  by_contra h; push Not at h
  exact hx (by rw [le_antisymm h (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]; simp)

/-- If $\|x\| \ne 0$ then $\|x\| > 0$. -/
lemma euclidNorm_pos (x : Fin 3 → ℝ) (hx : euclidNorm x ≠ 0) : 0 < euclidNorm x :=
  lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)

/-- The Euclidean norm on $\mathbb{R}^3$ is continuous. -/
lemma continuous_euclidNorm3 : Continuous (euclidNorm : (Fin 3 → ℝ) → ℝ) := by
  unfold euclidNorm
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2)

/-- The complement of the origin (where $\|y\| \ne 0$) is open in $\mathbb{R}^3$. -/
lemma isOpen_euclidNorm_ne : IsOpen {y : Fin 3 → ℝ | euclidNorm y ≠ 0} :=
  continuous_euclidNorm3.isOpen_preimage _ isOpen_ne

/-- The map $y \mapsto \sum_j y_j^2$ has Fréchet derivative `normSq_CLM x` at $x$. -/
lemma hasFDerivAt_normSq (x : Fin 3 → ℝ) :
    HasFDerivAt normSq (normSq_CLM x) x := by
  unfold normSq
  rw [show (fun y : Fin 3 → ℝ => ∑ j : Fin 3, y j ^ 2) =
      ∑ j : Fin 3, (fun y : Fin 3 → ℝ => y j ^ 2) from by ext y; simp [Finset.sum_apply]]
  apply HasFDerivAt.sum; intro j _
  convert (hasFDerivAt_apply (𝕜 := ℝ) (ι := Fin 3) (F' := fun _ => ℝ) j x).pow 2 using 1
  simp [mul_comm]

/-- Evaluation of `normSq_CLM x` on the $i$-th coordinate basis vector gives
$2 x_i$. -/
lemma normSq_CLM_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    normSq_CLM x (Pi.single i 1) = 2 * x i := by
  unfold normSq_CLM
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, Finset.sum_ite_eq']


/-- The scalar function $g(s) = -1 / (4 \pi \sqrt{s})$ has derivative
$g'(s) = 1 / (8 \pi (\sqrt{s})^3)$ for $s > 0$. -/
lemma hasDerivAt_g (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => -1 / (4 * π * Real.sqrt s))
      (1 / (8 * π * (Real.sqrt s) ^ 3)) s := by
  have hsqrt_ne := ne_of_gt (Real.sqrt_pos.mpr hs)
  have h_h : HasDerivAt (fun r => -1 / (4 * π * r))
    ((-1/(4*π)) * (-(Real.sqrt s ^ 2)⁻¹)) (Real.sqrt s) := by
    convert (hasDerivAt_inv hsqrt_ne).const_mul (-1/(4*π)) using 1; ext r; ring
  convert h_h.comp s (Real.hasDerivAt_sqrt (ne_of_gt hs)) using 1
  field_simp; ring


/-- Fréchet derivative of $\Phi_3$ on $\mathbb{R}^3 \setminus \{0\}$, obtained
by the chain rule $\Phi_3(y) = g(\|y\|^2)$. -/
lemma hasFDerivAt_Phi3 (y : Fin 3 → ℝ) (hy : euclidNorm y ≠ 0) :
    HasFDerivAt Phi3
      ((1 / (8 * π * (euclidNorm y) ^ 3)) • normSq_CLM y) y := by
  have h := (hasDerivAt_g (normSq y) (normSq_pos y hy)).comp_hasFDerivAt y (hasFDerivAt_normSq y)
  convert h using 1


/-- The $i$-th partial derivative of $\Phi_3$ at $y$ (with $y \ne 0$) is
$\partial_i \Phi_3(y) = y_i / (4 \pi \|y\|^3)$. -/
lemma fderiv_Phi3_apply (y : Fin 3 → ℝ) (hy : euclidNorm y ≠ 0) (i : Fin 3) :
    fderiv ℝ Phi3 y (Pi.single i 1) = y i / (4 * π * (euclidNorm y) ^ 3) := by
  rw [(hasFDerivAt_Phi3 y hy).fderiv]
  simp [ContinuousLinearMap.smul_apply, normSq_CLM_apply]; ring


/-- $\frac{d}{ds} (\sqrt{s})^3 = \frac{3}{2} \sqrt{s}$ for $s > 0$. -/
lemma hasDerivAt_sqrt_cube (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => (Real.sqrt s) ^ 3) ((3 / 2) * Real.sqrt s) s := by
  convert (Real.hasDerivAt_sqrt (ne_of_gt hs)).pow 3 using 1; simp; field_simp

/-- The derivative of $s \mapsto (4 \pi (\sqrt{s})^3)^{-1}$ at $s > 0$,
computed via the chain and quotient rules. -/
lemma hasDerivAt_inv_4pi_R3 (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => (4 * π * (Real.sqrt s) ^ 3)⁻¹)
      (-(4 * π * ((3 / 2) * Real.sqrt s)) / (4 * π * (Real.sqrt s) ^ 3) ^ 2) s := by
  have hdenom_ne : 4 * π * (Real.sqrt s) ^ 3 ≠ 0 := by positivity
  have h_R3 := hasDerivAt_sqrt_cube s hs
  have h_denom : HasDerivAt (fun s => 4 * π * (Real.sqrt s) ^ 3)
    (4 * π * ((3/2) * Real.sqrt s)) s := h_R3.const_mul _
  exact h_denom.inv hdenom_ne

/-- Fréchet derivative of $y \mapsto (4 \pi \|y\|^3)^{-1}$ on
$\mathbb{R}^3 \setminus \{0\}$, used as a building block for partial derivatives
of $\Phi_3$ itself. -/
lemma hasFDerivAt_h (y : Fin 3 → ℝ) (hy : euclidNorm y ≠ 0) :
    HasFDerivAt (fun y => (4 * π * (euclidNorm y) ^ 3)⁻¹)
      ((-(4 * π * ((3 / 2) * euclidNorm y)) / (4 * π * (euclidNorm y) ^ 3) ^ 2) •
        normSq_CLM y) y := by
  have h := (hasDerivAt_inv_4pi_R3 (normSq y) (normSq_pos y hy)).comp_hasFDerivAt y (hasFDerivAt_normSq y)
  convert h using 1


/-- The map $y \mapsto y_i / (4 \pi \|y\|^3)$ is differentiable at every
$x \in \mathbb{R}^3$ with $\|x\| \ne 0$. -/
lemma differentiableAt_F (x : Fin 3 → ℝ) (hx : euclidNorm x ≠ 0) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x := by
  have h1 : DifferentiableAt ℝ (fun y : Fin 3 → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y => (4 * π * (euclidNorm y) ^ 3)⁻¹) x :=
    (hasFDerivAt_h x hx).differentiableAt
  have : (fun y : Fin 3 → ℝ => y i / (4 * π * (euclidNorm y) ^ 3)) =
    (fun y => y i * (4 * π * (euclidNorm y) ^ 3)⁻¹) := by ext y; ring
  rw [this]; exact h1.mul h2


/-- The sum of squares of the coordinates of $x$ other than the $i$-th:
$\sum_{j \ne i} x_j^2$. Used to reduce a multivariable derivative to a
one-dimensional computation. -/
def restSq (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· ≠ i), x j ^ 2

/-- Updating the $i$-th coordinate of $x$ to $t$ changes the squared Euclidean
norm to $t^2 + \sum_{j \ne i} x_j^2$. -/
lemma euclidNorm_update_sq (x : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    (∑ j : Fin 3, (Function.update x i t j) ^ 2) = t ^ 2 + restSq x i := by
  unfold restSq
  fin_cases i <;> simp [Fin.sum_univ_three, Function.update_apply, Finset.sum_filter] <;> ring

/-- Derivative of the one-variable section
$t \mapsto t / (4 \pi (\sqrt{t^2 + C})^3)$ at a point where $t^2 + C > 0$.
This is the diagonal contribution to $\partial_i \partial_i \Phi_3$. -/
lemma hasDerivAt_phi_2d (t C : ℝ) (hpos : 0 < t ^ 2 + C) :
    HasDerivAt (fun t => t / (4 * π * (√(t ^ 2 + C)) ^ 3))
      ((C - 2 * t ^ 2) / (4 * π * (√(t ^ 2 + C)) ^ 5)) t := by
  have hR_pos : 0 < √(t ^ 2 + C) := Real.sqrt_pos.mpr hpos
  have hR_ne : √(t ^ 2 + C) ≠ 0 := ne_of_gt hR_pos
  have h4piR3_ne : 4 * π * √(t ^ 2 + C) ^ 3 ≠ 0 := by positivity
  have h_num : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have h_sqrt : HasDerivAt (fun t => √(t ^ 2 + C)) (t / √(t ^ 2 + C)) t := by
    have h1 : HasDerivAt (fun t => t ^ 2 + C) (2 * t) t :=
      ((hasDerivAt_pow 2 t).add_const C).congr_deriv (by ring)
    exact (h1.sqrt (ne_of_gt hpos)).congr_deriv (by field_simp)
  have h_cube : HasDerivAt (fun t => (√(t ^ 2 + C)) ^ 3)
      (3 * (√(t ^ 2 + C)) ^ 2 * (t / √(t ^ 2 + C))) t := h_sqrt.pow 3
  have h_denom : HasDerivAt (fun t => 4 * π * (√(t ^ 2 + C)) ^ 3)
      (4 * π * (3 * √(t ^ 2 + C) ^ 2 * (t / √(t ^ 2 + C)))) t := h_cube.const_mul _
  convert h_num.div h_denom h4piR3_ne using 1
  have hR2 : √(t ^ 2 + C) ^ 2 = t ^ 2 + C := Real.sq_sqrt (le_of_lt hpos)
  field_simp; nlinarith [hR2, sq_nonneg t, sq_nonneg (√(t ^ 2 + C))]

end HarmonicProofHelpers


set_option maxHeartbeats 800000 in
/-- The fundamental solution $\Phi_3(x) = -1 / (4 \pi |x|)$ is harmonic on
$\mathbb{R}^3 \setminus \{0\}$: $\Delta \Phi_3(x) = 0$ for all $x$ with
$\|x\| \ne 0$. -/
theorem Phi3_harmonic_away
    (x : Fin 3 → ℝ) (hx : euclidNorm x ≠ 0) :
    laplacian Phi3 x = 0 := by
  unfold laplacian


  have h_eq : ∀ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ Phi3 y (Pi.single i 1)) x =
      fderiv ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x := by
    intro i; apply Filter.EventuallyEq.fderiv_eq
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{y | euclidNorm y ≠ 0}, isOpen_euclidNorm_ne.mem_nhds hx,
       fun y hy => fderiv_Phi3_apply y hy i⟩
  simp_rw [h_eq]


  have h_bridge : ∀ i : Fin 3,
      fderiv ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x (Pi.single i 1) =
      deriv (fun t => (Function.update x i t) i /
        (4 * π * (euclidNorm (Function.update x i t)) ^ 3)) (x i) := by
    intro i
    have hf' : DifferentiableAt ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3))
        (Function.update x i (x i)) := by
      rw [Function.update_eq_self]; exact differentiableAt_F x hx i
    have h_comp := hf'.hasFDerivAt.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
    simp only [Function.comp_def] at h_comp
    rw [h_comp.deriv]; simp [Function.update_eq_self]
  simp_rw [h_bridge]


  have h_1d : ∀ i : Fin 3,
      (fun t => (Function.update x i t) i /
        (4 * π * (euclidNorm (Function.update x i t)) ^ 3)) =
      (fun t => t / (4 * π * (√(t ^ 2 + restSq x i)) ^ 3)) := by
    intro i; ext t; simp only [Function.update_self, euclidNorm, euclidNorm_update_sq]
  simp_rw [h_1d]

  have hR_pos : 0 < euclidNorm x := euclidNorm_pos x hx
  have hR_sq : euclidNorm x ^ 2 = ∑ j : Fin 3, x j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))
  have h_sum_split : ∀ i : Fin 3, x i ^ 2 + restSq x i = ∑ j : Fin 3, x j ^ 2 := by
    intro i; unfold restSq
    rw [← Finset.add_sum_erase Finset.univ (fun j => x j ^ 2) (Finset.mem_univ i)]
    congr 1; apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp [Finset.mem_erase, ne_comm]
  have hpos : ∀ i : Fin 3, 0 < x i ^ 2 + restSq x i := by
    intro i; rw [h_sum_split, ← hR_sq]; exact sq_pos_of_pos hR_pos
  have h_deriv : ∀ i : Fin 3,
      deriv (fun t => t / (4 * π * (√(t ^ 2 + restSq x i)) ^ 3)) (x i) =
      (restSq x i - 2 * (x i) ^ 2) / (4 * π * (√(x i ^ 2 + restSq x i)) ^ 5) :=
    fun i => (hasDerivAt_phi_2d (x i) (restSq x i) (hpos i)).deriv
  simp_rw [h_deriv]

  have h_norm : ∀ i : Fin 3, √(x i ^ 2 + restSq x i) = euclidNorm x := by
    intro i; unfold euclidNorm; congr 1; exact h_sum_split i
  simp_rw [h_norm]


  rw [show (∑ i : Fin 3, (restSq x i - 2 * x i ^ 2) / (4 * π * euclidNorm x ^ 5)) =
      (∑ i : Fin 3, (restSq x i - 2 * x i ^ 2)) / (4 * π * euclidNorm x ^ 5)
    from by rw [Finset.sum_div]]
  rw [div_eq_zero_iff]; left

  unfold restSq
  simp only [Fin.sum_univ_three, Finset.sum_filter]
  simp (config := { decide := true })
  ring

/-- **Definition 2.0.2 (Green function for a domain).** Data of a Green
function for a domain $\Omega \subset \mathbb{R}^3$: a `corrector`
$\phi(x, y)$ which matches the fundamental solution on the boundary, i.e.
$\phi(x, \sigma) = \Phi_3(x - \sigma)$ for $x \in \Omega$ and $\sigma \in
\partial \Omega$. -/
structure GreenFunction (Ω : Set (Fin 3 → ℝ)) where
  corrector : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω,
    corrector x σ = Phi3 (x - σ)

/-- The Green function $G(x, y) = \Phi_3(x - y) - \phi(x, y)$ assembled from a
fundamental solution and its corrector. -/
def GreenFunction.G {Ω : Set (Fin 3 → ℝ)} (gf : GreenFunction Ω)
    (x y : Fin 3 → ℝ) : ℝ :=
  Phi3 (x - y) - gf.corrector x y














/-- **Proposition 2.0.2 (Green decomposition).** Predicate asserting that
$G(x, y) = \Phi(x - y) - \phi(x, y)$ where, for each $x \in \Omega$, the
corrector $\phi(x, \cdot)$ is harmonic in $\Omega$ and equals $\Phi(x - \sigma)$
on $\partial \Omega$. -/
structure IsGreenDecomposition {n : ℕ} (Ω : Set (Fin n → ℝ))
    (Φ : (Fin n → ℝ) → ℝ)
    (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop where
  decomposition : ∀ x y : Fin n → ℝ, G x y = Φ (x - y) - φ x y
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (φ x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, φ x σ = Φ (x - σ)

/-- Linearity of the Laplacian under subtraction: $\Delta(f - g) = \Delta f -
\Delta g$, provided $f, g$ are differentiable on $\mathbb{R}^n$ and each
partial $\partial_i f$, $\partial_i g$ is differentiable at $x$. -/
theorem laplacian_sub {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : ∀ y, DifferentiableAt ℝ f y)
    (hg : ∀ y, DifferentiableAt ℝ g y)
    (hf2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x)
    (hg2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x) :
    laplacian (f - g) x = laplacian f x - laplacian g x := by
  unfold laplacian
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i
  have h_inner : (fun y => fderiv ℝ (f - g) y (Pi.single i 1)) =
      (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) := by
    ext y; rw [fderiv_sub (hf y) (hg y)]; simp [ContinuousLinearMap.sub_apply]
  rw [h_inner]
  have h_sub : fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) x =
      fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x -
      fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x := by
    have : (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) =
        (fun y => fderiv ℝ f y (Pi.single i 1)) - (fun y => fderiv ℝ g y (Pi.single i 1)) := by
      ext y; simp [Pi.sub_apply]
    rw [this]; exact fderiv_sub (hf2 i) (hg2 i)
  rw [h_sub]; simp [ContinuousLinearMap.sub_apply]

end CM8
