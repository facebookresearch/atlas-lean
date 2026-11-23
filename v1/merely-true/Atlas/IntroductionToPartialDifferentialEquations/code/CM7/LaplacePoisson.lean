/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville

open Real Set MeasureTheory Filter

noncomputable section

namespace LaplacePoisson

/-- A bounded Lipschitz domain in $\mathbb{R}^n$: an open, bounded, nonempty,
connected set whose boundary can be locally straightened by bi-Lipschitz maps.
This is the natural class of domains for the Poisson Dirichlet problem. -/
structure IsLipschitzDomain {n : ℕ} (Ω : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  nonempty : Set.Nonempty Ω
  isConnected : IsConnected Ω
  frontier_nonempty : Set.Nonempty (frontier Ω)
  lipschitz_boundary : ∀ x ∈ frontier Ω, ∃ (U : Set (Fin n → ℝ)),
    IsOpen U ∧ x ∈ U ∧
    ∃ (φ : (Fin n → ℝ) → (Fin n → ℝ)),
      LipschitzWith 1 φ ∧
      ∃ (ψ : (Fin n → ℝ) → (Fin n → ℝ)),
        LipschitzWith 1 ψ ∧
        (∀ y ∈ U, ψ (φ y) = y) ∧ (∀ z ∈ φ '' U, φ (ψ z) = z)

/-- Euclidean norm on $\mathbb{R}^n$ written as $|x| = \sqrt{\sum_i (x^i)^2}$,
for vectors represented as `Fin n → ℝ` (the `LP` suffix marks the L^p-style
function space presentation). -/
def euclidNormLP {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean norm is invariant under negation: $|-x| = |x|$. -/
lemma euclidNormLP_neg {n : ℕ} (x : Fin n → ℝ) : euclidNormLP (-x) = euclidNormLP x := by
  unfold euclidNormLP
  congr 1; congr 1; ext i; simp

/-- The custom `euclidNormLP` agrees with the Mathlib L^2 norm on `Fin n → ℝ`
via the `WithLp 2` equivalence. -/
lemma euclidNormLP_eq_norm_withLp {n : ℕ} (v : Fin n → ℝ) :
    euclidNormLP v = ‖(WithLp.equiv 2 (Fin n → ℝ)).symm v‖ := by
  unfold euclidNormLP
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.equiv_symm_apply_ofLp]
  simp [sq_abs]

/-- The Euclidean norm is nonnegative: $|x| \ge 0$. -/
lemma euclidNormLP_nonneg {n : ℕ} (x : Fin n → ℝ) : euclidNormLP x ≥ 0 := by
  unfold euclidNormLP
  exact Real.sqrt_nonneg _

/-- Reverse triangle inequality for the Euclidean norm: $|a| - |b| \le |a - b|$. -/
lemma euclidNormLP_sub_le {n : ℕ} (a b : Fin n → ℝ) :
    euclidNormLP a - euclidNormLP b ≤ euclidNormLP (a - b) := by
  rw [euclidNormLP_eq_norm_withLp a, euclidNormLP_eq_norm_withLp b,
      euclidNormLP_eq_norm_withLp (a - b)]
  have h : (WithLp.equiv 2 (Fin n → ℝ)).symm (a - b) =
      (WithLp.equiv 2 (Fin n → ℝ)).symm a - (WithLp.equiv 2 (Fin n → ℝ)).symm b := by
    ext i
    simp
  rw [h]
  exact norm_sub_norm_le _ _

/-- Surface area $\omega_n$ of the unit sphere in $\mathbb{R}^n$,
defined via the Gamma function: $\omega_n = 2\pi^{n/2}/\Gamma(n/2)$ for $n \ge 1$.
For example $\omega_3 = 4\pi$. The convention $\omega_0 = 1$ is taken here. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The unit sphere area $\omega_n$ is strictly positive for every $n$. -/
theorem unitSphereArea_pos : ∀ n, unitSphereArea n > 0 := by
  intro n
  unfold unitSphereArea
  split
  · norm_num
  · rename_i hn
    apply div_pos
    · apply mul_pos (by norm_num : (2:ℝ) > 0)
      exact Real.rpow_pos_of_pos Real.pi_pos ((n : ℝ) / 2)
    · apply Real.Gamma_pos_of_pos
      apply div_pos
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      · norm_num

/-- Classical formula: the area of the unit $2$-sphere in $\mathbb{R}^3$
is $\omega_3 = 4\pi$. -/
theorem unitSphereArea_three : unitSphereArea 3 = 4 * Real.pi := by
  unfold unitSphereArea; simp
  have hG32 : Real.Gamma (3 / 2 : ℝ) = (1 / 2) * Real.Gamma (1 / 2) := by
    have h := Real.Gamma_add_one (s := (1:ℝ)/2) (by norm_num)
    linarith
  have hG12 : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hsqrt : Real.sqrt Real.pi = Real.pi ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow Real.pi
  have hpow : Real.pi ^ ((3:ℝ)/2) = Real.pi * Real.pi ^ ((1:ℝ)/2) := by
    rw [show (3:ℝ)/2 = 1 + 1/2 from by ring]
    rw [Real.rpow_add Real.pi_pos]
    rw [Real.rpow_one]
  rw [hG32, hG12, hsqrt, hpow]
  have hpi12_ne : Real.pi ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  field_simp
  ring

/-- The fundamental solution $\Phi$ for the Laplacian $\Delta$ in $\mathbb{R}^n$
(Definition 1.0.1 of CM7):
$\Phi(x) = \frac{1}{2\pi} \ln|x|$ for $n=2$, and
$\Phi(x) = -\frac{1}{\omega_n |x|^{n-2}}$ for $n \ge 3$,
where $\omega_n$ is the surface area of the unit sphere in $\mathbb{R}^n$. -/
def fundamentalSolution (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNormLP x)
  else
    -1 / (unitSphereArea n * (euclidNormLP x) ^ (n - 2))

/-- The fundamental solution is radially symmetric: $\Phi(-x) = \Phi(x)$. -/
lemma fundamentalSolution_neg {n : ℕ} (x : Fin n → ℝ) :
    fundamentalSolution n (-x) = fundamentalSolution n x := by
  unfold fundamentalSolution
  rw [euclidNormLP_neg]

/-- The Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$ on $\mathbb{R}^n$,
expressed in terms of `fderiv` applied twice in coordinate directions. -/
def laplacianLP {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- A function $u$ is harmonic on $\Omega$ when $\Delta u = 0$ pointwise on $\Omega$. -/
def IsHarmonicLP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, laplacianLP u x = 0

/-- Convolution of the fundamental solution with $f$:
$(\Phi * f)(x) = \int_{\mathbb{R}^n} \Phi(x - y)\,f(y)\,d^n y$.
This is the candidate solution of $\Delta u = f$ in Theorem 1.1 of CM7. -/
def phiConvolutionLP (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, fundamentalSolution n (x - y) * f y












/-- The Fréchet derivative of $y \mapsto \sum_j y_j^2$ at $x$ is the linear
functional $v \mapsto \sum_j 2 x_j \, v_j$. -/
lemma hasFDerivAt_sum_sq {n : ℕ} (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => ∑ j : Fin n, y j ^ 2)
      (∑ j : Fin n, (2 * x j) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j))
      x := by
  have hfderiv : ∀ j ∈ Finset.univ, HasFDerivAt (fun y : Fin n → ℝ => y j ^ 2)
      ((2 * x j) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
    intro j _
    convert (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.pow 2 using 1
    ext v; simp [mul_comm, smul_eq_mul]
  convert HasFDerivAt.sum hfderiv using 1; ext y; simp [Finset.sum_apply]

/-- If $x \ne 0$ in $\mathbb{R}^n$ then $\sum_j x_j^2 > 0$. -/
lemma sum_sq_pos_of_ne_zero {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∑ j : Fin n, x j ^ 2 > 0 := by
  have : ∃ i, x i ≠ 0 := by by_contra h; push Not at h; exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2
      ≥ x i ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

/-- Away from the origin the Euclidean norm is differentiable; its Fréchet
derivative is computed via the chain rule from $|x| = \sqrt{\sum_j x_j^2}$. -/
lemma hasFDerivAt_euclidNormLP {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasFDerivAt (euclidNormLP (n := n))
      ((1 / (2 * euclidNormLP x)) •
        (∑ j : Fin n, (2 * x j) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)))
      x := by
  unfold euclidNormLP
  exact (hasFDerivAt_sum_sq x).sqrt (ne_of_gt (sum_sq_pos_of_ne_zero x hx))

/-- The Euclidean norm is strictly positive at nonzero points: $x \ne 0 \Rightarrow |x| > 0$. -/
theorem euclidNormLP_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : euclidNormLP x > 0 := by
  unfold euclidNormLP
  apply Real.sqrt_pos_of_pos
  have : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2 ≥ x i ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

/-- Near a nonzero point $x$, the $i$-th partial derivative of a radial
function $g(|z|)$ equals $g'(|y|)\,(y_i/|y|)$ by the chain rule. -/
lemma first_partial_eq_near {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) =ᶠ[nhds x]
    (fun y => fderiv ℝ g (euclidNormLP y) 1 * (y i / euclidNormLP y)) := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨{y | y ≠ 0}, isOpen_ne.mem_nhds hx, fun y hy => ?_⟩
  have hr_pos : euclidNormLP y > 0 := euclidNormLP_pos y hy
  have hg_diff : DifferentiableAt ℝ g (euclidNormLP y) :=
    (hg.differentiableOn two_ne_zero).differentiableAt (Ioi_mem_nhds hr_pos)
  have hchain := hg_diff.hasFDerivAt.comp y (hasFDerivAt_euclidNormLP y hy)
  show fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1) = _
  change fderiv ℝ (g ∘ euclidNormLP) y (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  have harg : 1 / (2 * euclidNormLP y) * ∑ x : Fin n, 2 * y x * (if x = i then (1 : ℝ) else 0)
      = y i / euclidNormLP y := by
    simp [Finset.sum_ite_eq', Finset.mem_univ]; field_simp
  rw [harg]
  have : (fderiv ℝ g (euclidNormLP y)) (y i / euclidNormLP y) =
      (y i / euclidNormLP y) * (fderiv ℝ g (euclidNormLP y)) 1 := by
    conv_lhs => rw [show y i / euclidNormLP y = (y i / euclidNormLP y) • (1 : ℝ) from by simp]
    rw [map_smul, smul_eq_mul]
  rw [this, mul_comm]

/-- Away from the origin, the function $y \mapsto y_i / |y|$ is differentiable. -/
lemma differentiableAt_coord_over_norm {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    DifferentiableAt ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x := by
  have : (fun y : Fin n → ℝ => y i / euclidNormLP y) = (fun y => y i * (euclidNormLP y)⁻¹) := by
    ext y; rw [div_eq_mul_inv]
  rw [this]
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt).mul
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt.inv (ne_of_gt (euclidNormLP_pos x hx)))

/-- The partial derivative of $y \mapsto y_i/|y|$ in the direction $e_i$ is
$\partial_i (y_i/|y|) = 1/|y| - y_i^2 / |y|^3$ at points $x \ne 0$. -/
lemma fderiv_coord_over_norm_single {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x (Pi.single i 1) =
    1 / euclidNormLP x - x i ^ 2 / euclidNormLP x ^ 3 := by
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  have heq : (fun y : Fin n → ℝ => y i / euclidNormLP y) =
      (fun y => y i * (euclidNormLP y)⁻¹) := by ext y; rw [div_eq_mul_inv]
  rw [heq]
  have h1 : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x :=
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt).inv hr_ne
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y i) x (Pi.single i 1) = 1 := by
    have : (fun y : Fin n → ℝ => y i) =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := rfl
    rw [this, ContinuousLinearMap.fderiv]; simp
  rw [hproj]
  rw [show fderiv ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x =
      fderiv ℝ (Inv.inv ∘ euclidNormLP) x from rfl,
    ((hasFDerivAt_inv' (𝕜 := ℝ) hr_ne).comp x (hasFDerivAt_euclidNormLP x hx)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  field_simp
  ring

/-- Away from the origin, $y \mapsto g'(|y|)$ is differentiable for $g \in C^2$
on $(0, \infty)$. -/
lemma differentiableAt_gprime_comp_norm {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x := by
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ (fun s => fderiv ℝ g s 1) (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  exact (hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))).comp x
    (hasFDerivAt_euclidNormLP x hx).differentiableAt

/-- Chain rule for $\partial_i [g'(|y|)] = g''(|y|) \, (y_i / |y|)$ at $x \ne 0$. -/
lemma fderiv_gprime_comp_norm_single {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x (Pi.single i 1) =
    fderiv ℝ (fun s => fderiv ℝ g s 1) (euclidNormLP x) 1 * (x i / euclidNormLP x) := by
  set phi := (fun s : ℝ => fderiv ℝ g s 1) with hphi_def
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ phi (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  have hphi_diffAt : DifferentiableAt ℝ phi (euclidNormLP x) :=
    hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))
  have hchain := hphi_diffAt.hasFDerivAt.comp x (hasFDerivAt_euclidNormLP x hx)
  show fderiv ℝ (fun y => phi (euclidNormLP y)) x (Pi.single i 1) = _
  change fderiv ℝ (phi ∘ euclidNormLP) x (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  field_simp

/-- Second partial derivative of a radial function:
$\partial_i^2 [g(|x|)] = g''(|x|) (x_i/|x|)^2 + g'(|x|)(1/|x| - x_i^2/|x|^3)$
at points $x \ne 0$. -/
theorem axm_second_partial_comp_norm {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    let r := euclidNormLP x
    fderiv ℝ (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) x (Pi.single i 1) =
      fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 * (x i / r) ^ 2 +
      fderiv ℝ g r 1 * (1 / r - x i ^ 2 / r ^ 3) := by
  intro r

  rw [(first_partial_eq_near g hg x hx i).fderiv_eq]

  rw [fderiv_fun_mul (differentiableAt_gprime_comp_norm g hg x hx)
    (differentiableAt_coord_over_norm x hx i)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

  rw [fderiv_gprime_comp_norm_single g hg x hx i,
      fderiv_coord_over_norm_single x hx i]

  ring

/-- The Euclidean norm $x \mapsto |x|$ is continuous on $\mathbb{R}^n$. -/
lemma continuous_euclidNormLP {n : ℕ} : Continuous (fun x : Fin n → ℝ => euclidNormLP x) := by
  unfold euclidNormLP
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)

/-- The squared components of the unit vector $x/|x|$ sum to $1$:
$\sum_i (x_i/|x|)^2 = 1$ for $x \ne 0$. -/
lemma norm_sum_div_sq {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∑ i : Fin n, (x i / euclidNormLP x) ^ 2 = 1 := by
  have hr := euclidNormLP_pos x hx
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt hr
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have : ∑ i : Fin n, x i ^ 2 = (euclidNormLP x) ^ 2 := by
    unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [this, div_self (pow_ne_zero 2 hr_ne)]

/-- Radial form of the Laplacian: for a radial function $u(x) = g(|x|)$ in
$\mathbb{R}^n$ with $n \ge 2$ and $x \ne 0$,
$\Delta u(x) = g''(r) + \frac{n-1}{r} g'(r)$ where $r = |x|$. -/
theorem spherical_laplacian_identity {n : ℕ} (hn : n ≥ 2)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    let r := euclidNormLP x
    laplacianLP (fun y => g (euclidNormLP y)) x =
      fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 + (↑(n - 1) / r) * fderiv ℝ g r 1 := by
  simp only
  set r := euclidNormLP x with hr_def
  have hr := euclidNormLP_pos x hx
  have hr_ne : r ≠ 0 := ne_of_gt hr

  unfold laplacianLP

  simp_rw [axm_second_partial_comp_norm g hg x hx]

  rw [Finset.sum_add_distrib]

  rw [← Finset.mul_sum, norm_sum_div_sq x hx, mul_one]

  rw [← Finset.mul_sum]

  suffices h : ∑ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = ↑(n - 1) / r by
    rw [h]; ring

  have h1 : ∀ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = (r ^ 2 - x i ^ 2) / r ^ 3 := by
    intro i; field_simp
  simp_rw [h1]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

  have hr2 : ∑ i : Fin n, x i ^ 2 = r ^ 2 := by
    rw [hr_def]; unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [hr2]

  have h_cast : (↑(n - 1) : ℝ) = ↑n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_cast
  rw [h_cast]
  field_simp

/-- For $n \ge 3$, the radial profile $r \mapsto -1/(\omega_n r^{n-2})$ of the
fundamental solution is $C^2$ on $(0, \infty)$. -/
theorem radial_fundamental_smooth (n : ℕ) (_hn : n ≥ 3) :
    ContDiffOn ℝ 2 (fun r : ℝ => -1 / (unitSphereArea n * r ^ (n - 2))) (Set.Ioi 0) := by
  set k := n - 2
  set ω := unitSphereArea n
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hfun_eq : (fun r : ℝ => -1 / (ω * r ^ k)) = (fun r => (-1 / ω) * (r ^ k)⁻¹) := by
    funext r; field_simp
  rw [hfun_eq]
  exact (ContDiffOn.inv (contDiff_id.pow k).contDiffOn
    (fun x hx => pow_ne_zero k (ne_of_gt hx))).const_smul (-1 / ω)

/-- First derivative of the radial profile of $\Phi$ for $n \ge 3$:
$\frac{d}{dr}\!\left(-\frac{1}{\omega_n r^{n-2}}\right) = \frac{n-2}{\omega_n r^{n-1}}$. -/
theorem power_radial_first_deriv (n : ℕ) (hn : n ≥ 3) (r : ℝ) (hr : r > 0) :
    fderiv ℝ (fun s : ℝ => -1 / (unitSphereArea n * s ^ (n - 2))) r 1 =
      (↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1)) := by
  rw [fderiv_apply_one_eq_deriv]
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) r (Or.inl hr_ne)).const_mul (-1/ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring, zpow_neg,
      show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast, hk1]
  field_simp

/-- Second derivative of the radial profile of $\Phi$ for $n \ge 3$:
$\frac{d^2}{dr^2}\!\left(-\frac{1}{\omega_n r^{n-2}}\right) =
-\frac{(n-2)(n-1)}{\omega_n r^n}$. -/
theorem power_radial_second_deriv (n : ℕ) (hn : n ≥ 3) (r : ℝ) (hr : r > 0) :
    fderiv ℝ (fun s => fderiv ℝ (fun t : ℝ => -1 / (unitSphereArea n * t ^ (n - 2))) s 1) r 1 =
      -(↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * r ^ n) := by
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hk2 : k + 2 = n := by omega
  have heq : (fun s => fderiv ℝ (fun t : ℝ => -1 / (ω * t ^ k)) s 1) =
    (fun s => deriv (fun t : ℝ => -1 / (ω * t ^ k)) s) := by
    ext s; exact fderiv_apply_one_eq_deriv
  rw [heq, fderiv_apply_one_eq_deriv]
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  have hderiv_eq : ∀ᶠ s in nhds r, deriv (fun t : ℝ => -1 / (ω * t ^ k)) s =
      (↑k / ω) * s ^ (-((k : ℤ) + 1)) := by
    filter_upwards [eventually_gt_nhds (by linarith : (0 : ℝ) < r)] with s hs
    rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) s (Or.inl (ne_of_gt hs))).const_mul (-1/ω) |>.deriv]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring]
    field_simp
  rw [Filter.EventuallyEq.deriv_eq hderiv_eq,
      (hasDerivAt_zpow (-((k : ℤ) + 1)) r (Or.inl hr_ne)).const_mul (↑k / ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [show -((k : ℤ) + 1) - 1 = -(((k : ℤ) + 1) + 1) from by ring, zpow_neg,
      show ((k : ℤ) + 1) + 1 = ((k + 2 : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast, hk2]
  have : (k : ℝ) + 1 = ↑(n - 1) := by rw [← hk1]; push_cast; ring
  rw [this]; field_simp

/-- Lemma 1.0.1 of CM7: the fundamental solution is harmonic away from the
origin. That is, $\Delta \Phi(x) = 0$ for $x \ne 0$ (here $n \ge 3$). -/
theorem fundamental_solution_harmonic_away {n : ℕ} (hn : n ≥ 3)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    laplacianLP (fundamentalSolution n) x = 0 := by

  have hn2 : n ≠ 2 := by omega
  let g : ℝ → ℝ := fun s => -1 / (unitSphereArea n * s ^ (n - 2))
  have hfg : fundamentalSolution n = fun y => g (euclidNormLP y) := by
    ext y; simp only [fundamentalSolution, hn2, ite_false, g]
  rw [hfg]

  have hn2' : n ≥ 2 := by omega
  have hg_smooth := radial_fundamental_smooth n hn
  rw [spherical_laplacian_identity hn2' g hg_smooth x hx]

  have hr := euclidNormLP_pos x hx
  rw [power_radial_second_deriv n hn (euclidNormLP x) hr,
      power_radial_first_deriv n hn (euclidNormLP x) hr]

  set r := euclidNormLP x
  have h1 : r * r ^ (n - 1) = r ^ n := by
    calc r * r ^ (n - 1) = r ^ 1 * r ^ (n - 1) := by ring
      _ = r ^ (1 + (n - 1)) := by rw [pow_add]
      _ = r ^ n := by congr 1; omega
  have key : (↑(n - 1) : ℝ) / r * ((↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1))) =
    (↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * (r * r ^ (n - 1))) := by ring
  rw [key, h1]
  ring



/-- Substitution $y \mapsto x - y$ in the convolution integral:
$\int \Phi(x - y) f(y)\,dy = \int \Phi(y) f(x - y)\,dy$. -/
theorem convolution_substitution {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∫ y, fundamentalSolution n (x - y) * f y) =
      ∫ y, fundamentalSolution n y * f (x - y) := by
  have key : ∀ y : Fin n → ℝ,
    fundamentalSolution n (x - y) * f y =
    (fun z => fundamentalSolution n z * f (x - z)) (x - y) := by
    intro y; simp [sub_sub_cancel]
  simp_rw [key]
  exact MeasureTheory.integral_sub_left_eq_self
    (fun z : Fin n → ℝ => fundamentalSolution n z * f (x - z))
    (volume : Measure (Fin n → ℝ)) x

/-- Chain rule for $z \mapsto g(x - z)$: its derivative at $z'$ is the negative
of the derivative of $g$ at $x - z'$. -/
lemma fderiv_comp_const_sub_LP {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x z' : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g (x - z')) :
    fderiv ℝ (fun z => g (x - z)) z' = -(fderiv ℝ g (x - z')) := by
  rw [show (fun z => g (x - z)) = g ∘ (fun z => x - z) from rfl,
      fderiv_comp z' hg ((differentiableAt_const x).sub differentiableAt_id)]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  have : fderiv ℝ (fun z : Fin n → ℝ => x - z) z' = -ContinuousLinearMap.id ℝ _ := by
    rw [fderiv_const_sub x]; simp
  rw [this]; simp

/-- Variable swap for the Laplacian under translation: the Laplacian of
$x' \mapsto f(x' - y)$ at $x$ equals the Laplacian of $z \mapsto f(x - z)$ at $y$,
since each equals $\Delta f(x - y)$. -/
theorem laplacianLP_chain_rule_sub {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (_hf : ContDiff ℝ ⊤ f)
    (x y : Fin n → ℝ) :
    laplacianLP (fun x' => f (x' - y)) x = laplacianLP (fun z => f (x - z)) y := by


  suffices h_lhs : laplacianLP (fun x' => f (x' - y)) x = laplacianLP f (x - y) by
    suffices h_rhs : laplacianLP (fun z => f (x - z)) y = laplacianLP f (x - y) by
      rw [h_lhs, h_rhs]

    unfold laplacianLP
    congr 1; ext i
    have hf_diff : ∀ z', DifferentiableAt ℝ f (x - z') :=
      fun z' => (_hf.differentiable WithTop.top_ne_zero).differentiableAt
    have h_func_eq : (fun z' => fderiv ℝ (fun z => f (x - z)) z' (Pi.single i 1))
      = (fun z' => -(fderiv ℝ f (x - z') (Pi.single i 1))) := by
      ext z'; rw [fderiv_comp_const_sub_LP f x z' (hf_diff z')]; simp
    rw [h_func_eq, fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply]
    have hg_diff : DifferentiableAt ℝ (fun w => fderiv ℝ f w (Pi.single i 1)) (x - y) := by
      rw [show (fun w => fderiv ℝ f w (Pi.single i 1)) =
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) ∘ (fderiv ℝ f) from rfl]
      exact DifferentiableAt.comp _
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).differentiableAt
        ((_hf.fderiv_right le_top).differentiable WithTop.top_ne_zero |>.differentiableAt)
    rw [fderiv_comp_const_sub_LP (fun w => fderiv ℝ f w (Pi.single i 1)) x y hg_diff]
    simp

  unfold laplacianLP
  congr 1; ext i
  rw [show (fun z => fderiv ℝ (fun x' => f (x' - y)) z (Pi.single i 1))
    = (fun z => fderiv ℝ f (z - y) (Pi.single i 1)) from by ext z; rw [fderiv_comp_sub y]]
  rw [show (fun z => fderiv ℝ f (z - y) (Pi.single i 1))
    = (fun z => (fun w => fderiv ℝ f w (Pi.single i 1)) (z - y)) from rfl]
  exact @fderiv_comp_sub ℝ _ (Fin n → ℝ) _ _ ℝ _ _
    (fun w => fderiv ℝ f w (Pi.single i 1)) x y ▸ rfl


/-- The Laplacian of a smooth, compactly supported function is uniformly bounded. -/
theorem laplacianLP_bounded_of_smooth_compactSupport {n : ℕ}
    (g : (Fin n → ℝ) → ℝ)
    (_hg_smooth : ContDiff ℝ ⊤ g) (_hg_supp : HasCompactSupport g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Fin n → ℝ, |laplacianLP g y| ≤ M := by

  have h_summand_supp : ∀ i : Fin n,
      HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    exact (_hg_supp.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

  have h_summand_cont : ∀ i : Fin n,
      Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    have h_inner_smooth : ContDiff ℝ ⊤ (fun y => fderiv ℝ g y (Pi.single i 1)) :=
      (_hg_smooth.fderiv_right le_top).clm_apply contDiff_const
    exact (h_inner_smooth.continuous_fderiv (by simp)).clm_apply continuous_const

  have h_summand_bound : ∀ i : Fin n, ∃ C : ℝ, ∀ x, ‖(fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1))‖ ≤ C := by
    intro i
    exact (h_summand_supp i).exists_bound_of_continuous (h_summand_cont i)

  choose Cs hCs using h_summand_bound

  refine ⟨∑ i : Fin n, |Cs i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun y => ?_⟩
  unfold laplacianLP
  calc |∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)|
      ≤ ∑ i : Fin n, |fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, |Cs i| := by
        apply Finset.sum_le_sum
        intro i _
        have := hCs i y
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self _)





















/-- The sup-norm on $\mathbb{R}^n$ is dominated by the Euclidean L² norm:
$\|\sigma\|_\infty \le \|\sigma\|_2$. -/
lemma norm_le_euclidNormLP {n : ℕ} (σ : Fin n → ℝ) : ‖σ‖ ≤ euclidNormLP σ := by
  unfold euclidNormLP
  have h_comp : ∀ i : Fin n, |σ i| ≤ Real.sqrt (∑ j, σ j ^ 2) := by
    intro i
    have h1 : σ i ^ 2 ≤ ∑ j, σ j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (σ j)) (Finset.mem_univ i)
    calc |σ i| = Real.sqrt (σ i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (∑ j, σ j ^ 2) := Real.sqrt_le_sqrt h1
  exact pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr h_comp

/-- Continuity at $x$ implies that the oscillation
$\sup_{|\sigma|=\varepsilon} |f(x-\sigma) - f(x)|$ tends to $0$ as $\varepsilon \to 0^+$. -/
theorem oscillation_origin_sphere_tendsto_zero {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun ε => ⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}, |f (x - σ) - f x|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hcont := hf.continuousAt (x := x)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη⟩ := hcont (δ / 2) hδ2
  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
    exact hε_dist
  have hfrontier_sub : frontier {z : Fin n → ℝ | euclidNormLP z = ε} ⊆
      {z | euclidNormLP z = ε} := by
    have hclosed : IsClosed {z : Fin n → ℝ | euclidNormLP z = ε} :=
      IsClosed.preimage
        (Continuous.sqrt (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)))
        isClosed_singleton
    exact frontier_subset_closure.trans hclosed.closure_eq.subset
  have hbound : ∀ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x| ≤ δ / 2 := by
    intro σ hσ_frontier
    have hσ_norm : euclidNormLP σ = ε := hfrontier_sub hσ_frontier
    have h_dist : dist (x - σ) x < η := by
      calc dist (x - σ) x = ‖(x - σ) - x‖ := dist_eq_norm _ _
        _ = ‖-σ‖ := by ring_nf
        _ = ‖σ‖ := norm_neg σ
        _ ≤ euclidNormLP σ := norm_le_euclidNormLP σ
        _ = ε := hσ_norm
        _ < η := hε_lt_η
    have h_f_dist := hη h_dist
    rw [Real.dist_eq] at h_f_dist
    exact h_f_dist.le
  have h_bisup_le : (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x|) ≤ δ / 2 := by
    apply ciSup_le
    intro σ
    by_cases hσ : σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}
    · haveI : Nonempty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) := ⟨hσ⟩
      exact ciSup_le (fun _ => hbound σ hσ)
    · haveI : IsEmpty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) :=
        isEmpty_Prop.mpr hσ
      rw [Real.iSup_of_isEmpty]
      exact hδ2.le
  have h_bisup_nn : 0 ≤ (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x|) := by
    apply Real.sSup_nonneg
    intro y hy
    obtain ⟨σ, rfl⟩ := mem_range.mp hy
    apply Real.sSup_nonneg
    intro z hz
    obtain ⟨_, rfl⟩ := mem_range.mp hz
    exact abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_bisup_nn]
  linarith










/-- Decomposition of an integral on $\mathbb{R}^n$ as a sum of an integral over the
open ball $\{|y|<\varepsilon\}$ and over its complement $\{|y|\ge\varepsilon\}$. -/
theorem integral_split_ball_complement {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (ε : ℝ) (_hε : ε > 0)
    (hg : Integrable g) :
    ∫ y, g y = (∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, g y) +
      (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε}, g y) := by
  have hms : MeasurableSet {z : Fin n → ℝ | euclidNormLP z < ε} :=
    (isOpen_lt continuous_euclidNormLP continuous_const).measurableSet
  have hcompl : {z : Fin n → ℝ | euclidNormLP z < ε}ᶜ =
      {z : Fin n → ℝ | euclidNormLP z ≥ ε} := by
    ext z; simp [not_lt]
  rw [← hcompl]
  exact (integral_add_compl hms hg).symm





/-- Auxiliary limit for $n = 2$: $\varepsilon^2\,|\log \varepsilon| \to 0$ as
$\varepsilon \to 0^+$. -/
theorem eps_sq_abs_log_tendsto_zero :
    Filter.Tendsto (fun ε : ℝ => ε ^ 2 * |Real.log ε|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 := tendsto_log_mul_rpow_nhdsGT_zero (by positivity : (0 : ℝ) < 2)
  rw [tendsto_zero_iff_abs_tendsto_zero] at h1
  refine h1.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro x hx
  rw [Set.mem_Ioi] at hx
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg (rpow_nonneg hx.le 2)]
  rw [show x ^ (2:ℝ) = (x:ℝ) ^ (2:ℕ) from by norm_cast]
  ring













































/-- Continuity at $x$ implies that $\sup_{\sigma \in \partial B(x,\varepsilon)}
|u(\sigma) - u(x)| \to 0$ as $\varepsilon \to 0^+$. -/
theorem oscillation_sphere_tendsto_zero {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by

  have hcont : ContinuousOn u (closure Ω) := hu.continuousOn
  have hx_nhds : closure Ω ∈ nhds x :=
    _root_.mem_nhds_iff.mpr ⟨Ω, subset_closure, hΩ, hx⟩
  have hca : ContinuousAt u x := hcont.continuousAt hx_nhds

  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨η, hη, hηu⟩ := hca (δ / 2) (by linarith)
  refine ⟨η, hη, fun ε hε_mem hε_dist => ?_⟩
  rw [mem_Ioi] at hε_mem
  simp [abs_of_pos hε_mem] at hε_dist
  rw [Real.dist_eq, sub_zero]

  have hnn : 0 ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg (fun σ => Real.iSup_nonneg (fun _ => abs_nonneg _))
  rw [abs_of_nonneg hnn]

  have hbnd : ∀ σ : Fin n → ℝ, ⨆ (_ : σ ∈ Metric.sphere x ε), |u σ - u x| ≤ δ / 2 := by
    intro σ
    by_cases hσ : σ ∈ Metric.sphere x ε
    ·
      haveI : Unique (σ ∈ Metric.sphere x ε) := ⟨⟨hσ⟩, fun _ => Subsingleton.elim _ _⟩
      rw [ciSup_unique]
      rw [Metric.mem_sphere] at hσ
      have hdist : dist σ x < η := by rw [hσ]; exact hε_dist
      have := hηu hdist
      rw [Real.dist_eq] at this
      linarith
    ·
      haveI : IsEmpty (σ ∈ Metric.sphere x ε) := isEmpty_iff.mpr hσ
      rw [Real.iSup_of_isEmpty]
      linarith

  calc ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|
      ≤ δ / 2 := ciSup_le hbnd
    _ < δ := by linarith















/-- Laplacian on `EuclideanSpace ℝ (Fin n)` (i.e.\ Mathlib's L²-normed $\mathbb{R}^n$).
Defined as $\Delta f(x) = \sum_i \partial_{x_i}^2 f(x)$ using standard basis vectors. -/
def laplacianE {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

/-- A function $u$ on `EuclideanSpace ℝ (Fin n)` is harmonic on $\Omega$ iff
$\Delta u = 0$ on $\Omega$. -/
def IsHarmonicE {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ Ω, laplacianE u x = 0






/-- Bundled Green's function for the Dirichlet Laplacian on $\Omega \subseteq$
`EuclideanSpace ℝ (Fin n)`. Same defining properties as `GreenFunctionLP` but on the
Euclidean (rather than $L^p$) model of $\mathbb{R}^n$. -/
structure GreenFunctionE (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) where
  G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  domain_open : IsOpen Ω
  boundary_zero : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  distributional_pde : ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ y, G x y * laplacianE φ y = φ x

/-- Squared `EuclideanSpace` norm: $\|v\|^2 = \sum_i v_i^2$ in dimension $3$. -/
lemma euclideanSpace_norm_sq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  congr 1; ext i; simp [Real.norm_eq_abs, sq_abs]









/-- **Kelvin image** of $x$ with respect to the sphere $\partial B(p, R)$ in
$\mathbb{R}^3$: $x^* = p + (R/\|x - p\|)^2 (x - p)$. -/
def kelvinImageE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  p + (R / ‖x - p‖) ^ 2 • (x - p)

/-- The Kelvin image of an interior point $x \ne p$ of $B(p, R)$ lies *outside* the
ball, which is the property that makes the Kelvin image useful for constructing
Green's functions on the ball. -/
theorem kelvinImageE_not_in_ball (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R) (hxp : x ≠ p) :
    kelvinImageE p R x ∉ Metric.ball p R := by
  have hxp_pos : (0 : ℝ) < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
  have hxp_lt_R : ‖x - p‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, not_lt, dist_eq_norm]
  have h1 : kelvinImageE p R x - p = (R / ‖x - p‖) ^ 2 • (x - p) := by
    simp only [kelvinImageE, add_sub_cancel_left]
  rw [h1, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  have hxp_ne : ‖x - p‖ ≠ 0 := ne_of_gt hxp_pos
  have h2 : (R / ‖x - p‖) ^ 2 * ‖x - p‖ = R ^ 2 / ‖x - p‖ := by field_simp
  rw [h2]
  rw [le_div_iff₀ hxp_pos]
  nlinarith [sq_nonneg (R - ‖x - p‖)]


/-- Explicit Green's function on the ball $B(p, R) \subseteq \mathbb{R}^3$
constructed by the Kelvin-image method: $G(x, y) = -\frac{1}{4\pi|y-x|}
+ \frac{R/\|x-p\|}{4\pi|y - x^*|}$, where $x^*$ is the Kelvin image of $x$. The
center case $x = p$ is handled separately. -/
def greenBallFunctionE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if x = p then
    -1 / (4 * Real.pi * ‖y - p‖) + 1 / (4 * Real.pi * R)
  else
    -1 / (4 * Real.pi * ‖y - x‖) +
      (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖))













end LaplacePoisson
