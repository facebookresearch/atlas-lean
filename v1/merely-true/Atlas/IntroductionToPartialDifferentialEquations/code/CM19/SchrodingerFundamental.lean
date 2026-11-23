/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierInversion

open Complex Finset MeasureTheory

noncomputable section

/-- Squared Euclidean norm $|x|^2 = \sum_{i=1}^n (x^i)^2$ for $x \in \mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- The Schrödinger fundamental solution (Definition 2.0.1) in $n$ spatial dimensions:
$$K(t, x) = \frac{1}{(2\pi i t)^{n/2}}\, \exp\!\left(\frac{i|x|^2}{2t}\right).$$ -/
def schrodingerKernel (n : ℕ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  (2 * ↑Real.pi * I * ↑t) ^ (-(↑n : ℂ) / 2) *
  exp (I * ↑(euclidNormSq x) / (2 * ↑t))

/-- The partial derivative $\partial_j f(x)$ of a function $f : \mathbb{R}^n \to \mathbb{C}$
in the $j$-th coordinate direction, defined as the one-variable derivative obtained by varying
the $j$-th coordinate while keeping the others fixed. -/
def spatialPartialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  deriv (fun s => f (Function.update x j s)) (x j)

/-- The spatial Laplacian $\Delta f = \sum_{j=1}^n \partial_j^2 f$. -/
def spatialLaplacian {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ j, spatialPartialDeriv j (spatialPartialDeriv j f) x

/-- The free Schrödinger operator $i\,\partial_t u + \tfrac{1}{2}\Delta u$ applied to a
time-dependent field $u(t, x)$. -/
def schrodingerOp (n : ℕ) (u : ℝ → (Fin n → ℝ) → ℂ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  I * deriv (fun s => u s x) t + (1 / 2) * spatialLaplacian (u t) x

/-- The inclusion $\mathbb{R} \hookrightarrow \mathbb{C}$ has derivative $1$ at every point. -/
lemma hasDerivAt_ofReal (s : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s :=
  ofRealCLM.hasDerivAt.congr_deriv (by simp)

/-- The map $s \mapsto s^2 : \mathbb{R} \to \mathbb{C}$ has derivative $2s$. -/
lemma hasDerivAt_ofReal_sq (s : ℝ) :
    HasDerivAt (fun s : ℝ => ((s : ℂ)) ^ 2) (2 * (s : ℂ)) s :=
  ((hasDerivAt_ofReal s).mul (hasDerivAt_ofReal s) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun x => by simp [sq, Pi.mul_apply]))).congr_deriv (by ring)

/-- Chain rule: $\frac{d}{ds} \exp(a s^2 + b) = \exp(a s^2 + b) \cdot 2as$ for complex
constants $a, b$ and a real variable $s$. -/
lemma hasDerivAt_cexp_affine_sq (a b : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b))
      (exp (a * ((s : ℂ)) ^ 2 + b) * (2 * a * (s : ℂ))) s := by
  have h_inner : HasDerivAt (fun s : ℝ => a * ((s : ℂ)) ^ 2 + b) (2 * a * (s : ℂ)) s :=
    ((hasDerivAt_ofReal_sq s).const_mul a).add (hasDerivAt_const s b) |>.congr_deriv (by ring)
  exact h_inner.cexp.congr_deriv (by ring)

/-- Second derivative of $\exp(a s^2 + b)$: differentiating $\exp(a s^2 + b) \cdot 2as$ once
more yields $\exp(a s^2 + b) (4 a^2 s^2 + 2 a)$. -/
lemma hasDerivAt_cexp_affine_sq_times_linear (a b : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b) * (2 * a * (s : ℂ)))
      (exp (a * ((s : ℂ)) ^ 2 + b) * (4 * a ^ 2 * ((s : ℂ)) ^ 2 + 2 * a)) s :=
  ((hasDerivAt_cexp_affine_sq a b s).mul
    ((hasDerivAt_ofReal s).const_mul (2 * a))).congr_deriv (by ring)

/-- Updating the $j$-th coordinate of $x$ to $s$ shifts the squared norm by
$-x_j^2 + s^2$, i.e. $|x[j \mapsto s]|^2 = |x|^2 - x_j^2 + s^2$. -/
lemma euclidNormSq_update {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    euclidNormSq (Function.update x j s) = euclidNormSq x - (x j) ^ 2 + s ^ 2 := by
  simp only [euclidNormSq]
  have key : ∀ i : Fin n, (Function.update x j s i) ^ 2 =
    if i = j then s ^ 2 else (x i) ^ 2 := by
    intro i; simp [Function.update_apply]
  simp_rw [key]; rw [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']
  simp [Finset.mem_univ]; linarith

/-- Reformulates the second pure partial derivative $\partial_j^2 f$ as an iterated one-variable
derivative obtained by varying the $j$-th coordinate. -/
lemma second_spatialPartialDeriv_eq {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) :
    spatialPartialDeriv j (spatialPartialDeriv j f) x =
    deriv (fun r => deriv (fun s => f (Function.update x j s)) r) (x j) := by
  unfold spatialPartialDeriv; simp only [Function.update_self]
  congr 1; ext s; congr 1; ext r; congr 1; ext i
  simp [Function.update_apply]; split <;> simp_all

/-- Closed-form for the second partial derivative $\partial_j^2$ of the Schrödinger phase
$\exp(i|y|^2/(2t))$ at $x$, expressed in the $a = i/(2t)$ parametrization. -/
lemma second_partial_deriv_exp_phase {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    spatialPartialDeriv j (spatialPartialDeriv j
      (fun y => exp (I * ↑(euclidNormSq y) / (2 * ↑t)))) x =
    exp (I * ↑(euclidNormSq x) / (2 * ↑t)) *
    (4 * (I / (2 * ↑t)) ^ 2 * ((x j : ℂ)) ^ 2 + 2 * (I / (2 * ↑t))) := by
  rw [second_spatialPartialDeriv_eq]
  set a : ℂ := I / (2 * ↑t)
  set b : ℂ := I * ↑(euclidNormSq x - (x j) ^ 2) / (2 * ↑t)
  have h_eq : (fun s : ℝ => exp (I * ↑(euclidNormSq (Function.update x j s)) / (2 * ↑t))) =
    (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b)) := by
    ext s; congr 1; simp only [a, b]; rw [euclidNormSq_update]; push_cast; ring
  rw [h_eq]
  have h_deriv :
    (fun r : ℝ => deriv (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b)) r) =
    (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b) * (2 * a * ((s : ℂ)))) := by
    ext s; exact (hasDerivAt_cexp_affine_sq a b s).deriv
  rw [h_deriv, (hasDerivAt_cexp_affine_sq_times_linear a b (x j)).deriv]
  congr 1; congr 1; simp only [a, b]; push_cast; ring

/-- Closed-form for the spatial Laplacian of the Schrödinger phase $\exp(i|y|^2/(2t))$:
$$\Delta_x \exp(i|x|^2/(2t)) = \exp(i|x|^2/(2t))\left(\frac{i n}{t} - \frac{|x|^2}{t^2}\right).$$ -/
lemma laplacian_exp_phase {n : ℕ} (x : Fin n → ℝ) (t : ℝ) (ht : t ≠ 0) :
    spatialLaplacian (fun y => exp (I * ↑(euclidNormSq y) / (2 * ↑t))) x =
    exp (I * ↑(euclidNormSq x) / (2 * ↑t)) *
    (I * ↑n / ↑t - ↑(euclidNormSq x) / ↑t ^ 2) := by
  unfold spatialLaplacian
  simp_rw [second_partial_deriv_exp_phase]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
  simp only [euclidNormSq, ofReal_sum, ofReal_pow]
  have ht' : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  field_simp
  linear_combination (4 : ℂ) * (∑ i : Fin n, (↑(x i) : ℂ) ^ 2) * I_mul_I

/-- The spatial half-Laplacian of the Schrödinger kernel:
$$\tfrac{1}{2}\Delta_x K(t, x) = K(t, x)\left(\frac{i n}{2t} - \frac{|x|^2}{2t^2}\right).$$
The constant prefactor $(2\pi i t)^{-n/2}$ pulls out and the half-Laplacian of the phase is
computed via `laplacian_exp_phase`. -/
lemma half_laplacian_schrodinger (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    (1 / 2 : ℂ) * spatialLaplacian (schrodingerKernel n t) x =
    schrodingerKernel n t x *
    (I * ↑n / (2 * ↑t) - ↑(euclidNormSq x) / (2 * ↑t ^ 2)) := by


  set A : ℂ := (2 * ↑Real.pi * I * ↑t) ^ (-(↑n : ℂ) / 2) with hA_def
  set E : (Fin n → ℝ) → ℂ := fun y => exp (I * ↑(euclidNormSq y) / (2 * ↑t)) with hE_def

  have hK : schrodingerKernel n t = fun y => A * E y := by
    ext y; simp [schrodingerKernel, A, E]


  have hLap : spatialLaplacian (fun y => A * E y) x = A * spatialLaplacian E x := by
    unfold spatialLaplacian
    rw [Finset.mul_sum]
    congr 1; ext j


    rw [second_spatialPartialDeriv_eq, second_spatialPartialDeriv_eq]


    have h1 : ∀ r, deriv (fun s => A * E (Function.update x j s)) r =
        A * deriv (fun s => E (Function.update x j s)) r := by
      intro r


      have : DifferentiableAt ℝ (fun s => E (Function.update x j s)) r := by

        simp only [E]
        set a : ℂ := I / (2 * ↑t)
        set b : ℂ := I * ↑(euclidNormSq x - (x j) ^ 2) / (2 * ↑t)
        have h_eq : (fun s : ℝ => exp (I * ↑(euclidNormSq (Function.update x j s)) / (2 * ↑t))) =
          (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b)) := by
          ext s; congr 1; simp only [a, b]; rw [euclidNormSq_update]; push_cast; ring
        rw [h_eq]
        exact (hasDerivAt_cexp_affine_sq a b r).differentiableAt
      exact deriv_const_mul A this
    simp_rw [h1]

    have h2 : DifferentiableAt ℝ (fun r => deriv (fun s => E (Function.update x j s)) r) (x j) := by
      simp only [E]
      set a : ℂ := I / (2 * ↑t)
      set b : ℂ := I * ↑(euclidNormSq x - (x j) ^ 2) / (2 * ↑t)
      have h_eq : (fun s : ℝ => exp (I * ↑(euclidNormSq (Function.update x j s)) / (2 * ↑t))) =
        (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b)) := by
        ext s; congr 1; simp only [a, b]; rw [euclidNormSq_update]; push_cast; ring
      simp_rw [h_eq]
      have hd : (fun r : ℝ => deriv (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b)) r) =
        (fun s : ℝ => exp (a * ((s : ℂ)) ^ 2 + b) * (2 * a * ((s : ℂ)))) := by
        ext s; exact (hasDerivAt_cexp_affine_sq a b s).deriv
      rw [hd]
      exact (hasDerivAt_cexp_affine_sq_times_linear a b (x j)).differentiableAt
    exact deriv_const_mul A h2
  rw [hK, hLap, laplacian_exp_phase x t (ne_of_gt ht)]

  simp only [E, A]
  ring

/-- Time derivative of the Schrödinger kernel multiplied by $i$:
$$i\,\partial_t K(t, x) = K(t, x)\left(-\frac{n i}{2 t} + \frac{|x|^2}{2 t^2}\right).$$
Combined with `half_laplacian_schrodinger`, this gives that $K$ solves
$i\partial_t K + \tfrac{1}{2}\Delta K = 0$. -/
theorem time_deriv_schrodinger (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (ht : t > 0) :
    I * deriv (fun s => schrodingerKernel n s x) t =
    schrodingerKernel n t x *
      (-(↑n : ℂ) * I / (2 * ↑t) + ↑(euclidNormSq x) / (2 * ↑t ^ 2)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have htne_c : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  set c2pi := (↑(2 * Real.pi) : ℂ) with hc2pi_def
  have hc2pi_ne : c2pi ≠ 0 := by simp only [c2pi, ofReal_ne_zero]; positivity
  set z := c2pi * I * (↑t : ℂ)
  have hbase_ne : z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc2pi_ne I_ne_zero) htne_c
  have hbase_mem : z ∈ Complex.slitPlane := by
    have heq : z = ↑(2 * Real.pi * t) * I := by simp [z, c2pi]; ring
    rw [heq, Complex.mem_slitPlane_iff]; right
    simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity
  set Q := euclidNormSq x with hQ
  set p := -(↑n : ℂ) / 2 with hp
  set e := exp (I * ((Q / (2 * t) : ℝ) : ℂ)) with he

  have exp_conv : ∀ s : ℝ, I * ↑(euclidNormSq x) / (2 * ↑s) = I * ((Q / (2 * s) : ℝ) : ℂ) := by
    intro s; simp only [← hQ]; push_cast; ring
  have cpow_conv : ∀ s : ℝ, (2 : ℂ) * ↑Real.pi * I * ↑s = c2pi * I * ↑s := by
    intro s; simp [c2pi]

  have hderiv_cpow : HasDerivAt (fun s : ℝ => (c2pi * I * ↑s) ^ p)
      (p * z ^ (p - 1) * (c2pi * I)) t := by
    have hlin : HasDerivAt (fun w : ℂ => c2pi * I * w) (c2pi * I) (↑t : ℂ) := by
      have h2 := (hasDerivAt_id (↑t : ℂ)).const_mul (c2pi * I)
      simp [mul_one] at h2; exact h2
    exact (hlin.cpow_const hbase_mem).comp_ofReal

  have hderiv_exp : HasDerivAt (fun s : ℝ => exp (I * ((Q / (2 * s) : ℝ) : ℂ)))
      (e * (I * ((-Q / (2 * t ^ 2) : ℝ) : ℂ))) t := by
    have hq : HasDerivAt (fun s : ℝ => (Q / (2 * s) : ℝ)) (-Q / (2 * t ^ 2)) t := by
      have := (hasDerivAt_inv ht_ne).const_mul (Q / 2)
      simp only [mul_neg] at this
      convert this using 1 <;> [ext s; skip] <;> ring
    exact (hq.ofReal_comp.const_mul I).cexp

  have hfun_eq : (fun s => schrodingerKernel n s x) =
      (fun s => (c2pi * I * ↑s) ^ p * exp (I * ((Q / (2 * s) : ℝ) : ℂ))) := by
    ext s; unfold schrodingerKernel; rw [cpow_conv, exp_conv]

  have hK : HasDerivAt (fun s => schrodingerKernel n s x)
      (p * z ^ (p - 1) * (c2pi * I) * e +
       z ^ p * (e * (I * ((-Q / (2 * t ^ 2) : ℝ) : ℂ)))) t := by
    rw [hfun_eq]; exact hderiv_cpow.mul hderiv_exp
  rw [hK.deriv]

  have hcpow_sub : z ^ (p - 1) = z ^ p / z := by
    have h := Complex.cpow_sub p 1 hbase_ne
    rw [cpow_one] at h; exact h
  rw [hcpow_sub]

  have hz_div : c2pi * I / z = 1 / ↑t := by simp only [z]; field_simp

  have step1 : p * (z ^ p / z) * (c2pi * I) = z ^ p * (p * (c2pi * I / z)) := by ring
  rw [step1, hz_div]

  have hKval : schrodingerKernel n t x = z ^ p * e := by
    unfold schrodingerKernel; rw [cpow_conv, exp_conv]
  rw [hKval]

  simp only [p]
  ring_nf
  rw [I_sq]
  push_cast
  ring_nf

/-- Lemma 2.0.2: for $t > 0$, the Schrödinger fundamental solution $K(t, x)$ solves the free
Schrödinger equation $i\,\partial_t K + \tfrac{1}{2}\Delta K = 0$ pointwise. -/
theorem lemma_2_0_2_schrodinger_pde (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    schrodingerOp n (schrodingerKernel n) t x = 0 := by
  unfold schrodingerOp
  rw [time_deriv_schrodinger n t x ht, half_laplacian_schrodinger n t x ht]
  ring

/-- Dot product $\xi \cdot x = \sum_{i=1}^n \xi_i x_i$ on $\mathbb{R}^n$ indexed by $\text{Fin } n$. -/
def finDotProduct {n : ℕ} (ξ x : Fin n → ℝ) : ℝ := ∑ i, ξ i * x i

/-- Fourier transform on $\mathbb{R}^n$ with the analyst convention used in the book:
$\hat f(\xi) = \int_{\mathbb{R}^n} f(x)\, e^{-2\pi i \xi \cdot x}\, d^n x.$ -/
def fourierTransformFin {n : ℕ} (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, f x * exp ((↑(-2 * Real.pi * finDotProduct ξ x) : ℂ) * I)

/-- Inverse Fourier transform on $\mathbb{R}^n$:
$f^\vee(x) = \int_{\mathbb{R}^n} f(\xi)\, e^{2\pi i \xi \cdot x}\, d^n \xi.$ -/
def inverseFourierTransformFin {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ ξ : Fin n → ℝ, f ξ * exp ((↑(2 * Real.pi * finDotProduct ξ x) : ℂ) * I)

/-- The spatial Fourier transform of the Schrödinger kernel:
$\hat K(t, \xi) = e^{-2\pi^2 i t |\xi|^2}.$ -/
def schrodingerKernelFT (n : ℕ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  exp (((-2 * ↑(Real.pi ^ 2) * ↑t * ↑(euclidNormSq ξ)) : ℂ) * I)

/-- The spatial Fourier transform of the (candidate) solution $\psi(t, \cdot)$:
$\hat\psi(t, \xi) = \hat K(t, \xi)\,\hat\phi(\xi).$ -/
def schrodingerSolutionFT (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  schrodingerKernelFT n t ξ * fourierTransformFin φ ξ

/-- The convolution representation of the Schrödinger solution:
$\psi(t, x) = (K(t, \cdot) * \phi)(x) = \int K(t, x - y)\,\phi(y)\, d^n y.$ -/
def schrodingerConvolution (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  ∫ y : Fin n → ℝ, schrodingerKernel n t (x - y) * φ y

/-- The regularized Gaussian replacing the oscillatory kernel: for $\delta > 0$,
$g_\delta(t, \xi) = \exp\!\left(-2\pi^2 (\delta + i) t |\xi|^2\right).$
As $\delta \downarrow 0$, $g_\delta \to \hat K(t, \cdot)$ and the Gaussian is integrable, which
permits a rigorous Fourier-inversion argument. -/
def regularizedGaussian (n : ℕ) (δ : ℝ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  exp ((-2 * ↑(Real.pi ^ 2) * (↑δ + I) * ↑t * ↑(euclidNormSq ξ) : ℂ))

/-- The local `fourierTransformFin` (defined via `Fin n`-indexed dot products) coincides with the
$n$-dimensional Fourier transform `CM16.fourierTransformND` developed in Class Meeting 16. -/
lemma fourierTransformFin_eq_fourierTransformND {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) :
    fourierTransformFin f ξ = CM16.fourierTransformND n f ξ := by
  simp only [fourierTransformFin, CM16.fourierTransformND, finDotProduct]
  congr 1; ext x; congr 1; congr 1; push_cast; ring

/-- Regularization step: writing the oscillatory kernel as the $\delta \downarrow 0$ limit of
$g_\delta$ and applying dominated convergence (with bound $|\hat\phi|$),
$$\psi(t, x) = (\hat K(t, \cdot)\,\hat\phi)^\vee(x)
  = \lim_{\delta \downarrow 0} (g_\delta(t, \cdot)\,\hat\phi)^\vee(x).$$ -/
theorem regularization_limit {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    inverseFourierTransformFin (schrodingerSolutionFT n φ t) x =
    Filter.limUnder (nhdsWithin 0 (Set.Ioi 0))
      (fun δ => inverseFourierTransformFin
        (fun ξ => regularizedGaussian n δ t ξ * fourierTransformFin φ ξ) x) := by


  symm
  apply Filter.Tendsto.limUnder_eq

  show Filter.Tendsto
    (fun δ => ∫ ξ, (regularizedGaussian n δ t ξ * fourierTransformFin φ ξ) *
      exp ((↑(2 * Real.pi * finDotProduct ξ x) : ℂ) * I))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ ξ, schrodingerSolutionFT n φ t ξ *
      exp ((↑(2 * Real.pi * finDotProduct ξ x) : ℂ) * I)))


  set bound := fun (ξ : Fin n → ℝ) => ‖fourierTransformFin φ ξ‖ with hbound_def
  apply tendsto_integral_filter_of_dominated_convergence bound
  ·
    apply Filter.Eventually.of_forall; intro δ
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Continuous.mul
      · unfold regularizedGaussian euclidNormSq
        apply Complex.continuous_exp.comp
        apply Continuous.const_mul
        apply continuous_ofReal.comp
        exact continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
      ·
        rw [show fourierTransformFin φ = CM16.fourierTransformND n φ from
          funext (fourierTransformFin_eq_fourierTransformND φ)]
        exact (CM16.schwartz_ft_smoothND φ (hφ_smooth.of_le le_top) hφ_supp).continuous
    · apply Complex.continuous_exp.comp
      apply Continuous.mul
      · apply continuous_ofReal.comp
        apply Continuous.const_mul
        exact continuous_finset_sum _ fun i _ =>
          (continuous_apply i).mul continuous_const
      · exact continuous_const
  ·
    apply eventually_nhdsWithin_of_forall; intro δ hδ
    apply ae_of_all; intro ξ
    simp only [hbound_def, norm_mul]
    calc ‖regularizedGaussian n δ t ξ‖ * ‖fourierTransformFin φ ξ‖ *
          ‖cexp (↑(2 * Real.pi * finDotProduct ξ x) * I)‖
        = ‖regularizedGaussian n δ t ξ‖ * ‖fourierTransformFin φ ξ‖ * 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
      _ = ‖regularizedGaussian n δ t ξ‖ * ‖fourierTransformFin φ ξ‖ := mul_one _
      _ ≤ 1 * ‖fourierTransformFin φ ξ‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)


          unfold regularizedGaussian
          rw [norm_exp]
          apply Real.exp_le_one_iff.mpr

          have hξ : (0 : ℝ) ≤ euclidNormSq ξ :=
            Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
          have hδ_pos : (0 : ℝ) < δ := hδ

          have hre : (-2 * ↑(Real.pi ^ 2) * (↑δ + I) * ↑t * ↑(euclidNormSq ξ)).re =
              -2 * Real.pi ^ 2 * δ * t * euclidNormSq ξ := by
            have h1 : ↑(Real.pi ^ 2) = (↑Real.pi : ℂ) ^ 2 := by push_cast; ring
            rw [h1]
            simp only [ofReal_re, ofReal_im, I_re, I_im, mul_re, add_re, mul_im, add_im,
                       pow_succ, pow_zero, one_mul, mul_one, mul_zero, zero_mul,
                       sub_zero, add_zero, zero_add, neg_re, neg_im]
            norm_num
          rw [hre]
          have : 0 ≤ Real.pi ^ 2 * δ * t * euclidNormSq ξ :=
            mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hδ_pos.le) ht.le) hξ
          linarith
      _ = ‖fourierTransformFin φ ξ‖ := one_mul _
  ·
    rw [hbound_def]
    rw [show (fun ξ => ‖fourierTransformFin φ ξ‖) =
        (fun ξ => ‖CM16.fourierTransformND n φ ξ‖) from by
      ext ξ; rw [fourierTransformFin_eq_fourierTransformND]]
    exact (CM16.schwartz_decay_of_compact_supportND φ
      (hφ_smooth.of_le le_top) hφ_supp).norm
  ·
    apply ae_of_all; intro ξ
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.mul
      ·


        have h_at_zero : regularizedGaussian n 0 t ξ = schrodingerKernelFT n t ξ := by
          unfold regularizedGaussian schrodingerKernelFT
          congr 1; simp only [ofReal_zero, zero_add]; ring
        have h_cont : Continuous (fun δ : ℝ => regularizedGaussian n δ t ξ) := by
          unfold regularizedGaussian
          exact Complex.continuous_exp.comp
            ((continuous_const.mul (continuous_ofReal.add continuous_const)).mul
              continuous_const |>.mul continuous_const)
        rw [← h_at_zero]
        exact h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

      · exact tendsto_const_nhds
    · exact tendsto_const_nhds

/-- Coercion identity: $(\sum_i (\xi_i)^2) \in \mathbb{C}$ equals $\sum_i (\xi_i : \mathbb{C})^2$. -/
lemma ofReal_euclidNormSq {n : ℕ} (ξ : Fin n → ℝ) :
    (↑(euclidNormSq ξ) : ℂ) = ∑ i, (↑(ξ i) : ℂ) ^ 2 := by
  simp [euclidNormSq, ofReal_pow]

/-- For $\delta > 0$ and $t > 0$, the regularized Gaussian $g_\delta(t, \cdot)$ is integrable
on $\mathbb{R}^n$: the real part of the exponent is $-2\pi^2 \delta t |\xi|^2 < 0$ for
$\xi \neq 0$, which gives Gaussian decay. -/
lemma regularizedGaussian_integrable (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable (regularizedGaussian n δ t) := by
  unfold regularizedGaussian
  simp_rw [ofReal_euclidNormSq]
  have key : (fun ξ : Fin n → ℝ =>
      cexp (-2 * ↑(Real.pi ^ 2) * (↑δ + I) * ↑t * ∑ i, (↑(ξ i) : ℂ) ^ 2)) =
    (fun ξ : Fin n → ℝ =>
      cexp (-(2 * ↑(Real.pi ^ 2) * (↑δ + I) * ↑t) * ∑ i, (↑(ξ i) : ℂ) ^ 2 +
        ∑ i : Fin n, (0 : ℂ) * ↑(ξ i))) := by
    ext ξ; congr 1; simp only [zero_mul, sum_const_zero, add_zero]; ring
  rw [key]
  apply GaussianFourier.integrable_cexp_neg_mul_sum_add
  simp only [mul_re, add_re, ofReal_re, I_re, ofReal_im, I_im, mul_im, add_im]
  norm_num; positivity

/-- Joint integrability on $\mathbb{R}^n \times \mathbb{R}^n$ of the integrand
$g_\delta(t, \xi)\, e^{2\pi i \xi \cdot (x-y)}\, \phi(y)$ needed to apply Fubini's theorem in
`convolution_via_FT_inversion`. -/
lemma fubini_integ_regularizedGaussian_phi {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (ξ y : Fin n → ℝ) =>
        regularizedGaussian n δ t ξ * cexp (↑(2 * Real.pi * finDotProduct ξ (x - y)) * I) * φ y)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by

  apply MeasureTheory.Integrable.mono
        (MeasureTheory.Integrable.op_fst_snd continuous_mul
          ⟨1, fun a b => by rw [one_mul]; exact norm_mul_le a b⟩
          (regularizedGaussian_integrable n δ hδ t ht)
          (hφ_smooth.continuous.integrable_of_hasCompactSupport hφ_supp))
  ·
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    apply Continuous.mul
    ·
      unfold regularizedGaussian euclidNormSq
      apply Complex.continuous_exp.comp
      apply Continuous.const_mul
      apply continuous_ofReal.comp
      apply continuous_finset_sum
      intro i _; exact ((continuous_apply i).comp continuous_fst).pow 2
    ·
      apply Complex.continuous_exp.comp
      apply Continuous.mul
      · apply continuous_ofReal.comp
        apply Continuous.const_mul
        unfold finDotProduct
        apply continuous_finset_sum
        intro i _
        exact ((continuous_apply i).comp continuous_fst).mul
          (continuous_const.sub ((continuous_apply i).comp continuous_snd))
      · exact continuous_const
    · exact hφ_smooth.continuous.comp continuous_snd
  ·
    filter_upwards with ⟨ξ, y⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [Complex.norm_exp_ofReal_mul_I]
    simp [mul_one]

/-- Convolution-via-Fourier-inversion at the regularized level: for any $\delta > 0$,
$$(g_\delta(t, \cdot)\,\hat\phi)^\vee(x) = \int g_\delta^\vee(t, x - y)\,\phi(y)\, d^n y.$$
The proof combines the product formula for the inverse Fourier transform with Fubini's theorem
to swap the $\xi$ and $y$ integrals. -/
theorem convolution_via_FT_inversion {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    inverseFourierTransformFin
      (fun ξ => regularizedGaussian n δ t ξ * fourierTransformFin φ ξ) x =
    ∫ y : Fin n → ℝ,
      inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y := by


  simp only [inverseFourierTransformFin, fourierTransformFin]

  have step1_eq : ∀ c : ℂ, ∀ g : (Fin n → ℝ) → ℂ, ∀ d : ℂ,
      c * (∫ y, g y) * d = ∫ y, c * g y * d := by
    intro c g d
    have hc : ∀ (r : ℂ) (f : (Fin n → ℝ) → ℂ),
        r * ∫ y, f y = ∫ y, r * f y := fun r f => (integral_const_mul r f).symm
    have hd : ∀ (r : ℂ) (f : (Fin n → ℝ) → ℂ),
        (∫ y, f y) * r = ∫ y, f y * r := fun r f => (integral_mul_const r f).symm
    rw [mul_assoc, hd, hc]; congr 1; ext y; ring
  conv_lhs =>
    arg 2; ext ξ
    rw [step1_eq]


  have exp_combine : ∀ (ξ y : Fin n → ℝ),
      cexp (↑(-2 * Real.pi * finDotProduct ξ y) * I) *
      cexp (↑(2 * Real.pi * finDotProduct ξ x) * I) =
      cexp (↑(2 * Real.pi * finDotProduct ξ (x - y)) * I) := by
    intro ξ y
    rw [← Complex.exp_add]; congr 1
    simp only [finDotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    push_cast; ring
  conv_lhs =>
    arg 2; ext ξ; arg 2; ext y
    rw [show regularizedGaussian n δ t ξ * (φ y * cexp (↑(-2 * Real.pi * finDotProduct ξ y) * I)) *
        cexp (↑(2 * Real.pi * finDotProduct ξ x) * I) =
        regularizedGaussian n δ t ξ * cexp (↑(2 * Real.pi * finDotProduct ξ (x - y)) * I) * φ y
        from by rw [← exp_combine]; ring]


  have fubini_integ : MeasureTheory.Integrable
      (Function.uncurry fun (ξ y : Fin n → ℝ) =>
        regularizedGaussian n δ t ξ * cexp (↑(2 * Real.pi * finDotProduct ξ (x - y)) * I) * φ y)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    fubini_integ_regularizedGaussian_phi φ hφ_smooth hφ_supp δ hδ t ht x
  rw [MeasureTheory.integral_integral_swap fubini_integ]


  congr 1; ext y
  exact integral_mul_const (φ y)
    (fun ξ => regularizedGaussian n δ t ξ * cexp (↑(2 * Real.pi * finDotProduct ξ (x - y)) * I))

/-- The closed-form inverse Fourier transform of the regularized Gaussian:
$$g_\delta^\vee(t, z) = (2\pi(\delta + i)t)^{-n/2}\, \exp\!\left(\frac{-|z|^2}{2t(\delta + i)}
\right).$$
At $\delta = 0$ this formally recovers the Schrödinger kernel $K(t, z)$. -/
def regularizedGaussianInverseFT (n : ℕ) (δ : ℝ) (t : ℝ) (z : Fin n → ℝ) : ℂ :=
  (2 * ↑Real.pi * (↑δ + I) * ↑t) ^ (-(↑n : ℂ) / 2) *
  exp (-(↑(euclidNormSq z) : ℂ) / (2 * ↑t * (↑δ + I)))

/-- The inverse Fourier transform of the regularized Gaussian agrees with the closed-form
expression `regularizedGaussianInverseFT`. Proved by reducing to the complex Gaussian Fourier
transform formula `CM16.fourier_gaussian_complex`. -/
theorem inverseFT_regularizedGaussian_eq_closedForm {n : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : 0 < t) (z : Fin n → ℝ) :
    inverseFourierTransformFin (regularizedGaussian n δ t) z =
    regularizedGaussianInverseFT n δ t z := by


  have h_inv_eq_fwd : inverseFourierTransformFin (regularizedGaussian n δ t) z =
      CM16.fourierTransformND n (regularizedGaussian n δ t) (-z) := by
    simp only [inverseFourierTransformFin, CM16.fourierTransformND, finDotProduct]
    congr 1; ext ξ; congr 2
    simp only [Pi.neg_apply]
    have : ∑ j, (-z j) * ξ j = -(∑ j, ξ j * z j) := by
      simp [mul_comm, Finset.sum_neg_distrib]
    rw [this]; push_cast; ring
  rw [h_inv_eq_fwd]

  set w : ℂ := 2 * ↑Real.pi * (↑δ + I) * ↑t with hw_def
  have hw_re : 0 < w.re := by
    simp only [w, mul_re, ofReal_re, ofReal_im, add_re, I_re, add_im, I_im, mul_one, mul_zero,
               sub_zero, add_zero, zero_add]; norm_num; positivity
  have hw_im : w.im ≠ 0 := by
    simp only [w, mul_im, ofReal_re, ofReal_im, add_im, I_im, add_re, I_re, mul_one, mul_zero,
               add_zero, zero_add]; norm_num
    exact ne_of_gt (by positivity)


  have h_eq : (regularizedGaussian n δ t) =
      (fun x => exp (↑(-Real.pi) * w * ↑(CM16.euclidNormSq x))) := by
    ext ξ
    simp only [regularizedGaussian, CM16.euclidNormSq, euclidNormSq]
    congr 1; push_cast; ring

  rw [h_eq, CM16.fourier_gaussian_complex w hw_re hw_im]

  unfold regularizedGaussianInverseFT
  congr 1

  congr 1

  have h_neg : CM16.euclidNormSq (-z) = CM16.euclidNormSq z := by
    simp [CM16.euclidNormSq, neg_sq]

  have h_ens : ∀ v : Fin n → ℝ, euclidNormSq v = CM16.euclidNormSq v := by
    intro v; simp [euclidNormSq, CM16.euclidNormSq]
  rw [h_neg, ← h_ens]

  simp only [w]
  have hpi_ne : (↑Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have ht_ne : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have hdi_ne : (↑δ + I : ℂ) ≠ 0 := by
    intro h; have := congr_arg im h
    simp at this
  push_cast
  field_simp

/-- Pointwise convergence of the regularized inverse Fourier transform to the Schrödinger kernel:
for each $z$,
$g_\delta^\vee(t, z) \to K(t, z)$ as $\delta \downarrow 0$. This is the pointwise input to the
dominated convergence argument in `dominated_convergence_convolution`. -/
theorem pointwise_limit_regularized_kernel {n : ℕ} (t : ℝ) (ht : 0 < t)
    (z : Fin n → ℝ) :
    Filter.Tendsto (fun δ => inverseFourierTransformFin (regularizedGaussian n δ t) z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (schrodingerKernel n t z)) := by

  have h_at_zero : regularizedGaussianInverseFT n 0 t z = schrodingerKernel n t z := by
    unfold regularizedGaussianInverseFT schrodingerKernel
    simp only [ofReal_zero, zero_add]
    have h_exp : exp (-(↑(euclidNormSq z) : ℂ) / (2 * ↑t * I)) =
                 exp (I * ↑(euclidNormSq z) / (2 * ↑t)) := by
      congr 1
      rw [show -(↑(euclidNormSq z) : ℂ) / (2 * ↑t * I) =
        ↑(euclidNormSq z) * (↑t)⁻¹ * I⁻¹ * (-1 / 2) from by ring]
      rw [inv_I]; ring
    rw [h_exp]

  rw [← h_at_zero]
  apply Filter.Tendsto.congr'
  ·
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun δ hδ =>
      (inverseFT_regularizedGaussian_eq_closedForm δ hδ t ht z).symm⟩
  ·
    apply ContinuousAt.continuousWithinAt
    unfold regularizedGaussianInverseFT
    apply ContinuousAt.mul
    ·
      apply ContinuousAt.cpow
      · apply ContinuousAt.mul
        · apply ContinuousAt.mul continuousAt_const
          exact continuous_ofReal.continuousAt.add continuousAt_const
        · exact continuousAt_const
      · exact continuousAt_const
      ·
        simp only [ofReal_zero, zero_add]
        rw [show (2 : ℂ) * ↑Real.pi * I * ↑t = ↑(2 * Real.pi * t) * I from by push_cast; ring]
        rw [Complex.mem_slitPlane_iff]; right
        simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity
    ·
      apply Complex.continuous_exp.continuousAt.comp
      apply ContinuousAt.div continuousAt_const
      · apply ContinuousAt.mul continuousAt_const
        exact continuous_ofReal.continuousAt.add continuousAt_const
      · simp only [ofReal_zero, zero_add]
        apply mul_ne_zero
        · exact_mod_cast (show (2 * t : ℝ) ≠ 0 from ne_of_gt (by positivity))
        · exact I_ne_zero

/-- For $\delta > 0$, the integrand $y \mapsto g_\delta^\vee(t, x - y)\,\phi(y)$ is
$\mathrm{AEStronglyMeasurable}$ with respect to Lebesgue measure on $\mathbb{R}^n$. -/
theorem ae_strongly_measurable_regularized_integrand {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    AEStronglyMeasurable
      (fun y => inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y)
      volume := by
  unfold inverseFourierTransformFin
  apply AEStronglyMeasurable.mul
  · have : AEStronglyMeasurable
        (fun (p : (Fin n → ℝ) × (Fin n → ℝ)) =>
          regularizedGaussian n δ t p.2 *
            exp ((↑(2 * Real.pi * finDotProduct p.2 (x - p.1)) : ℂ) * I))
        (volume.prod volume) := by
      apply Continuous.aestronglyMeasurable
      unfold regularizedGaussian finDotProduct euclidNormSq
      fun_prop
    exact this.integral_prod_right'
  · exact (hφ_smooth.continuous).aestronglyMeasurable

/-- Inverse Fourier transform expressed via the forward transform at $-z$:
$f^\vee(z) = \hat f(-z)$. This is the standard symmetry used to reduce inverse-transform
estimates to forward-transform results. -/
lemma inverseFourierTransformFin_eq_fourierTransformND_neg {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (z : Fin n → ℝ) :
    inverseFourierTransformFin f z = CM16.fourierTransformND n f (-z) := by
  simp only [inverseFourierTransformFin, CM16.fourierTransformND, finDotProduct]
  congr 1; ext ξ; congr 2
  simp only [Pi.neg_apply]
  have : ∑ j, (-z j) * ξ j = -(∑ j, ξ j * z j) := by
    simp [mul_comm, Finset.sum_neg_distrib]
  rw [this]; push_cast; ring

/-- The complex-scaled Gaussian $x \mapsto \exp(-\pi z |x|^2)$ for $z \in \mathbb{C}$ with
$\operatorname{Re} z > 0$. -/
def scaledGaussian (n : ℕ) (z : ℂ) (x : Fin n → ℝ) : ℂ :=
  exp (-(↑Real.pi * z * ↑(CM16.euclidNormSq x)))

/-- Fourier transform of the complex-scaled Gaussian (Proposition 3.0.3 of CM16, in `scaledGaussian`
form): for $\operatorname{Re} z > 0$ and $\operatorname{Im} z \neq 0$,
$$\widehat{\exp(-\pi z |\cdot|^2)}(\xi) = z^{-n/2}\, \exp(-\pi |\xi|^2 / z).$$ -/
lemma fourier_scaledGaussian_complex {n : ℕ} (z : ℂ) (hz : 0 < z.re) (him : z.im ≠ 0)
    (ξ : Fin n → ℝ) :
    CM16.fourierTransformND n (scaledGaussian n z) ξ =
    z ^ (-(n : ℂ) / 2) * exp (-(↑Real.pi * ↑(CM16.euclidNormSq ξ) / z)) := by
  have h_eq : scaledGaussian n z = fun x => exp (↑(-Real.pi) * z * ↑(CM16.euclidNormSq x)) := by
    ext x; simp only [scaledGaussian]; congr 1; push_cast; ring
  rw [h_eq, CM16.fourier_gaussian_complex z hz him]
  congr 1; push_cast; ring

/-- Uniform $L^\infty$ bound on $g_\delta^\vee(t, \cdot)$ in $\delta > 0$ and $z \in \mathbb{R}^n$:
there exists $C > 0$ (depending on $n, t$) with $\|g_\delta^\vee(t, z)\| \le C$ for all
$\delta > 0$. One may take $C = (2\pi t)^{-n/2}$. -/
lemma norm_inverseFT_regularizedGaussian_uniform_bound {n : ℕ} (t : ℝ) (ht : 0 < t) :
    ∃ (C : ℝ), ∀ (δ : ℝ), 0 < δ → ∀ (z : Fin n → ℝ),
      ‖inverseFourierTransformFin (regularizedGaussian n δ t) z‖ ≤ C := by
  have hB : 0 < 2 * Real.pi * t := by positivity
  use (2 * Real.pi * t) ^ (-(n : ℝ) / 2)
  intro δ hδ z

  rw [inverseFourierTransformFin_eq_fourierTransformND_neg]

  have hw_re : 0 < (2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ).re := by
    simp only [mul_re, ofReal_re, ofReal_im, add_re, I_re, add_im, I_im, mul_one, mul_zero,
               sub_zero, add_zero, zero_add]; norm_num; positivity
  have hw_ne : (2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ) ≠ 0 :=
    ne_of_apply_ne re (ne_of_gt hw_re)
  have hw_im : (2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ).im ≠ 0 := by
    simp only [mul_im, ofReal_re, ofReal_im, add_im, I_im, add_re, I_re, mul_one, mul_zero,
               add_zero, zero_add]; norm_num
    exact ne_of_gt (by positivity)

  have h_eq : regularizedGaussian n δ t = scaledGaussian n (2 * ↑Real.pi * (↑δ + I) * ↑t) := by
    ext ξ; simp only [regularizedGaussian, scaledGaussian, euclidNormSq, CM16.euclidNormSq]
    congr 1; push_cast; ring

  rw [h_eq, fourier_scaledGaussian_complex _ hw_re hw_im, norm_mul]

  have h_exp : ‖cexp (-(↑Real.pi * ↑(CM16.euclidNormSq fun i => -z i) /
      (2 * ↑Real.pi * (↑δ + I) * ↑t)))‖ ≤ 1 := by
    rw [norm_exp]; apply Real.exp_le_one_iff.mpr
    simp only [neg_re, div_re, ofReal_re, ofReal_im, mul_re, mul_im, mul_zero, sub_zero,
               zero_mul, add_zero, zero_div, add_zero, add_re, I_re, add_im, I_im]; norm_num
    have h1 : (0 : ℝ) ≤ CM16.euclidNormSq fun i => -z i :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have h2 : (0 : ℝ) ≤ normSq (↑δ + I : ℂ) := normSq_nonneg _
    have h3 := Real.pi_pos; positivity

  have h_pow : ‖(2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ) ^ (-(↑n : ℂ) / 2)‖ ≤
      (2 * Real.pi * t) ^ (-(n : ℝ) / 2) := by
    rw [show (-(↑n : ℂ) / 2 : ℂ) = ((-(n : ℝ) / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show ‖(2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ) ^ ((-(n : ℝ) / 2 : ℝ) : ℂ)‖ =
        ‖(2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ)‖ ^ (-(n : ℝ) / 2) from by
      rw [(cpow_def_of_ne_zero hw_ne _), norm_exp]
      simp only [mul_re, log_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [← Real.rpow_def_of_pos (norm_pos_iff.mpr hw_ne)]]
    apply Real.rpow_le_rpow_of_nonpos hB
    ·
      rw [show (2 * ↑Real.pi * (↑δ + I) * ↑t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * (↑δ + I) from by
        push_cast; ring]
      rw [norm_mul, norm_real, Real.norm_of_nonneg hB.le]
      calc 2 * Real.pi * t = (2 * Real.pi * t) * 1 := (mul_one _).symm
        _ ≤ (2 * Real.pi * t) * ‖(↑δ + I : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_left _ hB.le
          rw [norm_def]
          rw [show normSq (↑δ + I : ℂ) = δ ^ 2 + 1 from by simp [normSq, sq]]
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg δ))
    · linarith [show (0 : ℝ) ≤ (n : ℝ) from by positivity]

  calc _ ≤ (2 * Real.pi * t) ^ (-(n : ℝ) / 2) * 1 :=
        mul_le_mul h_pow h_exp (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- Localized form of the uniform bound: for any compact set $K \subset \mathbb{R}^n$ there
exists a uniform constant $C$ and a threshold $\delta_0 > 0$ such that $g_\delta^\vee(t, z)$ is
bounded by $C$ for all $\delta \in (0, \delta_0)$ and $z \in K$. -/
lemma uniform_bound_regularized_kernel_on_compact {n : ℕ}
    (t : ℝ) (ht : 0 < t) (K : Set (Fin n → ℝ)) (hK : IsCompact K) :
    ∃ (C : ℝ) (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ δ ∈ Set.Ioo 0 δ₀, ∀ z ∈ K,
        ‖inverseFourierTransformFin (regularizedGaussian n δ t) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := norm_inverseFT_regularizedGaussian_uniform_bound t ht (n := n)
  exact ⟨C, 1, one_pos, fun δ hδ z _ => hC δ hδ.1 z⟩

/-- Integrable dominating function for the convolution integrand: for $\phi \in
C_c^\infty(\mathbb{R}^n)$ there is an integrable function $\text{bound}(y) = |C| \cdot \|\phi(y)\|$
such that eventually in $\delta \downarrow 0$,
$\|g_\delta^\vee(t, x - y)\,\phi(y)\| \le \text{bound}(y)$ almost everywhere in $y$. This is the
hypothesis required for dominated convergence under the integral. -/
theorem uniform_bound_regularized_integrand {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    ∃ (bound : (Fin n → ℝ) → ℝ),
      Integrable bound volume ∧
      ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
          ‖inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y‖ ≤ bound y := by

  have hK : IsCompact ((fun y => x - y) '' tsupport φ) :=
    hφ_supp.isCompact.image (continuous_const.sub continuous_id)

  obtain ⟨C, δ₀, hδ₀, hunif⟩ := uniform_bound_regularized_kernel_on_compact t ht _ hK

  refine ⟨fun y => |C| * ‖φ y‖, ?_, ?_⟩
  ·
    exact ((hφ_smooth.continuous.norm).integrable_of_hasCompactSupport hφ_supp.norm).const_mul |C|
  ·
    apply Filter.Eventually.mono (Ioo_mem_nhdsGT hδ₀)
    intro δ hδ
    apply ae_of_all
    intro y
    rw [norm_mul]
    by_cases hy : y ∈ tsupport φ
    ·
      have hxy : x - y ∈ (fun y => x - y) '' tsupport φ := ⟨y, hy, rfl⟩
      calc ‖inverseFourierTransformFin (regularizedGaussian n δ t) (x - y)‖ * ‖φ y‖
          ≤ C * ‖φ y‖ := mul_le_mul_of_nonneg_right (hunif δ hδ _ hxy) (norm_nonneg _)
        _ ≤ |C| * ‖φ y‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    ·
      rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, mul_zero]
      exact mul_nonneg (abs_nonneg C) (norm_nonneg _)

/-- Dominated convergence for the convolution: as $\delta \downarrow 0$,
$$\int g_\delta^\vee(t, x - y)\,\phi(y)\, d^n y \longrightarrow
  \int K(t, x - y)\,\phi(y)\, d^n y = (K(t, \cdot) * \phi)(x).$$ -/
theorem dominated_convergence_convolution {n : ℕ}
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    Filter.limUnder (nhdsWithin 0 (Set.Ioi 0))
      (fun δ => ∫ y : Fin n → ℝ,
        inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y) =
    schrodingerConvolution n φ t x := by

  obtain ⟨bound, hbound_int, hbound⟩ :=
    uniform_bound_regularized_integrand φ hφ_smooth hφ_supp t ht x

  have h_ptwise : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      Filter.Tendsto
        (fun δ => inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (schrodingerKernel n t (x - y) * φ y)) := by
    apply Filter.Eventually.of_forall
    intro y
    exact (pointwise_limit_regularized_kernel t ht (x - y)).mul tendsto_const_nhds

  have h_meas : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable
        (fun y => inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y)
        volume := by
    apply eventually_nhdsWithin_of_forall
    intro δ hδ
    exact ae_strongly_measurable_regularized_integrand φ hφ_smooth hφ_supp t ht x δ hδ

  have h_tendsto := tendsto_integral_filter_of_dominated_convergence
    bound h_meas hbound hbound_int h_ptwise

  exact h_tendsto.limUnder_eq

/-- Proposition 2.0.1 (Calculation of the fundamental solution $K(t, x)$ for Schrödinger's
equation): for $\phi \in C_c^\infty(\mathbb{R}^n)$ and $t > 0$, the function $\psi$ defined by
$\hat\psi(t, \xi) = \hat K(t, \xi)\,\hat\phi(\xi)$ admits the convolution representation
$$\psi(t, x) = (K(t, \cdot) * \phi)(x) = \int K(t, x - y)\,\phi(y)\, d^n y,$$
where $K(t, x) = (2\pi i t)^{-n/2}\, e^{i|x|^2/(2t)}$. The proof passes through the regularized
Gaussian $g_\delta$ and takes the limit $\delta \downarrow 0$. -/
theorem proposition_2_0_1_convolution_representation (n : ℕ)
    (φ : (Fin n → ℝ) → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    inverseFourierTransformFin (schrodingerSolutionFT n φ t) x =
    schrodingerConvolution n φ t x := by


  rw [regularization_limit φ hφ_smooth hφ_supp t ht x]


  have h_conv : ∀ δ > 0,
      inverseFourierTransformFin
        (fun ξ => regularizedGaussian n δ t ξ * fourierTransformFin φ ξ) x =
      ∫ y : Fin n → ℝ,
        inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y :=
    fun δ hδ => convolution_via_FT_inversion φ hφ_smooth hφ_supp δ hδ t ht x

  have h_lim_eq : Filter.limUnder (nhdsWithin 0 (Set.Ioi 0))
      (fun δ => inverseFourierTransformFin
        (fun ξ => regularizedGaussian n δ t ξ * fourierTransformFin φ ξ) x) =
    Filter.limUnder (nhdsWithin 0 (Set.Ioi 0))
      (fun δ => ∫ y : Fin n → ℝ,
        inverseFourierTransformFin (regularizedGaussian n δ t) (x - y) * φ y) := by
    unfold Filter.limUnder
    congr 1
    exact Filter.map_congr (eventually_nhdsWithin_of_forall
      (fun δ (hδ : δ ∈ Set.Ioi 0) => h_conv δ hδ))
  rw [h_lim_eq]


  exact dominated_convergence_convolution φ hφ_smooth hφ_supp t ht x
