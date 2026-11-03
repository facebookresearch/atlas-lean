/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Real Set MeasureTheory

noncomputable section

namespace CM18

/-- Spacetime $\mathbb{R}^{1+n}$ modeled as functions $\text{Fin}(n+1) \to \mathbb{R}$.
The component indexed by $0$ is time and components $1, \ldots, n$ are spatial. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $(1+n)$-dimensional spacetime. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A Lagrangian (Definition 1.0.1) is a function of the field value $\phi \in \mathbb{R}$,
its spacetime gradient $\nabla\phi \in \mathbb{R}^{1+n}$, and the spacetime coordinate $x$.
We write $\mathcal{L}(\phi, \nabla\phi, x)$. -/
def Lagrangian (n : ℕ) := ℝ → (Fin (n + 1) → ℝ) → Spacetime n → ℝ

/-- The spacetime gradient $\nabla\phi$ of a scalar field $\phi$ at $x$, given by the components
$(\nabla\phi)_\mu = \partial_\mu \phi(x) = (D\phi)_x(e_\mu)$ where $e_\mu$ is the $\mu$-th
coordinate vector. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) : Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- The action (Definition 1.0.2) of a field $\phi$ over a compact set $\mathfrak{K} \subset
\mathbb{R}^{1+n}$:
$$\mathcal{A}[\phi; \mathfrak{K}] = \int_{\mathfrak{K}} \mathcal{L}(\phi(x), \nabla\phi(x), x)\,
d^{1+n}x.$$ -/
def action {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (K : Set (Spacetime n)) : ℝ :=
  ∫ x in K, L (φ x) (spacetimeGradient φ x) x

/-- A variation (Definition 1.0.3) on a set $K$ is a smooth scalar field $\psi$ whose support
is contained in $K$; equivalently $\psi \in C_c^\infty(K)$. -/
def IsVariation {n : ℕ} (K : Set (Spacetime n)) (ψ : ScalarField n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.support ψ ⊆ K

/-- The perturbed field (Definition 1.0.4) $\phi_\varepsilon := \phi + \varepsilon\psi$. -/
def perturbedField {n : ℕ} (φ ψ : ScalarField n) (ε : ℝ) : ScalarField n :=
  fun x => φ x + ε * ψ x

/-- $\phi$ is a stationary point of the action (Definition 1.0.5) iff for every compact set
$\mathfrak{K}$ and every variation $\psi \in C_c^\infty(\mathfrak{K})$,
$$\left.\frac{d}{d\varepsilon}\right|_{\varepsilon=0} \mathcal{A}[\phi_\varepsilon;
\mathfrak{K}] = 0.$$ -/
def IsStationaryPoint {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) : Prop :=
  ∀ (K : Set (Spacetime n)) (_hK : IsCompact K) (ψ : ScalarField n),
    IsVariation K ψ →
      deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 = 0

/-- The partial derivative $\partial\mathcal{L}/\partial\phi$ evaluated at $(\phi(x),
\nabla\phi(x), x)$. -/
def dL_dφ {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (x : Spacetime n) : ℝ :=
  deriv (fun v => L v (spacetimeGradient φ x) x) (φ x)

/-- The partial derivative $\partial\mathcal{L}/\partial(\nabla_\alpha\phi)$ evaluated at
$(\phi(x), \nabla\phi(x), x)$, holding the other gradient components, $\phi$, and $x$ fixed. -/
def dL_dgrad {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) (α : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun p => L (φ x) p x) (spacetimeGradient φ x) (Pi.single α 1)

/-- The Euler-Lagrange operator
$$E[\phi](x) = \frac{\partial\mathcal{L}}{\partial\phi} - \sum_\alpha \nabla_\alpha\left(
\frac{\partial\mathcal{L}}{\partial(\nabla_\alpha\phi)}\right).$$
The Euler-Lagrange PDE (Theorem 1.1) is $E[\phi] = 0$. -/
def eulerLagrangeOperator {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) : ℝ :=
  dL_dφ L φ x - ∑ α : Fin (n + 1),
    fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1)

/-- Fundamental lemma of the calculus of variations: if $f$ is continuous and $\int_K f\psi = 0$
for every compact $K$ and every variation $\psi \in C_c^\infty(K)$, then $f \equiv 0$. -/
theorem ibp_fundamental_lemma {n : ℕ}
    (f : Spacetime n → ℝ) (hcont : Continuous f)
    (hf : ∀ (K : Set (Spacetime n)), IsCompact K →
      ∀ (ψ : ScalarField n), IsVariation K ψ →
        ∫ x in K, f x * ψ x = 0) :
    ∀ x : Spacetime n, f x = 0 := by
  have hli : LocallyIntegrable f volume := hcont.locallyIntegrable


  have hsmul : ∀ (g : Spacetime n → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) g → HasCompactSupport g →
      ∫ x, g x • f x = 0 := by
    intro g hg hsupp
    have hK : IsCompact (tsupport g) := hsupp
    have hvar : IsVariation (tsupport g) g := ⟨hg, subset_tsupport g⟩
    have h := hf (tsupport g) hK g hvar
    simp only [smul_eq_mul]
    have hzero : ∀ x, x ∉ tsupport g → g x * f x = 0 := by
      intro x hx
      have : x ∉ Function.support g := fun hs => hx (subset_tsupport g hs)
      rw [Function.notMem_support.mp this, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp_rw [show ∀ x, g x * f x = f x * g x from fun x => mul_comm (g x) (f x)]
    exact h

  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli hsmul


  have heq : f = 0 := Measure.eq_of_ae_eq hae hcont continuous_const
  exact fun x => congr_fun heq x

/-- Pointwise chain rule at $\varepsilon = 0$ for the integrand of the action: the derivative
in $\varepsilon$ of $\mathcal{L}(\phi_\varepsilon(x), \nabla\phi_\varepsilon(x), x)$ at
$\varepsilon=0$ equals
$\frac{\partial\mathcal{L}}{\partial\phi}\psi + \sum_\alpha
\frac{\partial\mathcal{L}}{\partial(\nabla_\alpha\phi)} \nabla_\alpha\psi$. -/
lemma pointwise_chain_rule {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (x : Spacetime n)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasDerivAt (fun ε => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x)
      (dL_dφ L φ x * ψ x +
        ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α) 0 := by

  have hφ_da : DifferentiableAt ℝ φ x :=
    (hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by norm_num) |>.differentiableAt
  have hψ_da : DifferentiableAt ℝ ψ x :=
    hψ.differentiable (by simp) |>.differentiableAt

  have h_grad_eq : ∀ ε, spacetimeGradient (perturbedField φ ψ ε) x =
      fun μ => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ := by
    intro ε; ext μ; simp only [spacetimeGradient]
    have hd : HasFDerivAt (perturbedField φ ψ ε) (fderiv ℝ φ x + ε • fderiv ℝ ψ x) x := by
      show HasFDerivAt (fun y => φ y + ε * ψ y) _ x
      exact hφ_da.hasFDerivAt.add (hψ_da.hasFDerivAt.const_smul ε)
    rw [hd.fderiv]; simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [show (fun ε => L (φ x + ε * ψ x) (spacetimeGradient (perturbedField φ ψ ε) x) x) =
      (fun ε => L (φ x + ε * ψ x)
        (fun μ => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ) x) from by
    ext ε; rw [h_grad_eq]]

  set a₀ := φ x; set b₀ := spacetimeGradient φ x
  set da := ψ x; set db := spacetimeGradient ψ x
  set G : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun q => L q.1 q.2 x with hG_def
  have hG_smooth : ContDiff ℝ 2 G := by
    show ContDiff ℝ 2 ((fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n => L p.1 p.2.1 p.2.2) ∘
        (fun q : ℝ × (Fin (n + 1) → ℝ) => (q.1, q.2, x)))
    exact hL.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hG_diff : DifferentiableAt ℝ G (a₀, b₀) :=
    (hG_smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable
      (by norm_num) |>.differentiableAt

  have h_path : HasDerivAt (fun ε => (a₀ + ε * da, fun μ : Fin (n+1) => b₀ μ + ε * db μ))
      ((da, db) : ℝ × (Fin (n + 1) → ℝ)) 0 :=
    ((by convert (hasDerivAt_const 0 a₀).add (hasDerivAt_mul_const da) using 1; ring :
      HasDerivAt (fun ε => a₀ + ε * da) da 0).prodMk
      (hasDerivAt_pi.mpr fun μ => by
        convert (hasDerivAt_const 0 (b₀ μ)).add (hasDerivAt_mul_const (db μ)) using 1; ring))

  have h_chain : HasDerivAt (fun ε => G (a₀ + ε * da, fun μ => b₀ μ + ε * db μ))
      (fderiv ℝ G (a₀, b₀) (da, db)) 0 := by
    have hpv : (fun ε => (a₀ + ε * da, fun μ : Fin (n+1) => b₀ μ + ε * db μ)) 0 = (a₀, b₀) := by
      simp [mul_comm]
    have : HasFDerivAt G (fderiv ℝ G (a₀, b₀))
        ((fun ε => (a₀ + ε * da, fun μ : Fin (n+1) => b₀ μ + ε * db μ)) 0) := by
      rw [hpv]; exact hG_diff.hasFDerivAt
    exact this.comp_hasDerivAt 0 h_path

  have h_partial1 : HasFDerivAt (fun v : ℝ => G (v, b₀))
      ((fderiv ℝ G (a₀, b₀)).comp (ContinuousLinearMap.inl ℝ ℝ (Fin (n+1) → ℝ))) a₀ := by
    rw [show (fun v : ℝ => G (v, b₀)) = G ∘ (fun v => (v, b₀)) from rfl]
    exact hG_diff.hasFDerivAt.comp a₀ (hasFDerivAt_prodMk_left a₀ b₀)
  have h_partial2 : HasFDerivAt (fun p : Fin (n+1) → ℝ => G (a₀, p))
      ((fderiv ℝ G (a₀, b₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin (n+1) → ℝ))) b₀ := by
    rw [show (fun p : Fin (n+1) → ℝ => G (a₀, p)) = G ∘ (fun p => (a₀, p)) from rfl]
    exact hG_diff.hasFDerivAt.comp b₀ (hasFDerivAt_prodMk_right a₀ b₀)
  have h_decomp : fderiv ℝ G (a₀, b₀) (da, db) =
      fderiv ℝ (fun v => G (v, b₀)) a₀ da + fderiv ℝ (fun p => G (a₀, p)) b₀ db := by
    rw [h_partial1.fderiv, h_partial2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    rw [show (da, db) = (da, (0 : Fin (n+1) → ℝ)) + ((0 : ℝ), db) from by simp [Prod.mk_add_mk]]
    exact map_add _ _ _

  have h_term1 : fderiv ℝ (fun v => G (v, b₀)) a₀ da = dL_dφ L φ x * ψ x := by
    calc fderiv ℝ (fun v => G (v, b₀)) a₀ da
        = fderiv ℝ (fun v => G (v, b₀)) a₀ (da • 1) := by rw [smul_eq_mul, mul_one]
      _ = da • fderiv ℝ (fun v => G (v, b₀)) a₀ 1 := by rw [map_smul]
      _ = da * deriv (fun v => G (v, b₀)) a₀ := by rw [smul_eq_mul, fderiv_apply_one_eq_deriv]
      _ = dL_dφ L φ x * ψ x := by rw [mul_comm]; rfl

  have h_term2 : fderiv ℝ (fun p => G (a₀, p)) b₀ db =
      ∑ α, dL_dgrad L φ x α * spacetimeGradient ψ x α := by
    conv_lhs =>
      rw [show db = ∑ i : Fin (n+1), db i • (Pi.single i (1 : ℝ) : Fin (n+1) → ℝ) from by
        ext j; simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]]
    simp only [map_sum, map_smul, smul_eq_mul]
    congr 1; ext α; rw [mul_comm]; rfl

  rw [h_decomp, h_term1, h_term2] at h_chain
  exact h_chain

/-- General pointwise chain rule at an arbitrary base point $\varepsilon_0$: gives a closed-form
expression for $\frac{d}{d\varepsilon} \mathcal{L}(\phi_\varepsilon(x), \nabla\phi_\varepsilon(x),
x)$ at any $\varepsilon = \varepsilon_0$ in terms of the full Fréchet derivative of $\mathcal{L}$.
Used to dominate the difference quotient when differentiating under the integral sign. -/
lemma general_chain_rule_all_eps {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (x : Spacetime n) (ε₀ : ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    HasDerivAt (fun ε => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x)
      (fderiv ℝ (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n => L p.1 p.2.1 p.2.2)
        (φ x + ε₀ * ψ x, fun μ => spacetimeGradient φ x μ + ε₀ * spacetimeGradient ψ x μ, x)
        (ψ x, spacetimeGradient ψ x, 0))
      ε₀ := by


  have h_grad_eq : ∀ ε, spacetimeGradient (perturbedField φ ψ ε) x =
      fun μ => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ := by
    intro ε; ext μ; simp only [spacetimeGradient]
    show (fderiv ℝ (perturbedField φ ψ ε) x) (Pi.single μ 1) =
      (fderiv ℝ φ x) (Pi.single μ 1) + ε * (fderiv ℝ ψ x) (Pi.single μ 1)
    have hd : HasFDerivAt (perturbedField φ ψ ε) (fderiv ℝ φ x + ε • fderiv ℝ ψ x) x := by
      show HasFDerivAt (fun y => φ y + ε * ψ y) _ x
      exact hφ.hasFDerivAt.add (hψ.hasFDerivAt.const_smul ε)
    rw [hd.fderiv]; simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  have h_eq : (fun ε => L (φ x + ε * ψ x) (spacetimeGradient (perturbedField φ ψ ε) x) x) =
      (fun ε => L (φ x + ε * ψ x)
        (fun μ => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ) x) := by
    ext ε; rw [h_grad_eq]
  rw [h_eq]

  have h_path : HasDerivAt
      (fun ε => (φ x + ε * ψ x,
        fun μ : Fin (n+1) => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ, x))
      ((ψ x, spacetimeGradient ψ x, (0 : Spacetime n)) :
        ℝ × (Fin (n+1) → ℝ) × Spacetime n) ε₀ := by
    exact ((by convert (hasDerivAt_const ε₀ (φ x)).add (hasDerivAt_mul_const (ψ x))
      using 1; ring : HasDerivAt (fun ε => φ x + ε * ψ x) (ψ x) ε₀).prodMk
      ((hasDerivAt_pi.mpr fun μ => by
        convert (hasDerivAt_const ε₀ (spacetimeGradient φ x μ)).add
          (hasDerivAt_mul_const (spacetimeGradient ψ x μ)) using 1; ring).prodMk
        (hasDerivAt_const ε₀ x)))

  exact ((hL.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by norm_num)
    |>.differentiableAt).hasFDerivAt.comp_hasDerivAt ε₀ h_path

/-- Differentiation under the integral sign (Leibniz rule) applied to the action: for smooth
data,
$$\left.\frac{d}{d\varepsilon}\right|_{\varepsilon=0} \mathcal{A}[\phi_\varepsilon; K] =
\int_K \left(\frac{\partial\mathcal{L}}{\partial\phi}\,\psi + \sum_\alpha
\frac{\partial\mathcal{L}}{\partial(\nabla_\alpha\phi)}\,\nabla_\alpha\psi\right) d^{1+n}x.$$ -/
theorem leibniz_chain_rule {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 =
      ∫ x in K, (dL_dφ L φ x * ψ x +
        ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α) := by

  have hφ_da : ∀ x : Spacetime n, DifferentiableAt ℝ φ x :=
    fun x => (hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable
      (by norm_num) |>.differentiableAt
  have hψ_da : ∀ x : Spacetime n, DifferentiableAt ℝ ψ x :=
    fun x => hψ.differentiable (by simp) |>.differentiableAt
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)

  let F' : ℝ → Spacetime n → ℝ := fun ε x =>
    fderiv ℝ (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n => L p.1 p.2.1 p.2.2)
      (φ x + ε * ψ x,
       fun μ => spacetimeGradient φ x μ + ε * spacetimeGradient ψ x μ, x)
      (ψ x, spacetimeGradient ψ x, 0)

  have h_all : ∀ x : Spacetime n, ∀ ε : ℝ,
      HasDerivAt (fun ε => L (φ x + ε * ψ x)
        (spacetimeGradient (perturbedField φ ψ ε) x) x) (F' ε x) ε :=
    fun x ε => general_chain_rule_all_eps L φ ψ x ε hL (hφ_da x) (hψ_da x)


  have h_at_zero : ∀ x : Spacetime n,
      F' 0 x = dL_dφ L φ x * ψ x +
        ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α :=
    fun x => (h_all x 0).unique (pointwise_chain_rule L φ ψ x hL hφ hψ)


  let μ := (volume : Measure (Spacetime n)).restrict K
  haveI hfm : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_restrict]; exact hK.measure_lt_top.ne

  have h_fderiv_cont :=
    (hL.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv (by norm_num)
  have h_grad_ψ : ∀ α : Fin (n + 1), Continuous (fun x =>
      (fderiv ℝ ψ x) (Pi.single α 1)) :=
    fun α => ((hψ2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  have h_grad_φ : ∀ α : Fin (n + 1), Continuous (fun x =>
      (fderiv ℝ φ x) (Pi.single α 1)) :=
    fun α => ((hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const


  have h_F'_joint : Continuous (fun (p : ℝ × Spacetime n) => F' p.1 p.2) :=
    (h_fderiv_cont.comp
      (Continuous.prodMk ((hφ.continuous.comp continuous_snd).add
        (continuous_fst.mul (hψ2.continuous.comp continuous_snd)))
        (Continuous.prodMk (continuous_pi fun α => (h_grad_φ α).comp continuous_snd |>.add
          (continuous_fst.mul ((h_grad_ψ α).comp continuous_snd))) continuous_snd))).clm_apply
      (Continuous.prodMk (hψ2.continuous.comp continuous_snd)
        (Continuous.prodMk (continuous_pi fun α => (h_grad_ψ α).comp continuous_snd)
          continuous_const))

  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (f := fun p => F' p.1 p.2) h_F'_joint.continuousOn

  have h_cont_F : ∀ ε : ℝ, Continuous (fun x => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x) := by
    intro ε
    have hpe : ContDiff ℝ 2 (perturbedField φ ψ ε) :=
      show ContDiff ℝ 2 (fun x => φ x + ε * ψ x) from
      hφ.add (contDiff_const.mul hψ2)
    change Continuous (fun x => L ((perturbedField φ ψ ε) x)
      (fun μ => fderiv ℝ (perturbedField φ ψ ε) x (Pi.single μ 1)) x)
    exact hL.continuous.comp (Continuous.prodMk hpe.continuous
      ((continuous_pi fun α =>
        ((hpe.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv
          (by norm_num)).clm_apply continuous_const).prodMk continuous_id))

  have hleibniz := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε x => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x)
    (F' := F') (x₀ := (0 : ℝ)) (μ := μ) (bound := fun _ => C)
    (s := Set.Ioo (-1) 1)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (by
      apply Filter.Eventually.of_forall; intro ε
      exact (h_cont_F ε).aestronglyMeasurable.restrict)
    (by
      exact (h_cont_F 0).continuousOn.integrableOn_compact hK)
    (by
      have : Continuous (fun x => F' 0 x) :=
        h_F'_joint.comp (Continuous.prodMk continuous_const continuous_id)
      exact this.aestronglyMeasurable.restrict)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK ε hε
      exact hC (ε, x) ⟨Ioo_subset_Icc_self hε, hxK⟩)
    (by
      exact integrable_const C)
    (by filter_upwards with x; intro ε _; exact h_all x ε)

  have hda := hleibniz.2


  show deriv (fun ε => ∫ x in K, L ((perturbedField φ ψ ε) x)
    (spacetimeGradient (perturbedField φ ψ ε) x) x) 0 = _
  rw [show (fun ε => ∫ x in K, L ((perturbedField φ ψ ε) x)
    (spacetimeGradient (perturbedField φ ψ ε) x) x) =
    (fun ε => ∫ x, (fun ε x => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x) ε x ∂μ)
    from by ext ε; simp [μ, perturbedField]]
  rw [hda.deriv]
  congr 1; ext x
  exact h_at_zero x









end CM18
