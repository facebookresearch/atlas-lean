/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Finset Classical

noncomputable section

namespace CM14

/-- The squared Euclidean norm $\sum_i x_i^2$ of a vector $x \in \mathbb{R}^n$. -/
def waveEuclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The $1+n$-dimensional Minkowski spacetime $\mathbb{R} \times \mathbb{R}^n$, with the first
factor interpreted as time. -/
abbrev WaveSpacetime (n : ℕ) := ℝ × (Fin n → ℝ)

/-- A scalar field on spacetime: a function $\phi : \mathbb{R}^{1+n} \to \mathbb{R}$. -/
abbrev WaveScalarField (n : ℕ) := WaveSpacetime n → ℝ

/-- A spacetime vector field: a function $X$ assigning to each $p \in \mathbb{R}^{1+n}$ a vector
$X(p) \in \mathbb{R}^{n+1}$ indexed by spacetime indices. -/
abbrev SpacetimeVectorField (n : ℕ) := WaveSpacetime n → Fin (n + 1) → ℝ

/-- The linear wave operator $\square_m \phi = -\partial_t^2 \phi + \sum_{i=1}^n \partial_i^2 \phi$
applied to a scalar field $\phi$ at the point $p$. -/
noncomputable def waveOp {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n) : ℝ :=
  -(fderiv ℝ (fun s => fderiv ℝ (fun r => φ (r, p.2)) s 1) p.1 1) +
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => φ (p.1, z)) y (Pi.single i 1)) p.2 (Pi.single i 1)

/-- The partial derivative $\partial_\mu \phi(p)$ of a scalar field $\phi$ in the $\mu$-th
spacetime direction at $p$. The index $\mu = 0$ corresponds to the time derivative, and
$\mu = 1, \dots, n$ correspond to spatial derivatives. -/
noncomputable def partialDeriv {n : ℕ} (φ : WaveScalarField n) (μ : Fin (n + 1))
    (p : WaveSpacetime n) : ℝ :=
  if h : μ.val = 0 then
    fderiv ℝ (fun s => φ (s, p.2)) p.1 1
  else
    let i : Fin n := ⟨μ.val - 1, by omega⟩
    fderiv ℝ (fun y => φ (p.1, y)) p.2 (Pi.single i 1)

/-- The standard basis direction in spacetime corresponding to index $\mu$:
$e_0 = (1, 0)$ is the time direction, and $e_\mu = (0, \mathbf{e}_{\mu - 1})$ for $\mu \geq 1$. -/
def basisDir {n : ℕ} (μ : Fin (n + 1)) : ℝ × (Fin n → ℝ) :=
  if h : μ.val = 0 then (1, 0)
  else (0, Pi.single ⟨μ.val - 1, by omega⟩ 1)

/-- For a field differentiable at $p$, the coordinate partial derivative
$\partial_\mu \phi(p)$ equals the Fréchet derivative applied to the basis direction
$e_\mu$. -/
lemma partialDeriv_eq_fderiv {n : ℕ} (φ : WaveScalarField n) {p : WaveSpacetime n}
    (hφ : DifferentiableAt ℝ φ p) (μ : Fin (n + 1)) :
    partialDeriv φ μ p = fderiv ℝ φ p (basisDir μ) := by
  simp only [partialDeriv, basisDir]
  split_ifs with h
  · have hcomp : HasFDerivAt (fun s => φ (s, p.2))
        (fderiv ℝ φ p ∘L ContinuousLinearMap.inl ℝ ℝ (Fin n → ℝ)) p.1 :=
      hφ.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
    rw [hcomp.fderiv]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  · have hcomp : HasFDerivAt (fun y => φ (p.1, y))
        (fderiv ℝ φ p ∘L ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) p.2 :=
      hφ.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
    rw [hcomp.fderiv]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The Minkowski metric $m_{\mu\nu} = \operatorname{diag}(-1, 1, \dots, 1)$ on
$\mathbb{R}^{1+n}$, with mostly-plus signature. -/
def waveMinkowskiMetric (n : ℕ) (μ ν : Fin (n + 1)) : ℝ :=
  if μ = ν then (if μ.val = 0 then -1 else 1) else 0

/-- The inverse Minkowski metric $(m^{-1})^{\mu\nu}$. In the standard basis this coincides
with $m_{\mu\nu}$ since the metric is diagonal with entries $\pm 1$. -/
def minkowskiInverse (n : ℕ) (μ ν : Fin (n + 1)) : ℝ :=
  waveMinkowskiMetric n μ ν

/-- The Minkowski inner product $m(X, Y) = m_{\alpha\beta} X^\alpha Y^\beta$. -/
def minkowskiProduct {n : ℕ} (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    waveMinkowskiMetric n α β * X α * Y β

/-- A vector $X$ is timelike if $m(X, X) < 0$. -/
def IsTimelike {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X < 0

/-- A vector $X$ is spacelike if $m(X, X) > 0$. -/
def IsSpacelike {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X > 0

/-- A vector $X$ is null (lightlike) if $m(X, X) = 0$. -/
def IsNull {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X = 0

/-- A vector $X$ is causal if it is timelike or null, i.e. $m(X, X) \leq 0$. -/
def IsCausal {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  IsTimelike X ∨ IsNull X

/-- A vector $X$ is future-directed if its time component $X^0$ is positive. -/
def IsFutureDirected {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  X ⟨0, Nat.zero_lt_succ n⟩ > 0

/-- A vector $X$ is past-directed if its time component $X^0$ is negative. -/
def IsPastDirected {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  X ⟨0, Nat.zero_lt_succ n⟩ < 0

/-- A vector $V$ is future causal if it is future-directed and causal, i.e.
$V^0 > 0$ and $m(V, V) \leq 0$. -/
def IsFutureCausal {n : ℕ} (V : Fin (n + 1) → ℝ) : Prop :=
  IsFutureDirected V ∧ minkowskiProduct V V ≤ 0

/-- A vector $V$ is past causal if it is past-directed and causal, i.e.
$V^0 < 0$ and $m(V, V) \leq 0$. -/
def IsPastCausal {n : ℕ} (V : Fin (n + 1) → ℝ) : Prop :=
  IsPastDirected V ∧ minkowskiProduct V V ≤ 0

/-- The energy-momentum tensor of a scalar field $\phi$:
$$T_{\mu\nu} \overset{\text{def}}{=} \partial_\mu \phi \, \partial_\nu \phi
  - \tfrac{1}{2} m_{\mu\nu} (m^{-1})^{\alpha\beta} \partial_\alpha \phi \, \partial_\beta \phi.$$
(Definition 1.0.1.) -/
noncomputable def energyMomentumTensor {n : ℕ} (φ : WaveScalarField n)
    (p : WaveSpacetime n) (μ ν : Fin (n + 1)) : ℝ :=
  partialDeriv φ μ p * partialDeriv φ ν p -
    (1/2 : ℝ) * waveMinkowskiMetric n μ ν *
      ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n α β * partialDeriv φ α p * partialDeriv φ β p

/-- The energy density of a scalar field at a spacetime point:
$\frac{1}{2}\bigl((\partial_t \phi)^2 + |\nabla_x \phi|^2\bigr)$. -/
noncomputable def energyDensity {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n) : ℝ :=
  (1/2 : ℝ) * ((fderiv ℝ (fun s => φ (s, p.2)) p.1 1) ^ 2 +
    ∑ i : Fin n, (fderiv ℝ (fun y => φ (p.1, y)) p.2 (Pi.single i 1)) ^ 2)

/-- The energy of $\phi$ on the ball $B_R(x_0)$ at time $t$:
$\int_{|x - x_0| \leq R} \tfrac{1}{2}(|\partial_t \phi|^2 + |\nabla_x \phi|^2) \, dx$. -/
def energyOnBall {n : ℕ} (φ : WaveScalarField n) (t : ℝ) (x₀ : Fin n → ℝ) (R : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0



/-- The divergence $\partial_\mu T^{\mu\nu}$ of the (twice raised) energy-momentum tensor in
the $\nu$-direction. -/
noncomputable def divEnergyMomentumTensor {n : ℕ} (φ : WaveScalarField n)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) : ℝ :=
  ∑ μ : Fin (n + 1),
    partialDeriv (fun q =>
      ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n ν δ *
          energyMomentumTensor φ q γ δ) μ p

/-- The remainder term in the divergence identity for $T^{\mu\nu}$, defined so that
$\partial_\mu T^{\mu\nu}$ equals $(\square_m \phi)(m^{-1})^{\nu\alpha}\partial_\alpha\phi$
plus this remainder. -/
noncomputable def EMT_remainder {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n)
    (ν : Fin (n + 1)) : ℝ :=
  divEnergyMomentumTensor φ p ν -
    waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p)

/-- Tautological rewriting of $\partial_\mu T^{\mu\nu}$ as the sum of its principal part
$(\square_m \phi)(m^{-1})^{\nu\alpha}\partial_\alpha\phi$ and the remainder
`EMT_remainder`. -/
theorem EMT_product_rule_expansion {n : ℕ} (φ : WaveScalarField n)
    (_hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν =
      waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) +
      EMT_remainder φ p ν := by
  unfold EMT_remainder
  ring

/-- Symmetry of the inverse Minkowski metric: $(m^{-1})^{\mu\nu} = (m^{-1})^{\nu\mu}$. -/
lemma minkowskiInverse_symm (n : ℕ) (μ ν : Fin (n + 1)) :
    minkowskiInverse n μ ν = minkowskiInverse n ν μ := by
  simp only [minkowskiInverse, waveMinkowskiMetric]
  split_ifs with h1 h2 h3 <;> simp_all [eq_comm]

/-- Swap the outer and inner summation indices in a triple sum:
$\sum_\mu \sum_\alpha \sum_\beta f(\mu, \alpha, \beta) = \sum_\mu \sum_\alpha \sum_\beta f(\beta, \alpha, \mu)$. -/
lemma triple_sum_swap_13 {N : ℕ} (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f μ α β =
    ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f β α μ := by
  have step1 : ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f μ α β =
               ∑ α : Fin N, ∑ μ : Fin N, ∑ β : Fin N, f μ α β := Finset.sum_comm
  have step2 : ∑ α : Fin N, ∑ μ : Fin N, ∑ β : Fin N, f μ α β =
               ∑ α : Fin N, ∑ β : Fin N, ∑ μ : Fin N, f μ α β := by
    congr 1; ext α; exact Finset.sum_comm
  have step3 : ∑ α : Fin N, ∑ β : Fin N, ∑ μ : Fin N, f μ α β =
               ∑ β : Fin N, ∑ α : Fin N, ∑ μ : Fin N, f μ α β := Finset.sum_comm
  linarith

/-- Schwarz / Clairaut symmetry of partial derivatives: for $\phi \in C^2$,
$\partial_\mu \partial_\beta \phi = \partial_\beta \partial_\mu \phi$. -/
theorem partialDeriv_schwarz {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (μ β : Fin (n + 1)) (p : WaveSpacetime n) :
    partialDeriv (fun q => partialDeriv φ β q) μ p =
    partialDeriv (fun q => partialDeriv φ μ q) β p := by


  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have heq_β : (fun q => partialDeriv φ β q) = (fun q => fderiv ℝ φ q (basisDir β)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) β
  have heq_μ : (fun q => partialDeriv φ μ q) = (fun q => fderiv ℝ φ q (basisDir μ)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) μ
  rw [heq_β, heq_μ]

  have hDiff_fderiv : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (by norm_num)).differentiable one_ne_zero
  have hDiff_apply_β : Differentiable ℝ (fun q => fderiv ℝ φ q (basisDir β)) :=
    (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).differentiable.comp hDiff_fderiv
  have hDiff_apply_μ : Differentiable ℝ (fun q => fderiv ℝ φ q (basisDir μ)) :=
    (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).differentiable.comp hDiff_fderiv
  rw [partialDeriv_eq_fderiv _ (hDiff_apply_β p) μ,
      partialDeriv_eq_fderiv _ (hDiff_apply_μ p) β]

  have key_β : fderiv ℝ (fun q => fderiv ℝ φ q (basisDir β)) p (basisDir μ) =
      fderiv ℝ (fderiv ℝ φ) p (basisDir μ) (basisDir β) := by
    have h1 : fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ (basisDir β)) ∘ (fderiv ℝ φ)) p =
        (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).comp (fderiv ℝ (fderiv ℝ φ) p) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).hasFDerivAt.comp p
        (hDiff_fderiv p).hasFDerivAt |>.fderiv
    simp only [Function.comp_def] at h1
    rw [show (fun q => fderiv ℝ φ q (basisDir β)) =
            (fun q => (ContinuousLinearMap.apply ℝ ℝ (basisDir β)) (fderiv ℝ φ q)) from rfl, h1]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have key_μ : fderiv ℝ (fun q => fderiv ℝ φ q (basisDir μ)) p (basisDir β) =
      fderiv ℝ (fderiv ℝ φ) p (basisDir β) (basisDir μ) := by
    have h1 : fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ (basisDir μ)) ∘ (fderiv ℝ φ)) p =
        (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).comp (fderiv ℝ (fderiv ℝ φ) p) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).hasFDerivAt.comp p
        (hDiff_fderiv p).hasFDerivAt |>.fderiv
    simp only [Function.comp_def] at h1
    rw [show (fun q => fderiv ℝ φ q (basisDir μ)) =
            (fun q => (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)) (fderiv ℝ φ q)) from rfl, h1]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [key_β, key_μ]

  exact (hφ.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (basisDir μ) (basisDir β)

/-- Leibniz / product rule for the directional partial derivative:
$\partial_\mu(f \cdot g) = (\partial_\mu f) \cdot g + f \cdot (\partial_\mu g)$. -/
theorem partialDeriv_mul {n : ℕ} (f g : WaveScalarField n) (μ : Fin (n + 1))
    (p : WaveSpacetime n) (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    partialDeriv (fun q => f q * g q) μ p =
      partialDeriv f μ p * g p + f p * partialDeriv g μ p := by
  have hfg : DifferentiableAt ℝ (fun q => f q * g q) p := hf.mul hg
  rw [partialDeriv_eq_fderiv _ hfg μ, partialDeriv_eq_fderiv f hf μ, partialDeriv_eq_fderiv g hg μ]
  have hmul : HasFDerivAt (f * g)
      (f p • fderiv ℝ g p + g p • fderiv ℝ f p) p :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [show fderiv ℝ (fun q => f q * g q) p = fderiv ℝ (f * g) p from rfl]
  rw [hmul.fderiv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  ring

/-- Scalar homogeneity of $\partial_\mu$: $\partial_\mu (c \cdot f) = c \cdot \partial_\mu f$. -/
theorem partialDeriv_const_mul {n : ℕ} (c : ℝ) (f : WaveScalarField n) (μ : Fin (n + 1))
    (p : WaveSpacetime n) (hf : DifferentiableAt ℝ f p) :
    partialDeriv (fun q => c * f q) μ p = c * partialDeriv f μ p := by
  have hcf : DifferentiableAt ℝ (fun q => c * f q) p := hf.const_mul c
  rw [partialDeriv_eq_fderiv _ hcf μ, partialDeriv_eq_fderiv f hf μ]
  have hmul : HasFDerivAt (fun q => c * f q) (c • fderiv ℝ f p) p :=
    hf.hasFDerivAt.const_mul c
  rw [hmul.fderiv]
  simp [ContinuousLinearMap.smul_apply]

/-- Linearity of $\partial_\mu$ over a finite sum:
$\partial_\mu \bigl(\sum_{i \in s} f_i\bigr) = \sum_{i \in s} \partial_\mu f_i$. -/
theorem partialDeriv_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → WaveScalarField n) (μ : Fin (n + 1)) (p : WaveSpacetime n)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) p) :
    partialDeriv (fun q => ∑ i ∈ s, f i q) μ p = ∑ i ∈ s, partialDeriv (f i) μ p := by
  rw [partialDeriv_eq_fderiv _ (DifferentiableAt.fun_sum hf) μ,
      fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← partialDeriv_eq_fderiv _ (hf i hi) μ]

/-- Linearity of $\partial_\mu$ under subtraction:
$\partial_\mu(f - g) = \partial_\mu f - \partial_\mu g$. -/
theorem partialDeriv_sub {n : ℕ} (f g : WaveScalarField n) (μ : Fin (n + 1))
    (p : WaveSpacetime n)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    partialDeriv (fun q => f q - g q) μ p = partialDeriv f μ p - partialDeriv g μ p := by
  have heq : (fun q => f q - g q) = f - g := rfl
  rw [heq, partialDeriv_eq_fderiv _ (hf.sub hg) μ, fderiv_sub hf hg,
      ContinuousLinearMap.sub_apply,
      ← partialDeriv_eq_fderiv _ hf μ, ← partialDeriv_eq_fderiv _ hg μ]

/-- Product-rule expansion of the partial derivative of the "potential" scalar
$(m^{-1})^{\alpha\beta} \partial_\alpha \phi \, \partial_\beta \phi$ appearing inside the
energy-momentum tensor. -/
theorem divEMT_potential_expansion {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (μ : Fin (n + 1)) :
    partialDeriv (fun q => ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) μ p =
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      minkowskiInverse n α β *
        (partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p +
         partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by

  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hpd_diff : ∀ α, Differentiable ℝ (fun q => partialDeriv φ α q) := by
    intro α
    have heq : (fun q => partialDeriv φ α q) = (fun q => fderiv ℝ φ q (basisDir α)) := by
      ext q; exact partialDeriv_eq_fderiv φ (hDiff q) α
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisDir α)).differentiable.comp
      ((hφ.fderiv_right (by norm_num)).differentiable one_ne_zero)
  have hpd : ∀ α, DifferentiableAt ℝ (fun q => partialDeriv φ α q) p :=
    fun α => (hpd_diff α) p

  have hprod : ∀ (α β : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => partialDeriv φ α q * partialDeriv φ β q) p :=
    fun α β => (hpd α).mul (hpd β)
  have hterm : ∀ (α β : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => minkowskiInverse n α β *
        partialDeriv φ α q * partialDeriv φ β q) p := by
    intro α β
    exact ((hpd α).const_mul _).mul (hpd β)
  have hinner : ∀ (α : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => ∑ β : Fin (n + 1),
        minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    intro α
    exact DifferentiableAt.fun_sum (fun β _ => hterm α β)

  rw [partialDeriv_finset_sum Finset.univ
      (fun α q => ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)
      μ p (fun α _ => hinner α)]

  apply Finset.sum_congr rfl
  intro α _
  rw [partialDeriv_finset_sum Finset.univ
      (fun β q => minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)
      μ p (fun β _ => hterm α β)]
  apply Finset.sum_congr rfl
  intro β _


  have hassoc : (fun q => minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
      (fun q => minkowskiInverse n α β * (partialDeriv φ α q * partialDeriv φ β q)) := by
    ext q; ring
  rw [hassoc]
  rw [partialDeriv_const_mul _ _ _ _ (hprod α β)]

  rw [partialDeriv_mul _ _ _ _ (hpd α) (hpd β)]

/-- Explicit expansion of $\partial_\mu T^{\mu\nu}$ as the sum of the principal
$(\square_m \phi)$-term plus three correction terms involving second-order partial
derivatives of $\phi$. This is the algebraic preparation step for Lemma 1.0.2. -/
theorem divEMT_explicit_expansion {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν =

      waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) +

      (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by

  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hpd_diff : ∀ α, Differentiable ℝ (fun q => partialDeriv φ α q) := by
    intro α
    have heq : (fun q => partialDeriv φ α q) = (fun q => fderiv ℝ φ q (basisDir α)) := by
      ext q; exact partialDeriv_eq_fderiv φ (hDiff q) α
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisDir α)).differentiable.comp
      ((hφ.fderiv_right (by norm_num)).differentiable one_ne_zero)
  have hpd : ∀ α, DifferentiableAt ℝ (fun q => partialDeriv φ α q) p :=
    fun α => (hpd_diff α) p
  have hprod : ∀ (γ δ : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => partialDeriv φ γ q * partialDeriv φ δ q) p :=
    fun γ δ => (hpd γ).mul (hpd δ)
  have hpot : DifferentiableAt ℝ (fun q => ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    apply DifferentiableAt.fun_sum; intro α _
    apply DifferentiableAt.fun_sum; intro β _
    exact ((hpd α).const_mul _).mul (hpd β)

  have hpot_c : ∀ (γ δ : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => 1 / 2 * waveMinkowskiMetric n γ δ *
        ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    intro γ δ
    have : (fun q => 1 / 2 * waveMinkowskiMetric n γ δ *
        ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
        (fun q => (1 / 2 * waveMinkowskiMetric n γ δ) *
          (∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)) := by
      ext q; ring
    rw [this]; exact hpot.const_mul _
  have hEMT : ∀ (γ δ : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => energyMomentumTensor φ q γ δ) p := by
    intro γ δ; unfold energyMomentumTensor; exact (hprod γ δ).sub (hpot_c γ δ)
  have hcEMT : ∀ (μ γ δ : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => minkowskiInverse n μ γ * minkowskiInverse n ν δ *
        energyMomentumTensor φ q γ δ) p := by
    intro μ γ δ; exact (hEMT γ δ).const_mul _
  have hInnerSum : ∀ (μ γ : Fin (n + 1)),
      DifferentiableAt ℝ (fun q => ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n ν δ *
          energyMomentumTensor φ q γ δ) p := by
    intro μ γ; exact DifferentiableAt.fun_sum (fun δ _ => hcEMT μ γ δ)

  unfold divEnergyMomentumTensor
  conv_lhs =>
    arg 2; ext μ
    rw [partialDeriv_finset_sum Finset.univ _ μ p (fun γ _ => hInnerSum μ γ)]
    arg 2; ext γ
    rw [partialDeriv_finset_sum Finset.univ _ μ p (fun δ _ => hcEMT μ γ δ)]
    arg 2; ext δ
    rw [show (fun q => minkowskiInverse n μ γ * minkowskiInverse n ν δ *
            energyMomentumTensor φ q γ δ) =
        (fun q => (minkowskiInverse n μ γ * minkowskiInverse n ν δ) *
            energyMomentumTensor φ q γ δ) from by ext q; ring]
    rw [partialDeriv_const_mul _ _ μ p (hEMT γ δ)]

  simp only [energyMomentumTensor]

  conv_lhs =>
    arg 2; ext μ; arg 2; ext γ; arg 2; ext δ
    rw [show (fun q => partialDeriv φ γ q * partialDeriv φ δ q -
            1 / 2 * waveMinkowskiMetric n γ δ *
            ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
        (fun q => (fun q => partialDeriv φ γ q * partialDeriv φ δ q) q -
            (fun q => (1 / 2 * waveMinkowskiMetric n γ δ) *
            (∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)) q)
        from by ext q; ring]
    rw [partialDeriv_sub _ _ μ p (hprod γ δ) (hpot.const_mul _)]
    rw [partialDeriv_mul (fun q => partialDeriv φ γ q) (fun q => partialDeriv φ δ q) μ p (hpd γ) (hpd δ)]
    rw [partialDeriv_const_mul _ _ μ p hpot]
    rw [divEMT_potential_expansion φ hφ p μ]


  have hwaveOp : waveOp φ p = ∑ μ : Fin (n + 1),
      minkowskiInverse n μ μ * partialDeriv (fun q => partialDeriv φ μ q) μ p := by
    simp only [waveOp]
    rw [Fin.sum_univ_succ]
    simp only [minkowskiInverse, waveMinkowskiMetric, Fin.val_zero, if_true]
    have h0 : partialDeriv (fun q => partialDeriv φ 0 q) 0 p =
        fderiv ℝ (fun s => fderiv ℝ (fun r => φ (r, p.2)) s 1) p.1 1 := by
      simp [partialDeriv]
    rw [h0]; congr 1; · ring
    apply Finset.sum_congr rfl; intro i _
    have hsucc : ¬ (Fin.succ i : Fin (n + 1)).val = 0 := by simp [Fin.val_succ]
    simp only [hsucc, ite_false]
    have hpd_ss : partialDeriv (fun q => partialDeriv φ i.succ q) i.succ p =
        fderiv ℝ (fun y => fderiv ℝ (fun z => φ (p.1, z)) y (Pi.single i 1)) p.2 (Pi.single i 1) := by
      simp only [partialDeriv, Fin.val_succ]; simp
    rw [hpd_ss]; ring

  have hdiag : ∀ (μ : Fin (n + 1)) (f : Fin (n + 1) → ℝ),
      ∑ γ : Fin (n + 1), minkowskiInverse n μ γ * f γ =
        minkowskiInverse n μ μ * f μ := by
    intro μ f
    simp only [minkowskiInverse, waveMinkowskiMetric]
    rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ μ) h

  have hmetric_contract : ∀ (μ δ : Fin (n + 1)),
      ∑ γ : Fin (n + 1), minkowskiInverse n μ γ * waveMinkowskiMetric n γ δ =
        if μ = δ then 1 else 0 := by
    intro μ δ
    simp only [minkowskiInverse, waveMinkowskiMetric]
    rw [Finset.sum_eq_single μ]
    · simp only [ite_mul, one_mul, neg_mul, if_true]
      split_ifs <;> simp_all <;> omega
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ μ) h


  set dpd := fun (α μ : Fin (n + 1)) => partialDeriv (fun q => partialDeriv φ α q) μ p with dpd_def
  set pd := fun (α : Fin (n + 1)) => partialDeriv φ α p with pd_def
  set m := fun (μ γ : Fin (n + 1)) => minkowskiInverse n μ γ with m_def
  set met := fun (γ δ : Fin (n + 1)) => waveMinkowskiMetric n γ δ with met_def

  have hLHS_split : ∀ (μ γ δ : Fin (n + 1)),
      m μ γ * m ν δ *
        (dpd γ μ * pd δ + pd γ * dpd δ μ -
          1 / 2 * met γ δ *
            ∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
      m μ γ * m ν δ * dpd γ μ * pd δ +
      m μ γ * m ν δ * pd γ * dpd δ μ -
      m μ γ * m ν δ * (1 / 2 * met γ δ) *
        (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) := by
    intro μ γ δ; ring
  conv_lhs => arg 2; ext μ; arg 2; ext γ; arg 2; ext δ; rw [hLHS_split μ γ δ]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]


  have hkin1 : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      m μ γ * m ν δ * dpd γ μ * pd δ =
      waveOp φ p * ∑ α, m ν α * pd α := by

    have : ∀ μ, ∑ γ, ∑ δ, m μ γ * m ν δ * dpd γ μ * pd δ =
        (∑ γ, m μ γ * dpd γ μ) * (∑ δ, m ν δ * pd δ) := by
      intro μ
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro γ _
      simp_rw [show ∀ (δ : Fin (n + 1)),
          m μ γ * m ν δ * dpd γ μ * pd δ = (m μ γ * dpd γ μ) * (m ν δ * pd δ) from
        by intro δ; ring]
      rw [← Finset.mul_sum]

    simp_rw [this]
    rw [← Finset.sum_mul]
    congr 1

    conv_lhs => arg 2; ext μ; rw [hdiag μ (fun γ => dpd γ μ)]
    exact hwaveOp.symm

  have hkin2 : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      m μ γ * m ν δ * pd γ * dpd δ μ =
      ∑ μ, ∑ α, ∑ β, m μ α * m ν β * pd α * dpd β μ := by
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    ring


  have hpot_simp : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      m μ γ * m ν δ * (1 / 2 * met γ δ) *
        (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
      1 / 2 * ∑ μ, m ν μ *
        (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) := by

    simp_rw [show ∀ (μ γ δ : Fin (n + 1)) (x : ℝ),
        m μ γ * m ν δ * (1 / 2 * met γ δ) * x =
        1 / 2 * (m μ γ * met γ δ) * m ν δ * x from by intros; ring]
    rw [show (∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        1 / 2 * (m μ γ * met γ δ) * m ν δ *
          (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ))) =
      1 / 2 * ∑ μ, ∑ γ, ∑ δ,
        (m μ γ * met γ δ) * m ν δ *
          (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro γ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro δ _
      ring]
    congr 1
    apply Finset.sum_congr rfl; intro μ _

    rw [Finset.sum_comm]

    simp_rw [show ∀ (γ δ : Fin (n + 1)) (x : ℝ),
        m μ γ * met γ δ * m ν δ * x = (m μ γ * met γ δ) * (m ν δ * x) from by intros; ring]
    simp_rw [← Finset.sum_mul]
    simp_rw [show ∀ (δ : Fin (n + 1)),
        (∑ γ : Fin (n + 1), m μ γ * met γ δ) = if μ = δ then 1 else 0 from
      fun δ => hmetric_contract μ δ]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

  have hpot_split : 1 / 2 * ∑ μ : Fin (n + 1), m ν μ *
      (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
    1 / 2 * ∑ μ, ∑ α, ∑ β, m μ ν * m α β * dpd α μ * pd β +
    1 / 2 * ∑ μ, ∑ α, ∑ β, m μ ν * m α β * pd α * dpd β μ := by

    have hsymm : ∀ (a b : Fin (n + 1)), m a b = m b a := by
      intro a b; simp only [m_def, minkowskiInverse_symm]

    rw [← mul_add]
    congr 1

    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro μ _

    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    simp_rw [show ∀ (α β : Fin (n + 1)),
        m ν μ * (m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
        m μ ν * m α β * dpd α μ * pd β + m μ ν * m α β * pd α * dpd β μ from
      by intro α β; rw [hsymm ν μ]; ring]
    simp only [Finset.sum_add_distrib]

  rw [hkin1, hkin2, hpot_simp, hpot_split]
  ring

/-- Rewriting the remainder `EMT_remainder` as the explicit three-term sum of
second-order derivative quantities, obtained by subtracting the wave-operator term from
`divEMT_explicit_expansion`. -/
theorem EMT_remainder_eq_three_terms {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    EMT_remainder φ p ν =

      (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
  unfold EMT_remainder
  have h := divEMT_explicit_expansion φ hφ p ν
  linarith

/-- Combined product-rule expansion: $\partial_\mu T^{\mu\nu}$ equals the wave-operator term
$(\square_m \phi)(m^{-1})^{\nu\alpha}\partial_\alpha\phi$ plus three explicit correction
terms. -/
theorem divEMT_product_rule_expansion {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν =
      waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) +

      (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) +

      (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
  have h_rem := EMT_remainder_eq_three_terms φ hφ p ν
  unfold EMT_remainder at h_rem
  linarith

/-- The three correction terms in the expansion of $\partial_\mu T^{\mu\nu}$ sum to zero
when $\phi \in C^2$. The cancellation uses the symmetry of the inverse Minkowski metric
together with the Schwarz / Clairaut symmetry of second partial derivatives. -/
theorem three_term_schwarz_cancellation {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) +
    (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) +
    (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) = 0 := by


  have hA : (∑ μ : Fin (n+1), ∑ α, ∑ β, minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) =
            (∑ μ, ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
    rw [triple_sum_swap_13 (fun μ α β => minkowskiInverse n μ α * minkowskiInverse n ν β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p)]
    congr 1; ext μ; congr 1; ext α; congr 1; ext β
    rw [partialDeriv_schwarz φ hφ β μ p, minkowskiInverse_symm n β α, minkowskiInverse_symm n ν μ]
    ring


  have hB : (∑ μ : Fin (n+1), ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) =
            (∑ μ, ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
        partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
    congr 1; ext μ
    conv_lhs => arg 2; ext α; arg 2; ext β; rw [partialDeriv_schwarz φ hφ μ α p]
    rw [Finset.sum_comm]
    congr 1; ext α; congr 1; ext β
    rw [minkowskiInverse_symm n β α, partialDeriv_schwarz φ hφ β μ p]
    ring


  linarith

/-- The remainder term `EMT_remainder` vanishes for any $C^2$ scalar field, as a consequence
of the Schwarz cancellation of the three correction terms. -/
theorem EMT_schwarz_cancellation {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    EMT_remainder φ p ν = 0 := by
  unfold EMT_remainder
  have h1 := divEMT_product_rule_expansion φ hφ p ν
  have h2 := three_term_schwarz_cancellation φ hφ p ν
  linarith

/-- Core identity for the divergence of the energy-momentum tensor:
$\partial_\mu T^{\mu\nu} = (\square_m \phi)(m^{-1})^{\nu\alpha}\partial_\alpha\phi$
for any $C^2$ scalar field. -/
theorem emt_core_identity {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν =
      waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) := by
  have h1 := EMT_product_rule_expansion φ hφ p ν
  have h2 := EMT_schwarz_cancellation φ hφ p ν
  linarith

/-- **Lemma 1.0.2.** Conservation form of the divergence of the energy-momentum tensor:
$\partial_\mu T^{\mu\nu} = (\square_m \phi)(m^{-1})^{\nu\alpha} \partial_\alpha \phi$. -/
theorem energy_momentum_conserved {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν =
      waveOp φ p * ∑ α : Fin (n + 1),
        minkowskiInverse n ν α * partialDeriv φ α p :=
  emt_core_identity φ hφ p ν

/-- **Lemma 1.0.2 (consequence).** If $\phi$ solves the wave equation $\square_m \phi = 0$,
then the energy-momentum tensor is divergence-free: $\partial_\mu T^{\mu\nu} = 0$. -/
theorem energy_momentum_divergence_free {n : ℕ} (φ : WaveScalarField n)
    (hφ_smooth : ContDiff ℝ 2 φ)
    (hφ : ∀ p, waveOp φ p = 0) (p : WaveSpacetime n) (ν : Fin (n + 1)) :
    divEnergyMomentumTensor φ p ν = 0 := by
  rw [energy_momentum_conserved φ hφ_smooth]
  simp [hφ p]

/-- Compact statement of Lemma 1.0.2: the conjunction of the divergence identity and the
divergence-free consequence for wave-equation solutions. -/
theorem energy_momentum_divergence_lemma {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) :
    (∀ p ν, divEnergyMomentumTensor φ p ν =
      waveOp φ p * ∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) ∧
    (∀ (hw : ∀ p, waveOp φ p = 0), ∀ p ν, divEnergyMomentumTensor φ p ν = 0) :=
  ⟨fun p ν => energy_momentum_conserved φ hφ p ν,
   fun hw p ν => energy_momentum_divergence_free φ hφ hw p ν⟩

/-- The index-lowered components $X_\alpha = m_{\alpha\beta} X^\beta$ of a spacetime
vector field. -/
noncomputable def lowerIndex {n : ℕ} (X : SpacetimeVectorField n) (p : WaveSpacetime n)
    (α : Fin (n + 1)) : ℝ :=
  ∑ β : Fin (n + 1), waveMinkowskiMetric n α β * X p β

/-- **Definition 1.0.2 (Compatible current).** Given a scalar field $\phi$ and a vector
field $X$, the compatible current is the vector field
${}^{(X)} J^\mu \overset{\text{def}}{=} T^{\mu\alpha} X_\alpha$. -/
noncomputable def compatibleCurrent {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (p : WaveSpacetime n) (μ : Fin (n + 1)) : ℝ :=
  ∑ α : Fin (n + 1),
    (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ * energyMomentumTensor φ p γ δ) *
    lowerIndex X p α

/-- The deformation tensor of a vector field $X$:
${}^{(X)} \pi_{\mu\nu} \overset{\text{def}}{=} \tfrac{1}{2}(\partial_\mu X_\nu + \partial_\nu X_\mu)$. -/
noncomputable def deformationTensor {n : ℕ} (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) (μ ν : Fin (n + 1)) : ℝ :=
  (1/2 : ℝ) * (partialDeriv (fun q => lowerIndex X q ν) μ p +
                partialDeriv (fun q => lowerIndex X q μ) ν p)

/-- The divergence $\partial_\mu({}^{(X)} J^\mu)$ of the compatible current. -/
noncomputable def divCompatibleCurrent {n : ℕ} (φ : WaveScalarField n) (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) : ℝ :=
  ∑ μ : Fin (n + 1),
    partialDeriv (fun q => compatibleCurrent φ X q μ) μ p

/-- The auxiliary remainder $\partial_\mu({}^{(X)} J^\mu) - T^{\alpha\beta}\, {}^{(X)}\pi_{\alpha\beta}$,
which vanishes on solutions of the wave equation (Corollary 1.0.3). -/
noncomputable def divEMT_contracted_X {n : ℕ} (φ : WaveScalarField n) (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) : ℝ :=
  divCompatibleCurrent φ X p -
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n α γ * minkowskiInverse n β δ *
          energyMomentumTensor φ p γ δ) *
      deformationTensor X p α β

/-- Tautological rewriting splitting $\partial_\mu({}^{(X)} J^\mu)$ as the remainder
`divEMT_contracted_X` plus the deformation-tensor contraction $T^{\alpha\beta}\, {}^{(X)}\pi_{\alpha\beta}$. -/
theorem compatible_current_product_rule_expansion {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (p : WaveSpacetime n) :
    divCompatibleCurrent φ X p =
      divEMT_contracted_X φ X p +
      ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
          minkowskiInverse n α γ * minkowskiInverse n β δ *
            energyMomentumTensor φ p γ δ) *
        deformationTensor X p α β := by
  unfold divEMT_contracted_X
  ring

/-- If $S_{ij}$ is symmetric in $(i, j)$, then contracting it against an arbitrary tensor
$F_{ij}$ is the same as contracting it against the symmetrization
$\tfrac{1}{2}(F_{ij} + F_{ji})$. -/
lemma symm_sum_eq_half_deformation {ι : Type*} [Fintype ι]
    (S : ι → ι → ℝ) (F : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i) :
    ∑ i, ∑ j, S i j * F i j = ∑ i, ∑ j, S i j * ((1/2 : ℝ) * (F i j + F j i)) := by
  have key : ∑ i, ∑ j, S i j * F j i = ∑ i, ∑ j, S i j * F i j := by
    conv_lhs => rw [Finset.sum_comm (f := fun i j => S i j * F j i)]
    congr 1; ext j; congr 1; ext i; rw [hS j i]
  have expand : ∀ i j, S i j * (1/2 * (F i j + F j i)) =
    1/2 * (S i j * F i j) + 1/2 * (S i j * F j i) := by intros; ring
  simp_rw [expand]
  have h1 : ∑ i : ι, ∑ j : ι, (1 / 2 * (S i j * F i j) + 1 / 2 * (S i j * F j i)) =
    1/2 * (∑ i, ∑ j, S i j * F i j) + 1/2 * (∑ i, ∑ j, S i j * F j i) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, key]; ring

/-- Symmetry of the energy-momentum tensor: $T_{\mu\nu} = T_{\nu\mu}$. -/
lemma energyMomentumTensor_symm {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n)
    (μ ν : Fin (n + 1)) :
    energyMomentumTensor φ p μ ν = energyMomentumTensor φ p ν μ := by
  unfold energyMomentumTensor
  have hm : waveMinkowskiMetric n μ ν = waveMinkowskiMetric n ν μ := by
    unfold waveMinkowskiMetric; split_ifs with h1 h2 h2 <;> simp_all
  rw [hm]; ring

/-- Symmetry of the twice-raised energy-momentum tensor:
$T^{\alpha\beta} = T^{\beta\alpha}$. -/
lemma raised_EMT_symm {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n)
    (α β : Fin (n + 1)) :
    (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n α γ * minkowskiInverse n β δ *
        energyMomentumTensor φ p γ δ) =
    (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n β γ * minkowskiInverse n α δ *
        energyMomentumTensor φ p γ δ) := by
  conv_lhs => arg 2; ext γ; arg 2; ext δ; rw [energyMomentumTensor_symm φ p γ δ]
  rw [Finset.sum_comm]
  congr 1; ext δ; congr 1; ext γ; ring

/-- Product rule for the partial derivative of a finite sum of products:
$\partial_\mu \bigl(\sum_i f_i g_i\bigr) = \sum_i \bigl(\partial_\mu f_i\bigr) g_i +
f_i \bigl(\partial_\mu g_i\bigr)$. -/
theorem partialDeriv_sum_product {n : ℕ} {N : ℕ}
    (f g : Fin N → WaveScalarField n) (μ : Fin (n + 1)) (p : WaveSpacetime n)
    (hf : ∀ i, DifferentiableAt ℝ (f i) p)
    (hg : ∀ i, DifferentiableAt ℝ (g i) p) :
    partialDeriv (fun q => ∑ i : Fin N, f i q * g i q) μ p =
    ∑ i : Fin N, (partialDeriv (f i) μ p * g i p + f i p * partialDeriv (g i) μ p) := by
  simp only [partialDeriv]
  split_ifs with h
  ·
    have hf_s : ∀ i, DifferentiableAt ℝ (fun s => f i (s, p.2)) p.1 := fun i =>
      (hf i).comp p.1 (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const _))
    have hg_s : ∀ i, DifferentiableAt ℝ (fun s => g i (s, p.2)) p.1 := fun i =>
      (hg i).comp p.1 (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const _))
    have hfg_s : ∀ i, DifferentiableAt ℝ (fun s => f i (s, p.2) * g i (s, p.2)) p.1 :=
      fun i => (hf_s i).mul (hg_s i)
    have h_eq : (fun s => ∑ i : Fin N, f i (s, p.2) * g i (s, p.2)) =
      ∑ i : Fin N, (fun s => f i (s, p.2) * g i (s, p.2)) := by
      ext s; simp [Finset.sum_apply]
    rw [h_eq, fderiv_sum (fun i _ => hfg_s i), ContinuousLinearMap.sum_apply]
    congr 1; ext i
    have : (fun s => f i (s, p.2) * g i (s, p.2)) =
      (fun s => f i (s, p.2)) * (fun s => g i (s, p.2)) := by ext; simp [Pi.mul_apply]
    rw [this, fderiv_mul (hf_s i) (hg_s i), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  ·
    have hf_s : ∀ i, DifferentiableAt ℝ (fun y => f i (p.1, y)) p.2 := fun i =>
      (hf i).comp p.2 (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id)
    have hg_s : ∀ i, DifferentiableAt ℝ (fun y => g i (p.1, y)) p.2 := fun i =>
      (hg i).comp p.2 (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id)
    have hfg_s : ∀ i, DifferentiableAt ℝ (fun y => f i (p.1, y) * g i (p.1, y)) p.2 :=
      fun i => (hf_s i).mul (hg_s i)
    have h_eq : (fun y => ∑ i : Fin N, f i (p.1, y) * g i (p.1, y)) =
      ∑ i : Fin N, (fun y => f i (p.1, y) * g i (p.1, y)) := by
      ext s; simp [Finset.sum_apply]
    rw [h_eq, fderiv_sum (fun i _ => hfg_s i), ContinuousLinearMap.sum_apply]
    congr 1; ext i
    have : (fun y => f i (p.1, y) * g i (p.1, y)) =
      (fun y => f i (p.1, y)) * (fun y => g i (p.1, y)) := by ext; simp [Pi.mul_apply]
    rw [this, fderiv_mul (hf_s i) (hg_s i), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring

/-- For a $C^2$ scalar field, the partial derivative $\partial_\nu \phi$ is itself a
differentiable function of the spacetime point. -/
lemma partialDeriv_differentiable {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (ν : Fin (n + 1)) :
    Differentiable ℝ (fun q => partialDeriv φ ν q) := by
  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hDiff_fderiv : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (by norm_num)).differentiable one_ne_zero
  have heq : (fun q => partialDeriv φ ν q) = (fun q => fderiv ℝ φ q (basisDir ν)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) ν
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ (basisDir ν)).differentiable.comp hDiff_fderiv

/-- For a $C^2$ scalar field, each component $T_{\gamma\delta}$ of the energy-momentum
tensor is differentiable as a function of the spacetime point. -/
lemma emt_differentiableAt {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (p : WaveSpacetime n) (γ δ : Fin (n + 1)) :
    DifferentiableAt ℝ (fun q => energyMomentumTensor φ q γ δ) p := by
  simp only [energyMomentumTensor]
  have hpd : ∀ ν, DifferentiableAt ℝ (fun q => partialDeriv φ ν q) p :=
    fun ν => (partialDeriv_differentiable φ hφ ν) p
  apply DifferentiableAt.sub
  · exact (hpd γ).mul (hpd δ)
  · show DifferentiableAt ℝ (fun q => (1/2 : ℝ) * waveMinkowskiMetric n γ δ *
      ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) p
    apply DifferentiableAt.mul (differentiableAt_const _)
    have h1 : (fun q => ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) =
      ∑ a : Fin (n + 1), (fun q => ∑ b : Fin (n + 1),
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) := by
      ext q; simp [Finset.sum_apply]
    rw [h1]
    apply DifferentiableAt.sum
    intro a _
    have h2 : (fun q => ∑ b : Fin (n + 1),
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) =
      ∑ b : Fin (n + 1), (fun q =>
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) := by
      ext q; simp [Finset.sum_apply]
    rw [h2]
    apply DifferentiableAt.sum
    intro b _
    exact ((differentiableAt_const _).mul (hpd a)).mul (hpd b)

/-- The doubly raised energy-momentum tensor $T^{\mu\alpha}$ is differentiable as a
function of the spacetime point, for any $C^2$ scalar field. -/
theorem raised_EMT_differentiableAt {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (p : WaveSpacetime n) (μ α : Fin (n + 1)) :
    DifferentiableAt ℝ (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) p := by
  have h1 : (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) =
    ∑ γ : Fin (n + 1), (fun q => ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) := by
    ext q; simp [Finset.sum_apply]
  rw [h1]
  apply DifferentiableAt.sum
  intro γ _
  have h2 : (fun q => ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) =
    ∑ δ : Fin (n + 1), (fun q =>
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) := by
    ext q; simp [Finset.sum_apply]
  rw [h2]
  apply DifferentiableAt.sum
  intro δ _
  exact (differentiableAt_const _).mul (emt_differentiableAt φ hφ p γ δ)

/-- If each component of a vector field $X$ is differentiable at $p$, then its
index-lowered component $X_\alpha$ is differentiable at $p$. -/
theorem lowerIndex_differentiableAt {n : ℕ} (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) (α : Fin (n + 1))
    (hX : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    DifferentiableAt ℝ (fun q => lowerIndex X q α) p := by
  unfold lowerIndex
  have : (fun q => ∑ β : Fin (n + 1), waveMinkowskiMetric n α β * X q β) =
         (∑ β : Fin (n + 1), fun q => waveMinkowskiMetric n α β * X q β) := by
    ext q; simp [Finset.sum_apply]
  rw [this]
  exact DifferentiableAt.sum (fun β _ => (hX β).const_mul _)

/-- Product-rule expansion of the divergence of the compatible current:
$\partial_\mu({}^{(X)} J^\mu) = (\partial_\mu T^{\mu\alpha}) X_\alpha + T^{\mu\alpha} \partial_\mu X_\alpha$. -/
theorem divCC_product_rule {n : ℕ} (φ : WaveScalarField n) (X : SpacetimeVectorField n)
    (hφ_smooth : ContDiff ℝ 2 φ) (p : WaveSpacetime n)
    (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    divCompatibleCurrent φ X p =
      ∑ α : Fin (n + 1),
        divEnergyMomentumTensor φ p α * lowerIndex X p α +
      ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1),
        (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
          minkowskiInverse n μ γ * minkowskiInverse n α δ *
            energyMomentumTensor φ p γ δ) *
        partialDeriv (fun q => lowerIndex X q α) μ p := by
  simp only [divCompatibleCurrent, compatibleCurrent, divEnergyMomentumTensor]

  have h_rw : ∀ μ : Fin (n + 1),
      partialDeriv (fun q =>
        ∑ α : Fin (n + 1),
          (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
            minkowskiInverse n μ γ * minkowskiInverse n α δ *
              energyMomentumTensor φ q γ δ) *
          lowerIndex X q α) μ p =
      ∑ α : Fin (n + 1),
        (partialDeriv (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
            minkowskiInverse n μ γ * minkowskiInverse n α δ *
              energyMomentumTensor φ q γ δ) μ p *
          lowerIndex X p α +
        (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
            minkowskiInverse n μ γ * minkowskiInverse n α δ *
              energyMomentumTensor φ p γ δ) *
          partialDeriv (fun q => lowerIndex X q α) μ p) := by
    intro μ
    exact partialDeriv_sum_product
      (fun α => fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n α δ *
          energyMomentumTensor φ q γ δ)
      (fun α => fun q => lowerIndex X q α) μ p
      (fun α => raised_EMT_differentiableAt φ hφ_smooth p μ α)
      (fun α => lowerIndex_differentiableAt X p α hX_diff)

  simp_rw [h_rw, Finset.sum_add_distrib]

  congr 1
  rw [Finset.sum_comm]
  congr 1; ext α; rw [Finset.sum_mul]

/-- The remainder `divEMT_contracted_X` is exactly the contraction
$(\partial_\mu T^{\mu\alpha}) X_\alpha$ of the divergence of $T^{\mu\nu}$ with the
lowered vector field. Used to relate Corollary 1.0.3 to Lemma 1.0.2. -/
theorem divEMT_contracted_X_eq {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (hφ_smooth : ContDiff ℝ 2 φ) (p : WaveSpacetime n)
    (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    divEMT_contracted_X φ X p =
      ∑ α : Fin (n + 1),
        divEnergyMomentumTensor φ p α * lowerIndex X p α := by
  unfold divEMT_contracted_X
  rw [divCC_product_rule φ X hφ_smooth p hX_diff]


  suffices h : ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1),
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n α δ *
          energyMomentumTensor φ p γ δ) *
      partialDeriv (fun q => lowerIndex X q α) μ p =
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n α γ * minkowskiInverse n β δ *
          energyMomentumTensor φ p γ δ) *
      deformationTensor X p α β by
    linarith

  unfold deformationTensor
  exact symm_sum_eq_half_deformation
    (fun μ α => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ p γ δ)
    (fun μ α => partialDeriv (fun q => lowerIndex X q α) μ p)
    (fun μ α => raised_EMT_symm φ p μ α)

/-- For a wave-equation solution, the remainder `divEMT_contracted_X` vanishes, since
$\partial_\mu T^{\mu\nu} = 0$ (Lemma 1.0.2). -/
theorem divEMT_contracted_X_vanishes {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (hφ_smooth : ContDiff ℝ 2 φ)
    (hφ : ∀ p, waveOp φ p = 0)
    (p : WaveSpacetime n)
    (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    divEMT_contracted_X φ X p = 0 := by
  rw [divEMT_contracted_X_eq φ X hφ_smooth p hX_diff]
  simp [energy_momentum_divergence_free φ hφ_smooth hφ]

/-- **Corollary 1.0.3.** For a solution $\phi$ of the wave equation,
$\partial_\mu({}^{(X)} J^\mu) = T^{\alpha\beta}\, {}^{(X)} \pi_{\alpha\beta}$, where
${}^{(X)}\pi$ is the deformation tensor of $X$. -/
theorem compatible_current_divergence {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (hφ_smooth : ContDiff ℝ 2 φ)
    (hφ : ∀ p, waveOp φ p = 0)
    (p : WaveSpacetime n)
    (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    divCompatibleCurrent φ X p =
      ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
          minkowskiInverse n α γ * minkowskiInverse n β δ *
            energyMomentumTensor φ p γ δ) *
        deformationTensor X p α β := by
  have h1 := compatible_current_product_rule_expansion φ X p
  have h2 := divEMT_contracted_X_vanishes φ X hφ_smooth hφ p hX_diff
  linarith

/-- If $\phi$ solves the wave equation and $X$ is a Killing field (i.e. has vanishing
deformation tensor), then the compatible current is divergence-free:
$\partial_\mu({}^{(X)} J^\mu) = 0$. -/
theorem compatible_current_divergence_free {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (hφ_smooth : ContDiff ℝ 2 φ)
    (hφ : ∀ p, waveOp φ p = 0)
    (hX : ∀ p μ ν, deformationTensor X p μ ν = 0)
    (p : WaveSpacetime n)
    (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
    divCompatibleCurrent φ X p = 0 := by
  rw [compatible_current_divergence φ X hφ_smooth hφ p hX_diff]
  simp [hX]

/-- A spacetime domain $\Omega$ is regular if it is open, bounded and has compact closure;
the hypotheses needed to state the divergence theorem cleanly. -/
structure IsRegularDomain {n : ℕ} (Ω : Set (WaveSpacetime n)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  isCompact_closure : IsCompact (closure Ω)


/-- The surface measure on the boundary $\partial\Omega$, defined as the $n$-dimensional
Hausdorff measure restricted to the topological frontier of $\Omega$. -/
noncomputable def surfaceMeasure {n : ℕ} (Ω : Set (WaveSpacetime n)) :
    Measure (WaveSpacetime n) :=
  (Measure.hausdorffMeasure n).restrict (frontier Ω)



/-- The truncated solid backwards light cone with apex $(R, x_0)$, restricted to the time
slab $t_0 \leq t \leq t_1$:
$\{(t, x) \mid t_0 \leq t \leq t_1,\ |x - x_0| \leq R - t\}$. -/
def truncatedBackwardsCone {n : ℕ} (x₀ : Fin n → ℝ) (R t₀ t₁ : ℝ) :
    Set (WaveSpacetime n) :=
  { p | t₀ ≤ p.1 ∧ p.1 ≤ t₁ ∧ waveEuclidNormSq (p.2 - x₀) ≤ (R - p.1) ^ 2 }

/-- The constant past-directed timelike Killing vector field $X^\mu = -\delta_0^\mu$. -/
def pastTimelikeKillingField (n : ℕ) : SpacetimeVectorField n :=
  fun _ μ => if μ.val = 0 then -1 else 0

/-- The lateral (null) mantle of the truncated backwards cone:
$\{(t, x) \mid 0 \leq t \leq t,\ |x - x_0| = R - t\}$. -/
def coneMantle {n : ℕ} (x₀ : Fin n → ℝ) (R : ℝ) (t : ℝ) : Set (WaveSpacetime n) :=
  { p | 0 ≤ p.1 ∧ p.1 ≤ t ∧ waveEuclidNormSq (p.2 - x₀) = (R - p.1) ^ 2 }


/-- Each squared coordinate is bounded by the squared Euclidean norm:
$x_i^2 \leq \sum_j x_j^2$. -/
lemma waveEuclidNormSq_component_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    x i ^ 2 ≤ waveEuclidNormSq x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- If $\sum_i x_i^2 \leq R^2$ and $R \geq 0$, then the sup-norm $\|x\|_\infty \leq R$. -/
lemma norm_le_of_waveEuclidNormSq_le {n : ℕ} (x : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (h : waveEuclidNormSq x ≤ R ^ 2) : ‖x‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ hR
  calc (x i) ^ 2 ≤ waveEuclidNormSq x := waveEuclidNormSq_component_le x i
    _ ≤ R ^ 2 := h

/-- For $0 \leq t \leq R$, the truncated backwards cone is bounded in spacetime. -/
lemma truncatedBackwardsCone_isBounded {n : ℕ} (x₀ : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (t : ℝ) (_ht : 0 ≤ t) (htR : t ≤ R) :
    Bornology.IsBounded (truncatedBackwardsCone x₀ R 0 t) := by
  apply Metric.isBounded_closedBall (x := (0, x₀)) (r := R) |>.subset
  intro ⟨τ, y⟩ hp
  simp only [truncatedBackwardsCone, mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [Metric.mem_closedBall, Prod.dist_eq]
  apply max_le
  · rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]; linarith
  · rw [dist_eq_norm]
    apply norm_le_of_waveEuclidNormSq_le _ R hR.le
    calc waveEuclidNormSq (y - x₀) ≤ (R - τ) ^ 2 := h3
      _ ≤ R ^ 2 := by nlinarith

/-- The interior of the truncated backwards cone is a regular domain in the sense of
`IsRegularDomain`, so the divergence theorem applies. -/
theorem truncatedBackwardsCone_isRegularDomain {n : ℕ} (x₀ : Fin n → ℝ) (R : ℝ)
    (hR : 0 < R) (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ R) :
    IsRegularDomain (interior (truncatedBackwardsCone x₀ R 0 t)) := by
  have hbdd : Bornology.IsBounded (interior (truncatedBackwardsCone x₀ R 0 t)) :=
    (truncatedBackwardsCone_isBounded x₀ R hR t ht htR).subset interior_subset
  exact ⟨isOpen_interior, hbdd, hbdd.isCompact_closure⟩

/-- The lowered components of the past-timelike Killing field are constant in spacetime,
so all their partial derivatives vanish. -/
lemma partialDeriv_lowerIndex_killing_eq_zero {n : ℕ} (ν μ : Fin (n + 1))
    (p : WaveSpacetime n) :
    partialDeriv (fun q => lowerIndex (pastTimelikeKillingField n) q ν) μ p = 0 := by
  unfold partialDeriv
  split
  ·
    have : (fun s => lowerIndex (pastTimelikeKillingField n) (s, p.2) ν) =
           fun _ => lowerIndex (pastTimelikeKillingField n) (0, p.2) ν := by
      ext s; simp [lowerIndex, pastTimelikeKillingField]
    rw [this]; simp
  ·
    have : (fun y => lowerIndex (pastTimelikeKillingField n) (p.1, y) ν) =
           fun _ => lowerIndex (pastTimelikeKillingField n) (p.1, 0) ν := by
      ext y; simp [lowerIndex, pastTimelikeKillingField]
    rw [this]; simp

/-- The past-timelike Killing field has vanishing deformation tensor:
${}^{(X)}\pi_{\mu\nu} = 0$. This justifies calling it a Killing vector field. -/
theorem pastTimelikeKillingField_isKilling {n : ℕ} (p : WaveSpacetime n)
    (μ ν : Fin (n + 1)) :
    deformationTensor (pastTimelikeKillingField n) p μ ν = 0 := by
  unfold deformationTensor
  rw [partialDeriv_lowerIndex_killing_eq_zero,
      partialDeriv_lowerIndex_killing_eq_zero]
  ring












/-- The index-raising operation: $N^\gamma = (m^{-1})^{\gamma\mu} N_\mu$. -/
def raiseIndex {n : ℕ} (N : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun γ => ∑ μ : Fin (n + 1), minkowskiInverse n γ μ * N μ

/-- Symmetry of the Minkowski metric: $m_{\mu\nu} = m_{\nu\mu}$. -/
lemma waveMinkowskiMetric_symm (n : ℕ) (μ ν : Fin (n + 1)) :
    waveMinkowskiMetric n μ ν = waveMinkowskiMetric n ν μ := by
  simp only [waveMinkowskiMetric]; split_ifs <;> simp_all [eq_comm]

/-- The diagonal entries of the Minkowski metric square to $1$: $m_{kk}^2 = (\pm 1)^2 = 1$. -/
lemma waveMinkowskiMetric_sq_diag (n : ℕ) (k : Fin (n + 1)) :
    waveMinkowskiMetric n k k * waveMinkowskiMetric n k k = 1 := by
  simp only [waveMinkowskiMetric, ite_true]; split_ifs <;> ring

/-- Since $m_{k\beta}$ is non-zero only when $\beta = k$, contracting it against a vector
$f$ picks out the diagonal term: $\sum_\beta m_{k\beta} f(\beta) = m_{kk} f(k)$. -/
lemma waveMinkowskiMetric_row_select (n : ℕ) (k : Fin (n + 1))
    (f : Fin (n + 1) → ℝ) :
    ∑ β : Fin (n + 1), waveMinkowskiMetric n k β * f β =
    waveMinkowskiMetric n k k * f k := by
  simp_rw [waveMinkowskiMetric_symm n k]
  rw [show ∑ β, waveMinkowskiMetric n β k * f β =
      ∑ β ∈ Finset.univ, waveMinkowskiMetric n β k * f β from rfl]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  intro b _ hb; simp [waveMinkowskiMetric, hb]


/-- The Minkowski metric vanishes off the diagonal: $m_{\alpha\beta} = 0$ if $\alpha \neq \beta$. -/
lemma waveMinkowskiMetric_off_diag {n : ℕ} (α β : Fin (n + 1)) (h : α ≠ β) :
    waveMinkowskiMetric n α β = 0 := by
  simp [waveMinkowskiMetric, h]

/-- Because $m$ is diagonal, $N^\gamma = (m^{-1})^{\gamma\mu} N_\mu = m_{\gamma\gamma} N_\gamma$. -/
lemma raiseIndex_eq_diag {n : ℕ} (N : Fin (n + 1) → ℝ) (γ : Fin (n + 1)) :
    raiseIndex N γ = waveMinkowskiMetric n γ γ * N γ := by
  unfold raiseIndex minkowskiInverse
  conv_lhs =>
    arg 2; ext μ
    rw [show waveMinkowskiMetric n γ μ * N μ =
      if γ = μ then waveMinkowskiMetric n γ γ * N γ else 0 from by
      split_ifs with h
      · subst h; ring
      · simp [waveMinkowskiMetric_off_diag γ μ h]]
  simp

/-- The Minkowski norm-squared is invariant under index raising:
$m(N^\sharp, N^\sharp) = m(N, N)$. -/
lemma minkowskiProduct_raiseIndex_self {n : ℕ} (N : Fin (n + 1) → ℝ) :
    minkowskiProduct (raiseIndex N) (raiseIndex N) = minkowskiProduct N N := by
  simp only [minkowskiProduct, raiseIndex_eq_diag]
  congr 1; ext α
  congr 1; ext β
  by_cases hab : α = β
  · subst hab
    simp only [waveMinkowskiMetric]
    split_ifs <;> ring
  · simp [waveMinkowskiMetric_off_diag α β hab]




/-- The past-timelike Killing field $X^\mu = -\delta_0^\mu$ is past-causal at every point. -/
lemma pastTimelikeKillingField_isPastCausal (n : ℕ) (σ : WaveSpacetime n) :
    IsPastCausal (pastTimelikeKillingField n σ) := by
  constructor
  ·
    unfold IsPastDirected pastTimelikeKillingField
    simp
  ·
    unfold minkowskiProduct waveMinkowskiMetric pastTimelikeKillingField
    simp






/-- For a $C^2$ field, the time-direction partial derivative
$s \mapsto \partial_t \phi(s, x_0)$ is itself differentiable in $s$. -/
lemma diff_outer_t' {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ) (x₀ : Fin n → ℝ) :
    Differentiable ℝ (fun s => (fderiv ℝ (fun r => φ (r, x₀)) s) 1) := by
  have h : ContDiff ℝ 2 (fun r : ℝ => φ (r, x₀)) := hφ.comp₂ contDiff_id contDiff_const
  have heq : (fun s => (fderiv ℝ (fun r => φ (r, x₀)) s) 1) = deriv (fun r => φ (r, x₀)) := by ext s; simp
  rw [heq]; have h2 : ContDiff ℝ (1 + 1) (fun r : ℝ => φ (r, x₀)) := by convert h using 2
  exact h2.deriv'.differentiable (by decide)

/-- For a $C^2$ field, the spatial partial derivative $y \mapsto \partial_i \phi(t_0, y)$
is itself differentiable in $y$. -/
lemma diff_outer_x' {n : ℕ} (φ : WaveScalarField n) (hφ : ContDiff ℝ 2 φ) (t₀ : ℝ) (i : Fin n) :
    Differentiable ℝ (fun y => (fderiv ℝ (fun z => φ (t₀, z)) y) (Pi.single i 1)) := by
  have h_fderiv_smooth : ContDiff ℝ 1 (fun y : Fin n → ℝ => fderiv ℝ (fun z => φ (t₀, z)) y) :=
    ContDiff.fderiv (hφ.comp₂ contDiff_const contDiff_snd) contDiff_id (by decide)
  exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.fun_comp h_fderiv_smooth).differentiable (by decide)

/-- Linearity of the wave operator under subtraction:
$\square_m(\phi_1 - \phi_2) = \square_m \phi_1 - \square_m \phi_2$. -/
theorem waveOp_linearity_sub {n : ℕ} (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) (p : WaveSpacetime n) :
    waveOp (fun q => φ₁ q - φ₂ q) p = waveOp φ₁ p - waveOp φ₂ p := by
  unfold waveOp
  have hd1t : ∀ s, DifferentiableAt ℝ (fun r => φ₁ (r, p.2)) s :=
    fun s => ((hφ₁.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
  have hd2t : ∀ s, DifferentiableAt ℝ (fun r => φ₂ (r, p.2)) s :=
    fun s => ((hφ₂.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
  have hd1x : ∀ y, DifferentiableAt ℝ (fun z => φ₁ (p.1, z)) y :=
    fun y => ((hφ₁.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
  have hd2x : ∀ y, DifferentiableAt ℝ (fun z => φ₂ (p.1, z)) y :=
    fun y => ((hφ₂.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
  have htime_fn : (fun s => fderiv ℝ (fun r => φ₁ (r, p.2) - φ₂ (r, p.2)) s 1) =
      (fun s => fderiv ℝ (fun r => φ₁ (r, p.2)) s 1 - fderiv ℝ (fun r => φ₂ (r, p.2)) s 1) := by
    ext s
    show (fderiv ℝ ((fun r => φ₁ (r, p.2)) - fun r => φ₂ (r, p.2)) s) 1 = _
    rw [fderiv_sub (hd1t s) (hd2t s), ContinuousLinearMap.sub_apply]
  have hspace_fn : ∀ i : Fin n, (fun y => fderiv ℝ (fun z => φ₁ (p.1, z) - φ₂ (p.1, z)) y (Pi.single i 1)) =
      (fun y => fderiv ℝ (fun z => φ₁ (p.1, z)) y (Pi.single i 1) - fderiv ℝ (fun z => φ₂ (p.1, z)) y (Pi.single i 1)) := by
    intro i; ext y
    show (fderiv ℝ ((fun z => φ₁ (p.1, z)) - fun z => φ₂ (p.1, z)) y) (Pi.single i 1) = _
    rw [fderiv_sub (hd1x y) (hd2x y), ContinuousLinearMap.sub_apply]
  rw [htime_fn]; simp_rw [hspace_fn]
  have houter_t :
    (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1 - (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) p.1) 1 =
    (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1) p.1) 1 - (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) p.1) 1 := by
    rw [show (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1 - (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) =
      ((fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1) - (fun s => (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1)) from rfl]
    rw [fderiv_sub (diff_outer_t' φ₁ hφ₁ p.2).differentiableAt (diff_outer_t' φ₂ hφ₂ p.2).differentiableAt,
        ContinuousLinearMap.sub_apply]
  have houter_x : ∀ i : Fin n,
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1) - (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) =
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) -
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) := by
    intro i
    rw [show (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1) - (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) =
      ((fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1)) - (fun y => (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1))) from rfl]
    rw [fderiv_sub (diff_outer_x' φ₁ hφ₁ p.1 i).differentiableAt (diff_outer_x' φ₂ hφ₂ p.1 i).differentiableAt,
        ContinuousLinearMap.sub_apply]
  rw [houter_t]; simp_rw [houter_x, Finset.sum_sub_distrib]
  ring

/-- Pointwise formula for the energy density of $\phi_1 - \phi_2$: each derivative of
the difference is the difference of the corresponding derivatives. -/
theorem fderiv_sub_energy_density {n : ℕ} (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) (x : Fin n → ℝ) :
    energyDensity (fun q => φ₁ q - φ₂ q) (0, x) =
      (1/2 : ℝ) * ((fderiv ℝ (fun s => φ₁ (s, x)) 0 1 - fderiv ℝ (fun s => φ₂ (s, x)) 0 1) ^ 2 +
        ∑ i : Fin n, (fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) -
                      fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1)) ^ 2) := by
  unfold energyDensity
  simp only []
  congr 1; congr 1
  · congr 1
    have hd1 : DifferentiableAt ℝ (fun s => φ₁ (s, x)) 0 :=
      ((hφ₁.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun s => φ₂ (s, x)) 0 :=
      ((hφ₂.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
    show (fderiv ℝ ((fun s => φ₁ (s, x)) - fun s => φ₂ (s, x)) 0) 1 = _
    rw [fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]
  · congr 1; ext i; congr 1
    have hd1 : DifferentiableAt ℝ (fun y => φ₁ (0, y)) x :=
      ((hφ₁.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y => φ₂ (0, y)) x :=
      ((hφ₂.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
    show (fderiv ℝ ((fun y => φ₁ (0, y)) - fun y => φ₂ (0, y)) x) (Pi.single i 1) = _
    rw [fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]

/-- If two $C^2$ scalar fields have identical initial data on the closed ball $\overline{B_R(x_0)}$,
then their spatial partial derivatives agree on that ball (using continuity to extend from
the interior to the boundary). -/
theorem same_data_spatial_deriv_eq {n : ℕ} (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (x₀ : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
    (x : Fin n → ℝ) (hx : waveEuclidNormSq (x - x₀) ≤ R ^ 2) (i : Fin n) :
    fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) =
      fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1) := by

  let g : (Fin n → ℝ) → ℝ := fun y => φ₁ (0, y) - φ₂ (0, y)
  suffices h : fderiv ℝ g x (Pi.single i 1) = 0 by
    have hd1 : DifferentiableAt ℝ (fun y => φ₁ (0, y)) x :=
      ((hφ₁.comp (contDiff_prodMk_right (0 : ℝ))).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y => φ₂ (0, y)) x :=
      ((hφ₂.comp (contDiff_prodMk_right (0 : ℝ))).differentiable (by decide)).differentiableAt
    rw [show fderiv ℝ g x = fderiv ℝ (fun y => φ₁ (0, y)) x - fderiv ℝ (fun y => φ₂ (0, y)) x
      from fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply] at h; linarith

  have hg : ContDiff ℝ 2 g :=
    (hφ₁.comp (contDiff_prodMk_right (0 : ℝ))).sub (hφ₂.comp (contDiff_prodMk_right (0 : ℝ)))

  have hg_zero : ∀ y, waveEuclidNormSq (y - x₀) ≤ R ^ 2 → g y = 0 :=
    fun y hy => sub_eq_zero.mpr (h_data y hy)

  have hS_open : IsOpen {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) < R ^ 2} :=
    isOpen_lt (continuous_finset_sum _ fun j _ => ((continuous_apply j).sub continuous_const).pow 2)
      continuous_const

  have hF_cont : Continuous (fun y => fderiv ℝ g y (Pi.single i 1)) := by
    show Continuous ((fun L : ((Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1)) ∘ (fderiv ℝ g))
    exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).continuous).comp
      (hg.continuous_fderiv (by decide))

  have hF_zero_int : ∀ y, waveEuclidNormSq (y - x₀) < R ^ 2 →
      fderiv ℝ g y (Pi.single i 1) = 0 := by
    intro y hy
    have h_eq : g =ᶠ[nhds y] 0 :=
      Filter.eventually_iff_exists_mem.mpr ⟨_, hS_open.mem_nhds hy, fun z hz => hg_zero z hz.le⟩
    simp [Filter.EventuallyEq.fderiv_eq h_eq]

  rcases lt_or_eq_of_le hx with h_int | h_bdy
  ·
    exact hF_zero_int x h_int
  ·
    by_cases hR2 : R ^ 2 ≤ 0
    ·
      exact absurd (not_le.mpr (sq_pos_of_pos hR)) (not_not.mpr hR2)
    ·
      simp only [not_le] at hR2
      let γ : ℝ → Fin n → ℝ := fun t j => x₀ j + (1 - t) * (x j - x₀ j)
      have hγ0 : γ 0 = x := by ext j; simp [γ]

      have hFγ_cont : ContinuousAt (fun t => fderiv ℝ g (γ t) (Pi.single i 1)) 0 :=
        hF_cont.continuousAt.comp (continuousAt_pi.mpr fun j => by
          simp only [γ]; exact continuousAt_const.add
            ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))

      have hγ_int : ∀ t, 0 < t → t < 1 → waveEuclidNormSq (γ t - x₀) < R ^ 2 := by
        intro t ht0 ht1
        show ∑ j, (γ t j - x₀ j) ^ 2 < R ^ 2
        simp only [γ, add_sub_cancel_left]
        conv_lhs => arg 2; ext j; rw [mul_pow]
        rw [← Finset.mul_sum, show ∑ j : Fin n, (x j - x₀ j) ^ 2 = R ^ 2 from h_bdy]
        have h1t : (1 - t) ^ 2 < 1 := by nlinarith
        have : (1 - t) ^ 2 * R ^ 2 < 1 * R ^ 2 := by nlinarith
        linarith

      rw [← hγ0]
      by_contra h_ne
      obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hFγ_cont _ (abs_pos.mpr h_ne)
      set t₀ := min (δ / 2) (1 / 2)
      have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ0) (by norm_num)
      have ht₀_lt_δ : dist t₀ 0 < δ := by
        simp [abs_of_pos ht₀_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ0)
      have ht₀_lt_1 : t₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have h1 := hδ ht₀_lt_δ
      rw [hF_zero_int _ (hγ_int t₀ ht₀_pos ht₀_lt_1)] at h1
      simp at h1

/-- If two $C^2$ scalar fields share the same data $(\phi_i, \partial_t \phi_i)|_{t=0}$ on
$\overline{B_R(x_0)}$, then the energy of their difference $\phi_1 - \phi_2$ at $t = 0$
on this ball is zero. -/
theorem same_data_zero_energy {n : ℕ}
    (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (x₀ : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
    (h_vel : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 →
      fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) :
    energyOnBall (fun q => φ₁ q - φ₂ q) 0 x₀ R = 0 := by
  unfold energyOnBall

  have h_integrand_zero : (fun x : Fin n → ℝ =>
      if waveEuclidNormSq (x - x₀) ≤ R ^ 2
      then energyDensity (fun q => φ₁ q - φ₂ q) (0, x) else 0) = 0 := by
    ext x
    simp only [Pi.zero_apply]
    split_ifs with hx
    · rw [fderiv_sub_energy_density φ₁ φ₂ hφ₁ hφ₂]
      have hvel := h_vel x hx
      have hspatial : ∀ i : Fin n,
          fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) =
          fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1) :=
        fun i => same_data_spatial_deriv_eq φ₁ φ₂ hφ₁ hφ₂ x₀ R hR h_data x hx i
      simp [hvel, hspatial]
    · rfl
  rw [h_integrand_zero]
  simp

/-- For a $C^2$ scalar field, the energy density restricted to the closed ball
$\overline{B_R(x_0)}$ at time $t$ is Lebesgue-integrable on $\mathbb{R}^n$, since the ball
is compact and the integrand is continuous. -/
theorem energyDensity_integrable_on_ball {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (t : ℝ) (x₀ : Fin n → ℝ) (R : ℝ) :
    Integrable (fun x : Fin n → ℝ =>
      if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0) := by

  set S := {x : Fin n → ℝ | waveEuclidNormSq (x - x₀) ≤ R ^ 2} with hS_def

  have hfun : (fun x : Fin n → ℝ =>
      if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0) =
    S.indicator (fun x => energyDensity φ (t, x)) := by
    ext x; simp only [S, Set.indicator, Set.mem_setOf_eq]
  rw [hfun]

  have hS_closed : IsClosed S := by
    have : S = (fun x => waveEuclidNormSq (x - x₀)) ⁻¹' Set.Iic (R ^ 2) := by
      ext x; simp [S, Set.mem_preimage, Set.mem_Iic]
    rw [this]
    apply IsClosed.preimage _ isClosed_Iic
    exact (continuous_finset_sum _ (fun i _ => (continuous_apply i |>.comp (continuous_id.sub continuous_const)).pow 2))

  have hS_bounded : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_ball x₀]
    refine ⟨|R| + 1, fun x hx => ?_⟩
    simp only [S, Set.mem_setOf_eq] at hx
    rw [Metric.mem_ball, dist_comm]
    have : ‖x - x₀‖ ≤ |R| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
      intro i
      have hi : (x - x₀) i ^ 2 ≤ R ^ 2 := by
        calc (x - x₀) i ^ 2
            ≤ ∑ j, (x - x₀) j ^ 2 := single_le_sum (fun j _ => sq_nonneg ((x - x₀) j)) (mem_univ i)
          _ = waveEuclidNormSq (x - x₀) := rfl
          _ ≤ R ^ 2 := hx
      rw [Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq (hi.trans (by rw [sq_abs])) (abs_nonneg R)
    calc dist x₀ x = ‖x₀ - x‖ := dist_eq_norm x₀ x
      _ = ‖-(x - x₀)‖ := by ring_nf
      _ = ‖x - x₀‖ := norm_neg _
      _ ≤ |R| := this
      _ < |R| + 1 := lt_add_one _
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded

  have hcont : Continuous (fun x : Fin n → ℝ => energyDensity φ (t, x)) := by
    unfold energyDensity
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.pow
      have hswap : ContDiff ℝ 2
          (Function.uncurry (fun (x : Fin n → ℝ) (s : ℝ) => φ (s, x))) := by
        show ContDiff ℝ 2 (φ ∘ Prod.swap)
        exact hφ.comp (contDiff_snd.prodMk contDiff_fst)
      exact (hswap.fderiv_apply (n := 0) contDiff_const contDiff_const
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)).continuous
    · apply continuous_finset_sum; intro i _
      apply Continuous.pow
      have h1 : ContDiff ℝ 2 (fun y : Fin n → ℝ => φ (t, y)) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp
        (h1.fderiv_right (m := 1) (by norm_num)).continuous)

  rw [integrable_indicator_iff hS_closed.measurableSet]
  exact ContinuousOn.integrableOn_compact hS_compact hcont.continuousOn

/-- If a continuous function $f$ is almost-everywhere zero on a set $S$, then it is zero
at every interior point of $S$. -/
lemma continuous_zero_of_ae_imp_on_interior {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {S : Set (Fin n → ℝ)}
    (hae : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ S → f x = 0)
    {x : Fin n → ℝ} (hx : x ∈ interior S) : f x = 0 := by
  by_contra h
  have hopen : IsOpen {y : Fin n → ℝ | f y ≠ 0} := isOpen_ne_fun hf continuous_const
  have hinter_open : IsOpen ({y | f y ≠ 0} ∩ interior S) := hopen.inter isOpen_interior
  have hinter_ne : ({y | f y ≠ 0} ∩ interior S).Nonempty := ⟨x, h, hx⟩
  have hpos := hinter_open.measure_pos (μ := (volume : Measure (Fin n → ℝ))) hinter_ne
  rw [ae_iff] at hae
  have hsub : {y | f y ≠ 0} ∩ interior S ⊆ {a | ¬(a ∈ S → f a = 0)} :=
    fun y ⟨hy1, hy2⟩ => fun hc => hy1 (hc (interior_subset hy2))
  exact absurd (le_antisymm (le_trans (measure_mono hsub) hae.le) (zero_le _)) (ne_of_gt hpos)

/-- A strict inequality $\|x - x_0\|^2 < r^2$ implies $x$ lies in the interior of the
closed Euclidean ball $\overline{B_r(x_0)}$. -/
lemma mem_interior_of_waveEuclidNormSq_lt {n : ℕ} {x₀ : Fin n → ℝ} {r : ℝ} {x : Fin n → ℝ}
    (hx : waveEuclidNormSq (x - x₀) < r ^ 2) :
    x ∈ interior {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) ≤ r ^ 2} := by
  have hcont : Continuous (fun y : Fin n → ℝ => waveEuclidNormSq (y - x₀)) :=
    (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)).comp
      (continuous_id.sub continuous_const)
  have hopen : IsOpen {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) < r ^ 2} :=
    isOpen_lt hcont continuous_const
  exact interior_mono
    (fun y (hy : waveEuclidNormSq (y - x₀) < r ^ 2) => le_of_lt hy)
    (hopen.subset_interior_iff.mpr le_rfl hx)

/-- If $\phi$ vanishes initially on $\overline{B_R(x_0)}$ and its time-derivative vanishes
almost-everywhere on the slice $B_{R-t}(x_0)$ for each $t \in [0, R]$, then $\phi(t, x) = 0$
throughout the backwards cone. The argument uses continuity to upgrade a.e. zero to
pointwise zero on the interior, then the fundamental theorem of calculus along
$s \mapsto \phi(s, x)$. -/
theorem zero_derivs_ae_imply_zero_field {n : ℕ} (φ : WaveScalarField n)
    (hφ_smooth : ContDiff ℝ 2 φ)
    (x₀ : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
    (hdt : ∀ t, 0 ≤ t → t ≤ R →
      ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
        fderiv ℝ (fun s => φ (s, x)) t 1 = 0)
    (_hdx : ∀ t, 0 ≤ t → t ≤ R →
      ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
        ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0)
    (t : ℝ) (ht0 : 0 ≤ t) (htR : t ≤ R)
    (x : Fin n → ℝ) (hx : waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2) :
    φ (t, x) = 0 := by

  set f := fun s => φ (s, x) with hf_def

  have hslice : ContDiff ℝ 2 f := hφ_smooth.comp (contDiff_id.prodMk contDiff_const)
  have hf_diff : Differentiable ℝ f := hslice.differentiable (by norm_num)

  have hf0 : f 0 = 0 := hφ_zero_init x (by nlinarith)

  have hdt_cont : ∀ s, Continuous (fun y : Fin n → ℝ => fderiv ℝ (fun s' => φ (s', y)) s 1) := by
    intro s
    have hswap : ContDiff ℝ 2 (Function.uncurry (fun (y : Fin n → ℝ) (s : ℝ) => φ (s, y))) := by
      show ContDiff ℝ 2 (φ ∘ Prod.swap)
      exact hφ_smooth.comp (contDiff_snd.prodMk contDiff_fst)
    exact (hswap.fderiv_apply (n := 0) contDiff_const contDiff_const
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)).continuous


  have hderiv_zero : ∀ s ∈ Ioo 0 t, HasDerivAt f 0 s := by
    intro s ⟨hs0, hst⟩
    have hhas : HasDerivAt f (fderiv ℝ f s 1) s := hf_diff.differentiableAt.hasDerivAt
    have hball_strict : waveEuclidNormSq (x - x₀) < (R - s) ^ 2 := by nlinarith
    have := continuous_zero_of_ae_imp_on_interior (hdt_cont s)
      (hdt s (le_of_lt hs0) (le_trans (le_of_lt hst) htR))
      (mem_interior_of_waveEuclidNormSq_lt hball_strict)
    rwa [this] at hhas

  have hftc : ∫ s in (0 : ℝ)..t, (0 : ℝ) = f t - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0
      hf_diff.continuous.continuousOn hderiv_zero intervalIntegrable_const
  simp at hftc
  linarith

/-- Pointwise nonnegativity of the energy density: $0 \leq \tfrac{1}{2}(|\partial_t\phi|^2 +
|\nabla_x\phi|^2)$. -/
lemma energyDensity_nonneg {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n) :
    0 ≤ energyDensity φ p := by
  unfold energyDensity
  apply mul_nonneg
  · norm_num
  · exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- If the energy density of $\phi$ vanishes at $(t, x)$, then both the time derivative and
all spatial derivatives of $\phi$ vanish at $(t, x)$. -/
lemma energyDensity_zero_derivs {n : ℕ} (φ : WaveScalarField n) (t : ℝ) (x : Fin n → ℝ)
    (h : energyDensity φ (t, x) = 0) :
    fderiv ℝ (fun s => φ (s, x)) t 1 = 0 ∧
    ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0 := by
  unfold energyDensity at h
  have half_ne : (1/2 : ℝ) ≠ 0 := by norm_num
  have h1 := (mul_eq_zero.mp h).resolve_left half_ne
  have ha2 : (fderiv ℝ (fun s => φ (s, x)) t 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (fderiv ℝ (fun s => φ (s, x)) t 1),
               Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
                 sq_nonneg (fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1)))]
  have hb_sum : ∑ j : Fin n, (fderiv ℝ (fun y => φ (t, y)) x (Pi.single j 1)) ^ 2 = 0 := by
    linarith
  constructor
  · nlinarith [ha2]
  · intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg (fderiv ℝ (fun y => φ (t, y)) x (Pi.single j 1)))).mp hb_sum i
        (Finset.mem_univ i)
    nlinarith [this]

/-- Energy coercivity: if $\phi$ vanishes initially on $\overline{B_R(x_0)}$ and the energy
on each cone-slice $B_{R-t}(x_0)$ vanishes for $0 \leq t \leq R$, then $\phi$ vanishes
throughout the solid backwards cone $\mathcal{C}_{x_0; R}$. -/
theorem energy_coercivity {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (x₀ : Fin n → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
    (hE : ∀ t, 0 ≤ t → t ≤ R → energyOnBall φ t x₀ (R - t) = 0) :
    ∀ t, 0 ≤ t → t ≤ R →
      ∀ x, waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → φ (t, x) = 0 := by

  have h_density_zero : ∀ t, 0 ≤ t → t ≤ R →
      ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → energyDensity φ (t, x) = 0 := by
    intro t ht0 htR
    have hEt := hE t ht0 htR
    have hnn : ∀ x : Fin n → ℝ,
        0 ≤ (if waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2
             then energyDensity φ (t, x) else 0) := by
      intro x; by_cases h : waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2
      · simp [h]; exact energyDensity_nonneg φ (t, x)
      · simp [h]
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hnn)
      (energyDensity_integrable_on_ball φ hφ t x₀ (R - t))).mp hEt
    filter_upwards [hae] with x hx hball
    simp [hball] at hx
    exact hx

  have hdt : ∀ t, 0 ≤ t → t ≤ R →
      ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
        fderiv ℝ (fun s => φ (s, x)) t 1 = 0 := by
    intro t ht0 htR
    filter_upwards [h_density_zero t ht0 htR] with x hx hball
    exact (energyDensity_zero_derivs φ t x (hx hball)).1
  have hdx : ∀ t, 0 ≤ t → t ≤ R →
      ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
        ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0 := by
    intro t ht0 htR
    filter_upwards [h_density_zero t ht0 htR] with x hx hball
    exact (energyDensity_zero_derivs φ t x (hx hball)).2

  intro t ht0 htR x hx
  exact zero_derivs_ae_imply_zero_field φ hφ x₀ R hR hφ_zero_init hdt hdx t ht0 htR x hx

/-- Restatement of $\square_m$-linearity:
$\square_m(\phi_1 - \phi_2) = \square_m \phi_1 - \square_m \phi_2$. -/
theorem waveOp_sub {n : ℕ} (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) (p : WaveSpacetime n) :
    waveOp (fun q => φ₁ q - φ₂ q) p = waveOp φ₁ p - waveOp φ₂ p :=
  waveOp_linearity_sub φ₁ φ₂ hφ₁ hφ₂ p

/-- Restatement of `same_data_zero_energy`: same initial data implies zero initial energy
of the difference. -/
theorem energyOnBall_zero_of_same_data {n : ℕ}
    (φ₁ φ₂ : WaveScalarField n)
    (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (x₀ : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
    (h_vel : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 →
      fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) :
    energyOnBall (fun q => φ₁ q - φ₂ q) 0 x₀ R = 0 :=
  same_data_zero_energy φ₁ φ₂ hφ₁ hφ₂ x₀ R hR h_data h_vel

/-- Nonnegativity of the energy on a ball:
$E[\phi](t) = \int_{B_R(x_0)} \tfrac{1}{2}(|\partial_t\phi|^2 + |\nabla\phi|^2)\, dx \geq 0$. -/
theorem energyOnBall_nonneg {n : ℕ} (φ : WaveScalarField n) (t : ℝ)
    (x₀ : Fin n → ℝ) (R : ℝ) :
    0 ≤ energyOnBall φ t x₀ R := by
  unfold energyOnBall
  apply integral_nonneg
  intro x
  simp only [Pi.zero_apply]
  split_ifs with h
  · unfold energyDensity
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
    apply add_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact le_refl _

/-- Restatement of `energy_coercivity`: zero energy on each cone-slice (and vanishing
initial data) implies $\phi \equiv 0$ on the solid backwards cone. -/
theorem zero_energy_implies_zero {n : ℕ} (φ : WaveScalarField n)
    (hφ : ContDiff ℝ 2 φ) (x₀ : Fin n → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
    (hE : ∀ t, 0 ≤ t → t ≤ R → energyOnBall φ t x₀ (R - t) = 0) :
    ∀ t, 0 ≤ t → t ≤ R →
      ∀ x, waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → φ (t, x) = 0 :=
  energy_coercivity φ hφ x₀ R hR hφ_zero_init hE


/-- **Definition 3.0.3 (Future development).** A future region $\Omega \subset \mathbb{R}^{1+n}$
with $t \geq 0$ is a future development of $S \subset \{t = 0\}$ if any two $C^2$ wave-equation
solutions whose initial data agree on $S$ also agree on $\Omega$. -/
def IsDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) (Ω : Set (WaveSpacetime n)) : Prop :=
  (∀ p ∈ Ω, p.1 ≥ 0) ∧
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ x ∈ S, φ₁ (0, x) = φ₂ (0, x)) →
    (∀ x ∈ S, fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- The past-development variant of `IsDevelopment`: $\Omega \subset \{t \leq 0\}$ such that
identical initial data on $S$ force agreement throughout $\Omega$. -/
def IsPastDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) (Ω : Set (WaveSpacetime n)) : Prop :=
  (∀ p ∈ Ω, p.1 ≤ 0) ∧
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ x ∈ S, φ₁ (0, x) = φ₂ (0, x)) →
    (∀ x ∈ S, fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- **Definition 3.0.4 (Maximal future development).** The maximal future development of $S$,
denoted $\mathcal{D}^+(S)$, is the union of all future developments of $S$. -/
def maximalDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  ⋃₀ { Ω | IsDevelopment S Ω }

/-- The maximal past development of $S$, $\mathcal{D}^-(S)$, defined as the union of all
past developments of $S$. -/
def maximalPastDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  ⋃₀ { Ω | IsPastDevelopment S Ω }

/-- The (total) maximal development of $S$: $\mathcal{D}^+(S) \cup \mathcal{D}^-(S)$. -/
def maximalTotalDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  maximalDevelopment S ∪ maximalPastDevelopment S

/-- **Definition 3.0.5 (Domain of dependence).** A set $S \subset \mathbb{R}^{1+n}$ is a
domain of dependence for $\Omega$ if any two $C^2$ wave-equation solutions which agree
together with all of their first-order partial derivatives on $S$ also agree on $\Omega$. -/
def IsDomainOfDependence {n : ℕ} (Ω : Set (WaveSpacetime n)) (S : Set (WaveSpacetime n)) : Prop :=
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ p ∈ S, φ₁ p = φ₂ p) →
    (∀ p ∈ S, ∀ μ : Fin (n + 1), partialDeriv φ₁ μ p = partialDeriv φ₂ μ p) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- **Definition 3.0.6 (Range of influence).** The range of influence of $S$ is the set of
all spacetime points $p$ where some pair of $C^2$ wave-equation solutions, which agree
together with their partial derivatives off of $S$, nevertheless disagree at $p$. -/
def rangeOfInfluence {n : ℕ} (S : Set (WaveSpacetime n)) : Set (WaveSpacetime n) :=
  { p | ¬ ∀ (φ₁ φ₂ : WaveScalarField n),
      (∀ q, waveOp φ₁ q = 0) →
      (∀ q, waveOp φ₂ q = 0) →
      ContDiff ℝ 2 φ₁ →
      ContDiff ℝ 2 φ₂ →
      (∀ q, q ∉ S → φ₁ q = φ₂ q) →
      (∀ q, q ∉ S → ∀ μ : Fin (n + 1), partialDeriv φ₁ μ q = partialDeriv φ₂ μ q) →
      φ₁ p = φ₂ p }

end CM14

end
