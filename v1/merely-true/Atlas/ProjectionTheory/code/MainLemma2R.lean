/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section

open MeasureTheory Metric Set Finset
open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The perpendicular direction in $\mathbb{R}^2$: rotates a vector $(e_0, e_1)$ to
$(-e_1, e_0)$. -/
def perpDir (e : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
    if i = (0 : Fin 2) then -(EuclideanSpace.equiv (Fin 2) ℝ e 1)
    else EuclideanSpace.equiv (Fin 2) ℝ e 0)

/-- The rectangle in $\mathbb{R}^2$ centered at `center` with major axis along `dir`,
of half-length `halfLength` along `dir` and half-width `halfWidth` along `perpDir dir`. -/
def rectangleSet (center : EuclideanSpace ℝ (Fin 2))
    (dir : EuclideanSpace ℝ (Fin 2)) (halfWidth halfLength : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |⟪x - center, dir⟫_ℝ| ≤ halfLength ∧
       |⟪x - center, perpDir dir⟫_ℝ| ≤ halfWidth}

/-- A $1 \times R$ tube in $\mathbb{R}^2$: a long, thin rectangle with unit direction
vector, length `R ≥ 1`, and width $1$. -/
structure Tube where
  R : ℝ
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1
  hR : 1 ≤ R

/-- Realize a `Tube` as the set $\{x \in \mathbb{R}^2 : |\langle x - c, d\rangle| \leq R/2,
\ |\langle x - c, d^\perp\rangle| \leq 1/2\}$. -/
def Tube.asSet (T : Tube) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleSet T.center T.direction (1/2) (T.R/2)

/-- The two-dimensional Fourier transform $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x,
\xi\rangle}\, dx$ of a real-valued function on $\mathbb{R}^2$, returning a complex value. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) (fun x => (f x : ℂ)) ξ

/-- The set of dyadic scales between $1$ and $R$: $\{2^k : k \in \mathbb{N}, 1 \leq 2^k \leq R\}$. -/
def dyadicScales (R : ℝ) : Set ℝ :=
  {r : ℝ | ∃ k : ℕ, r = 2 ^ k ∧ 1 ≤ r ∧ r ≤ R}

/-- A collection of $1 \times R$ tubes in $\mathbb{R}^2$ together with smooth bump
functions $\psi_i$ adapted to each tube and a (compactly supported) Fourier bound.
This is the data $f = \sum_T \psi_T$ used in the real-version Main Lemma 2R. -/
structure TubeCollection where
  R : ℝ
  hR : 1 ≤ R
  ι : Type
  [hι : Fintype ι]
  tubes : ι → Tube
  tubes_scale : ∀ i, (tubes i).R = R
  ψ : ι → (EuclideanSpace ℝ (Fin 2) → ℝ)
  ψ_smooth : ∀ i, ContDiff ℝ ⊤ (ψ i)
  ψ_integrable : ∀ i, Integrable (ψ i) volume
  fourierSupportBound : ℝ
  ψ_fourier_compact_support : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > fourierSupportBound → fourierTransformR2 (ψ i) ξ = 0

/-- The index type of a `TubeCollection` is a `Fintype`. -/
instance (S : TubeCollection) : Fintype S.ι := S.hι

/-- The aggregated tube sum $f(x) = \sum_i \psi_i(x)$. -/
def TubeCollection.tubeSum (S : TubeCollection) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i : S.ι, S.ψ i x

/-- The number of tubes in `S` contained in the $r \times R$ rectangle with center `c`
and direction `d`. -/
def TubeCollection.countContained (S : TubeCollection) (r : ℝ)
    (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.filter fun j =>
    (S.tubes j).asSet ⊆ rectangleSet c d r S.R).card

/-- The multiplicity at scale $r$: the maximum, over all $r \times R$ rectangles, of the
number of tubes of `S` contained in that rectangle. -/
def TubeCollection.multiplicity (S : TubeCollection) (r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)),
    n = S.countContained r c d}

/-- A frequency decomposition $f = \sum_{r} f_r$ of the tube sum into pieces with
Fourier support in $\{|\xi| \leq 1/r\}$, satisfying a near-orthogonality $L^2$ bound. -/
structure FrequencyDecomposition (S : TubeCollection) where
  f_r : ℝ → (EuclideanSpace ℝ (Fin 2) → ℝ)
  scales : Finset ℝ
  scales_range : ∀ r ∈ scales, r ∈ dyadicScales S.R
  sum_eq : ∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x
  fourier_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0
  near_orthogonality : ∃ (C_orth : ℝ), 0 < C_orth ∧
    ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 ≤ C_orth * ∫ x, (S.tubeSum x) ^ 2






/-- Expanding the $L^2$ norm of a finite sum as a sum of pairwise integrals:
$\int (\sum_i \varphi_i)^2 = \sum_{i,j} \int \varphi_i \varphi_j$. -/
theorem l2_norm_bilinear_expansion
    {ι : Type} [Fintype ι]
    (φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ : ∀ i j, Integrable (fun x => φ i x * φ j x) volume) :
    ∫ x, (∑ i : ι, φ i x) ^ 2 =
      ∑ i : ι, ∑ j : ι, ∫ x, φ i x * φ j x := by
  have h_pw : ∀ x, (∑ i : ι, φ i x) ^ 2 = ∑ i : ι, ∑ j : ι, φ i x * φ j x := by
    intro x
    rw [sq, Finset.sum_mul]
    congr 1; ext i; rw [Finset.mul_sum]
  simp_rw [h_pw]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hφ i j))]
  congr 1; ext i
  rw [integral_finset_sum _ (fun j _ => hφ i j)]

/-- Per-tube row sum bound: each row $\sum_j |\langle \varphi_i, \varphi_j\rangle|$ is
controlled by `multiplicity r` (the count of $\varphi_j$ that can interact with
$\varphi_i$) times the diagonal bound $R/r$. -/
theorem tube_inner_product_multiplicity_bound
    (S : TubeCollection) (r : ℝ) (hr_scale : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_inner_bound : ∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r)
    (hφ_sparse : ∀ i, (Finset.univ.filter (fun j =>
      (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r) :
    ∀ i : S.ι,
      ∑ j : S.ι, |∫ x, φ i x * φ j x| ≤
        (S.multiplicity r : ℝ) * (S.R / r) := by
  intro i

  have hRr : (0 : ℝ) ≤ S.R / r := by
    apply div_nonneg
    · linarith [S.hR]
    · obtain ⟨k, _, hk1, _⟩ := hr_scale; linarith

  calc ∑ j : S.ι, |∫ x, φ i x * φ j x|
      = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          |∫ x, φ i x * φ j x|
        + ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
          |∫ x, φ i x * φ j x| := by
        rw [Finset.sum_filter_add_sum_filter_not]

    _ = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          |∫ x, φ i x * φ j x| := by
        have h0 : ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
            |∫ x, φ i x * φ j x| = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
          rw [hj, abs_zero]
        linarith

    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          (S.R / r) := by
        apply Finset.sum_le_sum; intro j _; exact hφ_inner_bound i j
    _ = (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card
          * (S.R / r) := by
        rw [Finset.sum_const, nsmul_eq_mul]

    _ ≤ (S.multiplicity r : ℝ) * (S.R / r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hφ_sparse i
        · exact hRr

/-- Per-scale $L^2$ bound: given a tube-localized representation
$f_r = \sum_i \varphi_i$ with per-tube energy $\leq R/r$ and bounded multiplicity at
scale $r$, we obtain $\int f_r^2 \leq |S.\iota| \cdot \mathrm{mult}(r) \cdot (R/r)$. -/
theorem per_scale_l2_bound
    (S : TubeCollection) (r : ℝ)
    (hr_scale : r ∈ dyadicScales S.R)
    (f_r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (h_fourier : ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 f_r ξ = 0)
    (h_tube_decomp : ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ i, Integrable (φ i) volume) ∧
      (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
      (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
      (∀ x, f_r x = ∑ i : S.ι, φ i x) ∧
      (∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r) ∧
      (∀ i, (Finset.univ.filter (fun j =>
        (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r)) :
    ∫ x, (f_r x) ^ 2 ≤
      (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by

  obtain ⟨φ, _, hφ_prod_int, hφ_freq, hφ_sum, hφ_inner, hφ_sparse⟩ := h_tube_decomp

  have h_expand : ∫ x, (f_r x) ^ 2 = ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x := by
    conv_lhs => rw [show f_r = fun x => ∑ i : S.ι, φ i x from funext hφ_sum]
    exact l2_norm_bilinear_expansion φ hφ_prod_int


  have h_ortho := tube_inner_product_multiplicity_bound S r hr_scale φ hφ_freq hφ_inner hφ_sparse

  rw [h_expand]
  calc ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x
      ≤ ∑ i : S.ι, ∑ j : S.ι, |∫ x, φ i x * φ j x| := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact le_abs_self _
    _ = ∑ i : S.ι, (∑ j : S.ι, |∫ x, φ i x * φ j x|) := rfl
    _ ≤ ∑ i : S.ι, ((S.multiplicity r : ℝ) * (S.R / r)) := by
        apply Finset.sum_le_sum; intro i _; exact h_ortho i
    _ = (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Cauchy–Schwarz via the AM–GM inequality: if $\int f^2, \int g^2 \leq A$ then
$|\int fg| \leq A$. -/
theorem abs_integral_mul_le_of_sq_integral_le
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f g : α → ℝ)
    (hf2_int : Integrable (fun x => (f x) ^ 2) μ)
    (hg2_int : Integrable (fun x => (g x) ^ 2) μ)
    (A : ℝ)
    (hf_bound : ∫ x, (f x) ^ 2 ∂μ ≤ A)
    (hg_bound : ∫ x, (g x) ^ 2 ∂μ ≤ A) :
    |∫ x, f x * g x ∂μ| ≤ A := by

  have h1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) (fun x => f x * g x)
    simp only [Real.norm_eq_abs] at this
    exact this

  have h2 : ∫ x, |f x * g x| ∂μ ≤ ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => abs_nonneg _)
    · exact (hf2_int.add hg2_int).div_const 2
    · apply ae_of_all _; intro x
      simp only
      rw [abs_mul]
      have := two_mul_le_add_sq (|f x|) (|g x|)
      rw [sq_abs, sq_abs] at this
      linarith

  have h3 : ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ ≤ A := by
    rw [integral_div, integral_add hf2_int hg2_int]
    linarith
  linarith





/-- Recover a per-tube $L^2$ bound $\int \varphi_i^2 \leq R/r$ from a pointwise
domination by integrable amplitudes $g_i$ with $\int g_i \leq R/r$. -/
theorem self_norm_from_amplitude
    {ι : Type} [Fintype ι]
    (φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (R r : ℝ)
    (hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume)
    (g : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg_int : ∀ i, Integrable (g i) volume)
    (h_pw : ∀ i, ∀ x, (φ i x) ^ 2 ≤ g i x)
    (h_integral_bound : ∀ i, ∫ x, g i x ≤ R / r) :
    ∀ i, ∫ x, (φ i x) ^ 2 ≤ R / r := by
  intro i
  calc ∫ x, (φ i x) ^ 2 ≤ ∫ x, g i x := by
        apply integral_mono (hφ_sq_int i) (hg_int i)
        intro x; exact h_pw i x
    _ ≤ R / r := h_integral_bound i











end ProjectionTheory

end
