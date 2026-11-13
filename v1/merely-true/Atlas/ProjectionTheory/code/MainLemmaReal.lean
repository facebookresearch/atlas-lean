/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Metric Set

noncomputable section

namespace FrequencyDecomposition

/-- Short alias for the Euclidean plane $\mathbb{R}^2$. -/
abbrev ℝ2 := EuclideanSpace ℝ (Fin 2)

/-- A $1 \times R$ tube in $\mathbb{R}^2$: an oriented rectangle of length $R \geq 1$
and width $1$, specified by its center and direction angle. -/
structure Tube where
  center : ℝ2
  direction : ℝ
  R : ℝ
  hR : 1 ≤ R

/-- A generic axis-aligned-along-direction rectangle in $\mathbb{R}^2$, with arbitrary
`halfWidth` and `halfLength`, used to contain bundles of $1 \times R$ tubes. -/
structure WideTube where
  center : ℝ2
  direction : ℝ
  halfWidth : ℝ
  halfLength : ℝ

/-- Realize a tube $T$ as the rectangle of half-length $R/2$ along direction $\theta$
and half-width $1/2$ along the perpendicular. -/
def Tube.toSet (T : Tube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - T.center)
       let θ := T.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ T.R / 2 ∧ |shortCoord| ≤ 1 / 2}

/-- Realize a `WideTube` as the corresponding rectangle in $\mathbb{R}^2$. -/
def WideTube.toSet (W : WideTube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - W.center)
       let θ := W.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ W.halfLength ∧ |shortCoord| ≤ W.halfWidth}

/-- A tube $T$ is contained in a wide tube $W$ if the rectangle of $T$ lies inside $W$. -/
def Tube.containedIn (T : Tube) (W : WideTube) : Prop :=
  T.toSet ⊆ W.toSet

/-- The dyadic scales up to $R$: $\{2^k : k \in \mathbb{N}, 2^k \leq R\}$ as a `Finset`. -/
def dyadicRange (R : ℝ) : Finset ℝ :=
  ((Finset.range (Nat.log 2 ⌊R⌋₊ + 1)).image (fun k => (2 : ℝ) ^ k)).filter (· ≤ R)

open Classical in
/-- Tube covering number $N_\mathcal{T}(r) = \max_W |\{T \in \mathcal{T} : T \subseteq W\}|$,
maximizing over $r \times R$ wide tubes $W$. -/
def tubeCoveringNumber (𝒯 : Finset Tube) (R r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
    n = (𝒯.filter (fun T => T.containedIn W)).card}

/-- The $L^2$ norm squared $\|f\|_{L^2}^2 = \int_{\mathbb{R}^2} |f(x)|^2\, dx$. -/
def l2NormSq (f : ℝ2 → ℂ) : ℝ :=
  ∫ x, ‖f x‖ ^ 2

/-- The support of the Fourier transform of `f` in $\mathbb{R}^2$. -/
def fourierSupport (f : ℝ2 → ℂ) : Set ℝ2 :=
  Function.support (FourierTransform.fourier f)

/-- The cumulative frequency projection $P_{\leq 1/r} f$: the inverse Fourier transform
of $\hat f(\xi) \cdot \mathbf{1}_{|\xi| \leq 1/r}$. -/
def cumulativeFreqProj (f : ℝ2 → ℂ) (r : ℝ) : ℝ2 → ℂ :=
  FourierTransformInv.fourierInv
    (fun ξ => (FourierTransform.fourier f) ξ * (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0))

/-- The $k$-th Littlewood–Paley piece of $f$ at depth $K$:
$\Delta_k f = P_{\leq 2^{-k}} f - P_{\leq 2^{-(k+1)}} f$ for $k < K$, and the final
endpoint $P_{\leq 2^{-K}} f$ when $k = K$ (with $f$ itself when $k = 0$). -/
def littlewoodPaleyPieceK (f : ℝ2 → ℂ) (K k : ℕ) (x : ℝ2) : ℂ :=
  let g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  if k < K then g k - g (k + 1) else g K

/-- Littlewood–Paley telescoping identity: $f(x) = \sum_{k=0}^{K} \Delta_k f(x)$. -/
theorem littlewoodPaleyPieceK_sum (f : ℝ2 → ℂ) (K : ℕ) (x : ℝ2) :
    ∑ k ∈ Finset.range (K + 1), littlewoodPaleyPieceK f K k x = f x := by
  simp only [littlewoodPaleyPieceK]
  set g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  rw [Finset.sum_range_succ]
  simp only [show ¬ (K < K) from lt_irrefl K, ite_false]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
  rw [show (fun k => g k - g (k + 1)) = (fun k => -(g (k + 1) - g k)) from by ext; ring]
  rw [Finset.sum_neg_distrib, Finset.sum_range_sub]
  simp only [g, if_true]; ring

/-- The natural logarithm base 2 of $\lfloor 2^k \rfloor$ equals $k$. -/
lemma nat_log_two_pow (k : ℕ) : Nat.log 2 ⌊((2 : ℝ) ^ k)⌋₊ = k := by
  rw [show ((2:ℝ) ^ k) = ((2:ℕ) ^ k : ℕ) from by push_cast; ring, Nat.floor_natCast]
  exact Nat.log_pow (by norm_num : 1 < 2) k

/-- If $k \leq \log_2 \lfloor R \rfloor$ then $2^k \leq R$. -/
lemma two_pow_le_of_mem_range (k : ℕ) (R : ℝ) (hR : 1 ≤ R) (hk : k < Nat.log 2 ⌊R⌋₊ + 1) :
    (2:ℝ) ^ k ≤ R := by
  have hk' : k ≤ Nat.log 2 ⌊R⌋₊ := Nat.lt_succ_iff.mp hk
  have hne : ⌊R⌋₊ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hR)
  have h2k : (2:ℕ) ^ k ≤ ⌊R⌋₊ :=
    (Nat.pow_le_pow_right (by norm_num) hk').trans (Nat.pow_log_le_self 2 hne)
  calc (2:ℝ) ^ k = ((2:ℕ)^k : ℕ) := by push_cast; ring
    _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h2k
    _ ≤ R := Nat.floor_le (by linarith)

/-- Injectivity of $k \mapsto 2^k$ on $\mathbb{N}$ (viewed in $\mathbb{R}$). -/
lemma two_pow_injective : Function.Injective (fun k : ℕ => (2:ℝ) ^ k) := by
  intro a b h
  have h2 : ((2:ℕ)^a : ℝ) = ((2:ℕ)^b : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (by norm_num : 2 ≥ 2) (by exact_mod_cast h2)

/-- The Littlewood–Paley piece $f_r$ at dyadic scale $r$ of the tube sum
$f = \sum_T \varphi_T$, indexed by the integer $\log_2 r$. -/
def littlewoodPaleyPiece (𝒯 : Finset Tube) (φ : Tube → ℝ2 → ℂ) (R r : ℝ) : ℝ2 → ℂ :=
  let f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  fun x => littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) (Nat.log 2 ⌊r⌋₊) x

/-- Bundle of frequency-decomposition data for the tube sum $f = \sum_T \varphi_T$:
the pieces $f_r$ at dyadic scales, Fourier support inside $\{|\xi| \leq 1/r\}$, and
the per-scale $L^2$ estimate $\|f_r\|_{L^2}^2 \leq C \cdot N_\mathcal{T}(r) \cdot
|\mathcal{T}| / r \cdot R$. -/
structure FrequencyDecompositionData (𝒯 : Finset Tube) (R : ℝ) where
  φ : Tube → ℝ2 → ℂ
  f_r : ℝ → ℝ2 → ℂ
  f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  decomposition : ∀ x, f x = ∑ r ∈ dyadicRange R, f_r r x
  freq_support : ∀ r ∈ dyadicRange R,
    fourierSupport (f_r r) ⊆ Metric.closedBall 0 (1 / r)
  C : ℝ
  hC : 0 < C
  l2_estimate : ∀ r ∈ dyadicRange R,
    l2NormSq (f_r r) ≤ C * (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * r⁻¹ * R

/-- The tube sum reconstructs from its Littlewood–Paley pieces:
$\sum_{T \in \mathcal{T}} \varphi_T(x) = \sum_{r \in \text{dyadicRange}(R)} f_r(x)$. -/
theorem littlewoodPaley_decomposition
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
    ∀ x, (fun x => ∑ T ∈ 𝒯, φ T x) x =
      ∑ r ∈ dyadicRange R, littlewoodPaleyPiece 𝒯 φ R r x := by
  intro x
  set f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  rw [show f x = ∑ k ∈ Finset.range (Nat.log 2 ⌊R⌋₊ + 1),
      littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) k x
    from (littlewoodPaleyPieceK_sum f (Nat.log 2 ⌊R⌋₊) x).symm]
  simp only [littlewoodPaleyPiece, dyadicRange]
  rw [Finset.sum_filter, Finset.sum_image (fun k₁ _ k₂ _ h => two_pow_injective h)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [two_pow_le_of_mem_range k R hR (Finset.mem_range.mp hk), ite_true, nat_log_two_pow]
  rfl




/-- The annular difference $\hat f \cdot (\mathbf 1_{B_{1/2^k}} - \mathbf 1_{B_{1/2^{k+1}}})$
is supported in the ball of radius $1/2^k$. -/
lemma annular_support_in_ball (f : ℝ2 → ℂ) (k : ℕ) :
    Function.support (fun ξ => (FourierTransform.fourier f) ξ *
      (if dist ξ 0 ≤ 1 / (2:ℝ) ^ k then (1:ℂ) else 0) -
      (FourierTransform.fourier f) ξ *
      (if dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1) then (1:ℂ) else 0)) ⊆
      Metric.closedBall 0 (1 / (2:ℝ) ^ k) := by
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  rw [Metric.mem_closedBall]
  by_contra h
  push_neg at h
  have h' : dist ξ 0 > 1 / (2:ℝ) ^ k := by linarith [dist_comm (0 : ℝ2) ξ]
  have h1 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ k) := not_le.mpr h'
  have h2 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1)) := by
    apply not_le.mpr
    have hpow : (2:ℝ) ^ k ≤ (2:ℝ) ^ (k+1) := by gcongr <;> [norm_num; omega]
    have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le (by positivity) hpow
    linarith
  simp only [h1, h2, ite_false, mul_zero, sub_self] at hξ
  exact hξ rfl




/-- Every element of `dyadicRange R` is strictly positive (it is a power of $2$). -/
lemma pos_of_mem_dyadicRange {R r : ℝ} (hr : r ∈ dyadicRange R) : 0 < r := by
  simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨⟨k, _, hk⟩, _⟩ := hr
  rw [← hk]; positivity











/-- The pairwise interaction $\langle g, F\rangle_{\mathbb R} = \mathrm{Re} \int
\overline{g(x)} F(x)\, dx$ between two complex-valued functions. -/
def tubeInteraction (g F : ℝ2 → ℂ) : ℝ :=
  ∫ x, ((starRingEnd ℂ) (g x) * F x).re

/-- Pointwise expansion of $\|\sum_T g(T)\|^2$ as $\sum_T \mathrm{Re}(\overline{g(T)}
\sum_{T'} g(T'))$. -/
lemma norm_sq_sum_eq_sum_re_tube (𝒯 : Finset Tube) (g : Tube → ℂ) :
    ‖∑ T ∈ 𝒯, g T‖ ^ 2 = ∑ T ∈ 𝒯, ((starRingEnd ℂ) (g T) * ∑ T' ∈ 𝒯, g T').re := by
  have h1 := Complex.sq_norm (∑ T ∈ 𝒯, g T)
  rw [h1]
  have h2 : ∀ z : ℂ, Complex.normSq z = ((starRingEnd ℂ) z * z).re := by
    intro z; simp [Complex.normSq]
  rw [h2, map_sum (starRingEnd ℂ), Finset.sum_mul]
  simp only [Complex.re_sum]

/-- $L^2$ norm of a tube sum equals the sum of tube interactions:
$\|\sum_T g_T\|_{L^2}^2 = \sum_T \langle g_T, \sum_{T'} g_{T'}\rangle$. -/
lemma l2NormSq_sum_eq_sum_interaction (𝒯 : Finset Tube) (g : Tube → ℝ2 → ℂ)
    (hint : ∀ T ∈ 𝒯, Integrable (fun x => ((starRingEnd ℂ) (g T x) *
      ∑ T' ∈ 𝒯, g T' x).re) volume) :
    l2NormSq (fun x => ∑ T ∈ 𝒯, g T x) =
    ∑ T ∈ 𝒯, tubeInteraction (g T) (fun x => ∑ T' ∈ 𝒯, g T' x) := by
  unfold l2NormSq tubeInteraction
  simp_rw [norm_sq_sum_eq_sum_re_tube 𝒯 (fun T => g T _)]
  exact integral_finset_sum 𝒯 hint















end FrequencyDecomposition
