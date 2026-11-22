/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Haar.Unique

variable {T : ℝ} [hT : Fact (0 < T)]

open MeasureTheory AddCircle Finset Filter Complex

namespace FourierSeries

/-- The `N`-th partial Fourier sum of a function `f : AddCircle T → ℂ`, defined as
`S_N f(x) = ∑_{n = -N}^{N} ĉ_n(f) · e^{2πi n x / T}`, where `ĉ_n(f) = fourierCoeff f n`. -/
noncomputable def partialFourierSum (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- The `N`-th Cesàro–Fourier mean of `f`, given by
`σ_N f(x) = (N+1)⁻¹ · ∑_{k=0}^{N} S_k f(x)`,
where `S_k f` is the `k`-th partial Fourier sum. -/
noncomputable def cesaroFourierMean (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1), partialFourierSum f k x

/-- The Fejér kernel `K_N`, defined here as the Cesàro mean of the Dirichlet kernels:
`K_N(x) = (N+1)⁻¹ · ∑_{k=0}^{N} ∑_{n=-k}^{k} e^{2πi n x / T}`. Equivalently (after
algebra), `K_N(x) = (N+1)⁻¹ · (sin((N+1)x/2) / sin(x/2))²` away from the origin. -/
noncomputable def fejerKernel (N : ℕ) : AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1),
    ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x

/-- Each Fourier mode `t ↦ e^{2πi n t / T}` is integrable on the circle (in fact
bounded by `1`); used repeatedly when integrating Fourier sums termwise. -/
theorem fourier_integrable (n : ℤ) :
    Integrable (fun t : AddCircle T => (fourier n t : ℂ)) haarAddCircle :=
  Integrable.of_bound (C := 1) (map_continuous (fourier n)).aestronglyMeasurable
    (ae_of_all _ (fun t => by rw [fourier_apply, Circle.norm_coe]))

/-- Orthogonality of the Fourier basis with respect to the Haar measure: the integral
of `e^{2πi n t / T}` over the circle equals `1` if `n = 0` and `0` otherwise. -/
theorem integral_fourier (n : ℤ) :
    ∫ t : AddCircle T, fourier n t ∂haarAddCircle =
    if n = 0 then 1 else 0 := by
  have h := fourierCoeff_fourier (T := T) 0
  have hn := congr_fun h (-n)
  simp only [Pi.single_apply, fourierCoeff] at hn
  simp only [neg_neg] at hn
  have h0 : ∀ t : AddCircle T, (fourier n t : ℂ) • (fourier (0 : ℤ) t : ℂ) = fourier n t := by
    intro t; simp [fourier_apply, zero_smul]
  simp only [h0] at hn
  simp only [show (-n = (0 : ℤ)) ↔ (n = 0) from neg_eq_zero] at hn
  exact hn

/-- The integral of the `k`-th Dirichlet kernel `∑_{n=-k}^{k} e^{2πi n t / T}` over
the circle equals `1`; only the `n = 0` term contributes by orthogonality. -/
theorem integral_dirichlet_sum (k : ℕ) :
    ∫ t : AddCircle T, ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      fourier n t ∂haarAddCircle = 1 := by
  rw [integral_finset_sum _ (fun n _ => fourier_integrable n)]
  simp only [integral_fourier]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) := by simp
  rw [← Finset.add_sum_erase _ _ h0, if_pos rfl]
  have : ∑ x ∈ (Finset.Icc (-(k : ℤ)) (k : ℤ)).erase 0,
      (if x = (0 : ℤ) then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_erase] at hn
    simp [hn.1]
  rw [this, add_zero]

set_option linter.unusedSectionVars false in
/-- Symmetry of the Fejér kernel: `K_N(-x) = K_N(x)` for every `x ∈ AddCircle T`. -/
theorem fejerKernel_symmetric (N : ℕ) (x : AddCircle T) :
    fejerKernel N (-x) = fejerKernel N x := by
  unfold fejerKernel
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have key : ∀ n : ℤ, n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) →
      (fourier n) (-x) = (fourier (-n)) x := by
    intros n _
    simp [fourier_apply, neg_smul]
  rw [Finset.sum_congr rfl (fun n hn => key n hn)]
  rw [← Finset.sum_equiv (Equiv.neg ℤ) (s := Finset.Icc (-(k : ℤ)) (k : ℤ))
    (t := Finset.Icc (-(k : ℤ)) (k : ℤ))]
  · intro n
    simp only [Equiv.neg_apply, Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · intro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · intro n _
    simp [Equiv.neg_apply]

/-- The Fejér kernel integrates to `1` on the circle:
`∫_{AddCircle T} K_N(t) dt = 1`. This is one of the defining properties of an
approximation to the identity. -/
theorem integral_fejerKernel (N : ℕ) :
    ∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle = 1 := by
  unfold fejerKernel
  rw [integral_smul]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _
    (fun n _ => fourier_integrable n))]
  simp only [integral_dirichlet_sum, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  rw [show ((N + 1 : ℕ) : ℂ) = ((N : ℂ) + 1) from by push_cast; ring]
  exact inv_mul_cancel₀ (by
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact_mod_cast this.ne')

/-- Arithmetic identity `∑_{k=0}^{N} (2k + 1) = (N+1)²`, used to bound the size of
the iterated Dirichlet sum that defines the Fejér kernel. -/
private lemma sum_odd_eq_sq (N : ℕ) :
    ∑ k ∈ range (N + 1), ((2 : ℝ) * k + 1) = ((N : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

set_option linter.unusedSectionVars false in
/-- Pointwise bound `‖K_N(x)‖ ≤ N + 1`, obtained from the triangle inequality applied
to the iterated Dirichlet sum together with `∑_{k=0}^{N}(2k+1) = (N+1)²`. -/
theorem norm_fejerKernel_le (N : ℕ) (x : AddCircle T) :
    ‖fejerKernel N x‖ ≤ (N : ℝ) + 1 := by
  unfold fejerKernel
  rw [norm_smul]
  have hN_inv : ‖((N : ℂ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
    rw [norm_inv]; congr 1
    have h : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_natCast]; push_cast; ring
  rw [hN_inv]
  have hsum_bound : ‖∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
    ≤ ((N : ℝ) + 1) ^ 2 := by
    calc ‖∑ k ∈ range (N + 1),
        ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
      ≤ ∑ k ∈ range (N + 1),
        ‖∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range (N + 1), ((2 : ℝ) * k + 1) := by
          gcongr with k _
          calc ‖∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
            ≤ ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ‖fourier n x‖ := norm_sum_le _ _
            _ = ∑ _n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (1 : ℝ) := by
                congr 1; ext n; rw [fourier_apply, Circle.norm_coe]
            _ = (Finset.Icc (-(k : ℤ)) (k : ℤ)).card := by simp
            _ = 2 * k + 1 := by
                have h : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
                  rw [Int.card_Icc]; omega
                exact_mod_cast h
      _ = ((N : ℝ) + 1) ^ 2 := sum_odd_eq_sq N
  calc ((N : ℝ) + 1)⁻¹ * ‖∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
    ≤ ((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ 2 := by gcongr
    _ = (N : ℝ) + 1 := by field_simp

set_option linter.unusedSectionVars false in
/-- The Fejér kernel `K_N` is continuous on `AddCircle T`, being a finite
linear combination of continuous Fourier modes. -/
theorem fejerKernel_continuous (N : ℕ) : Continuous (fejerKernel (T := T) N) := by
  unfold fejerKernel
  apply Continuous.const_smul
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro n _
  exact (map_continuous (fourier n))

/-- The Fejér kernel `K_N` is integrable on the circle; this follows from
continuity together with the pointwise bound `‖K_N‖ ≤ N + 1`. -/
theorem fejerKernel_integrable (N : ℕ) :
    Integrable (fejerKernel (T := T) N) haarAddCircle := by
  apply Integrable.of_bound (C := (N : ℝ) + 1)
  · exact (fejerKernel_continuous N).aestronglyMeasurable
  · exact ae_of_all _ (fun x => norm_fejerKernel_le N x)

omit hT in
/-- Convolution identity for Fourier modes: `e^{-2πi n t / T} · e^{2πi n x / T} =
e^{2πi n (x - t) / T}`. The basic shift identity behind expressing partial Fourier
sums as convolutions with the Dirichlet kernel. -/
theorem fourier_neg_mul_fourier_eq (n : ℤ) (x t : AddCircle T) :
    (fourier (-n) t : ℂ) * (fourier n x : ℂ) = (fourier n (x - t) : ℂ) := by
  simp only [fourier_apply]
  rw [smul_sub, show n • x - n • t = n • x + (-n) • t from by rw [neg_smul]; abel]
  rw [toCircle_add]
  simp [Circle.coe_mul, mul_comm]

set_option linter.unusedSectionVars false in
/-- Re-indexing lemma: the sum `∑_{k=0}^{N} e^{2πi (k - (N+1)) x / T}` equals the
sum over the negative range `n ∈ [-(N+1), -1]`. Used to expand `(∑ z^k) · z̄^{N+1}`
in the proof of the Fejér kernel identity. -/
lemma sum_range_fourier_shift_neg (N : ℕ) (x : AddCircle T) :
    ∑ k ∈ range (N + 1), (fourier ((↑k : ℤ) + -↑(N + 1)) x : ℂ) =
    ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (-1 : ℤ), (fourier n x : ℂ) := by
  apply Finset.sum_nbij (fun k : ℕ => (↑k : ℤ) + (-↑(N + 1)))
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]
    constructor <;> push_cast <;> omega
  · intro k1 _ k2 _ h; exact_mod_cast show (↑k1 : ℤ) = ↑k2 from by linarith
  · intro n hn
    simp only [Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_image, Set.mem_Iio] at hn ⊢
    exact ⟨(n + ↑(N + 1)).toNat, by push_cast; omega,
      by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring⟩
  · intro k _; rfl

set_option linter.unusedSectionVars false in
/-- Companion to `sum_range_fourier_shift_neg`: the sum
`∑_{k=0}^{N} e^{2πi ((N+1) - k) x / T}` equals the sum over the positive range
`n ∈ [1, N+1]`. -/
lemma sum_range_fourier_shift_pos (N : ℕ) (x : AddCircle T) :
    ∑ k ∈ range (N + 1), (fourier ((↑(N + 1) : ℤ) + -↑k) x : ℂ) =
    ∑ n ∈ Finset.Icc (1 : ℤ) (↑(N + 1)), (fourier n x : ℂ) := by
  apply Finset.sum_nbij (fun k : ℕ => (↑(N + 1) : ℤ) + (-↑k))
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]
    constructor <;> push_cast <;> omega
  · intro k1 _ k2 _ h; exact_mod_cast show (↑k1 : ℤ) = ↑k2 from by linarith
  · intro n hn
    simp only [Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_image, Set.mem_Iio] at hn ⊢
    exact ⟨(↑(N + 1) - n).toNat, by push_cast; omega,
      by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring⟩
  · intro k _; rfl

/-- Key algebraic identity: the iterated Dirichlet sum defining `K_N` equals
`|∑_{k=0}^{N} e^{2πi k x / T}|²`, i.e. a sum-of-Dirichlet kernels is the squared
modulus of a geometric sum. This is what makes the Fejér kernel nonnegative. -/
theorem fejer_dirichlet_sum_eq_sq (N : ℕ) (x : AddCircle T) :
    (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (↑k), (fourier n x : ℂ)) =
    (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)) *
    starRingEnd ℂ (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)) := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, neg_zero, Finset.Icc_self]
    rw [fourier_zero, map_one, mul_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    set G := ∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ) with hG_def
    set z := (fourier (↑(N + 1) : ℤ) x : ℂ) with hz_def
    suffices h : ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (↑(N + 1)), (fourier n x : ℂ) =
        G * starRingEnd ℂ z + z * starRingEnd ℂ G + z * starRingEnd ℂ z by
      rw [h, map_add, mul_add, add_mul, add_mul]; ring
    have hGz : G * starRingEnd ℂ z =
        ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (-1), (fourier n x : ℂ) := by
      rw [hG_def, hz_def, Finset.sum_mul]
      simp_rw [fourier_neg.symm, ← fourier_add (T := T)]
      exact sum_range_fourier_shift_neg N x
    have hzG : z * starRingEnd ℂ G =
        ∑ n ∈ Finset.Icc (1 : ℤ) (↑(N + 1)), (fourier n x : ℂ) := by
      rw [hG_def, hz_def, map_sum, Finset.mul_sum]
      simp_rw [fourier_neg.symm, ← fourier_add (T := T)]
      exact sum_range_fourier_shift_pos N x
    have hzz : z * starRingEnd ℂ z = fourier (0 : ℤ) x := by
      rw [hz_def, fourier_neg.symm, ← fourier_add]; simp
    rw [hGz, hzG, hzz]
    have h_union : Finset.Icc (-(↑(N + 1) : ℤ)) (↑(N + 1)) =
        Finset.Icc (-(↑(N + 1) : ℤ)) (-1) ∪ {(0 : ℤ)} ∪ Finset.Icc (1 : ℤ) (↑(N + 1)) := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega
    have h_disj1 : Disjoint (Finset.Icc (-(↑(N + 1) : ℤ)) (-1) ∪ {(0 : ℤ)})
        (Finset.Icc (1 : ℤ) (↑(N + 1))) := by
      simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      intro n hn; omega
    have h_disj2 : Disjoint (Finset.Icc (-(↑(N + 1) : ℤ)) (-1)) {(0 : ℤ)} := by
      simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_singleton]
      intro n hn; omega
    rw [h_union, Finset.sum_union h_disj1, Finset.sum_union h_disj2, Finset.sum_singleton]
    ring

/-- Positivity of the Fejér kernel: `0 ≤ Re K_N(x)` for every `x`. Direct
consequence of the expression `K_N(x) = (N+1)⁻¹ · |∑_{k=0}^N e^{2πi k x / T}|²`. -/
theorem fejerKernel_nonneg (N : ℕ) (x : AddCircle T) :
    0 ≤ (fejerKernel N x).re := by
  unfold fejerKernel
  rw [fejer_dirichlet_sum_eq_sq, mul_conj]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  apply mul_nonneg
  · have h : (1 + (↑N : ℂ))⁻¹ = ↑((1 + (N : ℝ))⁻¹) := by
      rw [Complex.ofReal_inv]; congr 1; push_cast; ring
    rw [h, Complex.ofReal_re]
    positivity
  · exact normSq_nonneg _

/-- Bundled properties of the Fejér kernel `K_N` on `AddCircle T`:
(1) `K_N(x) ≥ 0` for all `x`,
(2) `K_N` is symmetric: `K_N(-x) = K_N(x)`,
(3) `K_N` is `T`-periodic on `ℝ`,
(4) `∫ K_N = 1`, and
(5) the decay estimate: for any `δ > 0` and any `x` with
`δ ≤ ‖1 - e^{2πi x / T}‖`, we have `‖K_N(x)‖ ≤ 4 / ((N+1) δ²)`. -/
theorem fejer_kernel_properties (N : ℕ) :
    (∀ x : AddCircle T, 0 ≤ (fejerKernel N x).re) ∧
    (∀ x : AddCircle T, fejerKernel N (-x) = fejerKernel N x) ∧
    (Function.Periodic (fun t : ℝ => fejerKernel (T := T) N (↑t)) T) ∧
    (∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle = 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ x : AddCircle T,
      δ ≤ ‖(1 : ℂ) - fourier (1 : ℤ) x‖ →
      ‖fejerKernel N x‖ ≤ 4 / (((N : ℝ) + 1) * δ ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fejerKernel_nonneg N
  · exact fejerKernel_symmetric N
  · intro t
    show fejerKernel (T := T) N ↑(t + T) = fejerKernel (T := T) N ↑t
    congr 1
    exact coe_add_period T t
  · exact integral_fejerKernel N
  · intro δ hδ x hx
    unfold fejerKernel
    rw [fejer_dirichlet_sum_eq_sq, mul_conj, norm_smul, norm_inv,
      show ‖(↑N + 1 : ℂ)‖ = ((N : ℝ) + 1) from by norm_cast,
      show ‖(↑(normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) : ℂ)‖ =
        ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ^ 2 from by
        simp only [Complex.norm_real, normSq_eq_norm_sq]
        exact Real.norm_of_nonneg (sq_nonneg _)]
    have hfne : (fourier (1 : ℤ) x : ℂ) ≠ 1 := by
      intro h; linarith [show ‖(1 : ℂ) - fourier (1 : ℤ) x‖ = 0 from by
        rw [h, sub_self, norm_zero]]
    have hfnorm : ‖fourier (1 : ℤ) x‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    have hfourier_pow : ∀ k : ℕ, (fourier (↑k : ℤ) x : ℂ) = (fourier (1 : ℤ) x) ^ k := by
      intro k; induction k with
      | zero => simp
      | succ n ih => rw [pow_succ, ← ih, ← fourier_add]; push_cast; ring_nf
    have hG_bound : ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ≤ 2 / δ := by
      conv_lhs => rw [show ∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ) =
        ∑ k ∈ range (N + 1), (fourier (1 : ℤ) x) ^ k from by
        congr 1; ext k; exact hfourier_pow k]
      rw [geom_sum_eq hfne (N + 1), norm_div,
        show ‖(fourier (1 : ℤ) x : ℂ) - 1‖ = ‖(1 : ℂ) - fourier (1 : ℤ) x‖ from
          norm_sub_rev _ _]
      calc ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1) - 1‖ / ‖(1 : ℂ) - fourier (1 : ℤ) x‖
          ≤ 2 / ‖(1 : ℂ) - fourier (1 : ℤ) x‖ := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            calc ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1) - 1‖
                ≤ ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by rw [norm_pow, hfnorm, one_pow, norm_one]; norm_num
        _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hδ hx
    calc ((N : ℝ) + 1)⁻¹ * ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ^ 2
        ≤ ((N : ℝ) + 1)⁻¹ * (2 / δ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_nn := norm_nonneg (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))
          exact sq_le_sq' (by linarith) hG_bound
      _ ≤ 4 / (((N : ℝ) + 1) * δ ^ 2) := le_of_eq (by field_simp; ring)

set_option linter.unusedSectionVars false in
/-- Reversed form of `fourier_neg_mul_fourier_eq`:
`e^{2πi n (x - t) / T} = e^{-2πi n t / T} · e^{2πi n x / T}`. Convenient orientation
for the convolution computation. -/
lemma fourier_sub_eq (n : ℤ) (x t : AddCircle T) :
    (fourier n (x - t) : ℂ) = (fourier (-n) t : ℂ) * (fourier n x : ℂ) :=
  (fourier_neg_mul_fourier_eq n x t).symm

/-- If `f` is integrable on `AddCircle T`, then `t ↦ e^{2πi n t / T} · f(x - t)` is
also integrable; a routine integrability lemma needed to interchange sums and
integrals in the convolution computation. -/
lemma fourier_smul_integrable (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (n : ℤ) (x : AddCircle T) :
    Integrable (fun t => (fourier n t : ℂ) • f (x - t)) haarAddCircle := by
  simp only [smul_eq_mul]
  exact (hf.comp_sub_left x).bdd_mul (map_continuous (fourier n)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [fourier_apply, Circle.norm_coe])

/-- Convolution-with-a-mode identity: for integrable `f`,
`∫ e^{2πi n t / T} · f(x - t) dt = ĉ_n(f) · e^{2πi n x / T}`. This says that the
`n`-th term of the partial Fourier sum at `x` is the convolution of `f` with the
mode `e^{2πi n · / T}`. -/
theorem fourier_integral_convolution (f : AddCircle T → ℂ)
    (hf : Integrable f haarAddCircle) (n : ℤ) (x : AddCircle T) :
    ∫ t : AddCircle T, (fourier n t : ℂ) • f (x - t) ∂haarAddCircle =
    fourierCoeff f n • (fourier n x : ℂ) := by

  have h1 : ∫ t : AddCircle T, (fourier n t : ℂ) • f (x - t) ∂haarAddCircle =
      ∫ t : AddCircle T, (fourier n (x - t) : ℂ) • f t ∂haarAddCircle := by
    have key : (fun t => (fourier n t : ℂ) • f (x - t)) =
        (fun t => (fourier n (x - t) : ℂ) • f t) ∘ (x - ·) := by
      ext t; simp only [Function.comp, sub_sub_cancel]
    rw [key]
    exact integral_sub_left_eq_self (fun s => (fourier n (x - s) : ℂ) • f s) haarAddCircle x
  rw [h1]

  simp_rw [fourier_sub_eq n x, smul_eq_mul, mul_assoc]

  simp_rw [show ∀ t, (fourier (-n) t : ℂ) * ((fourier n x : ℂ) * f t) =
    ((fourier (-n) t : ℂ) * f t) * (fourier n x : ℂ) from fun t => by ring]
  rw [show (fun t => ((fourier (-n) t : ℂ) * f t) * (fourier n x : ℂ)) =
    (fun t => ((fourier (-n) t : ℂ) * f t) • (fourier n x : ℂ)) from by
    ext t; simp [smul_eq_mul]]
  rw [integral_smul_const]

  rfl

/-- The Cesàro–Fourier mean as a convolution against the Fejér kernel:
`σ_N f(x) = ∫_{AddCircle T} K_N(t) · f(x - t) dt`,
valid for any integrable `f`. This is the bridge from the abstract definition of
`σ_N f` to the kernel-theoretic analysis underlying Fejér's theorem. -/
theorem cesaroMean_eq_fejer_convolution (f : AddCircle T → ℂ)
    (hf : Integrable f haarAddCircle) (N : ℕ) (x : AddCircle T) :
    cesaroFourierMean f N x =
    ∫ t : AddCircle T, fejerKernel N t • f (x - t) ∂haarAddCircle := by
  unfold cesaroFourierMean fejerKernel

  rw [show (fun t => (((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t)) =
    (fun t => ((N : ℂ) + 1)⁻¹ • ((∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t))) from by
    ext t; rw [smul_assoc]]
  rw [integral_smul]
  congr 1

  have h_rw : (fun t => (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ)) • f (x - t)) = (fun t => ∑ k ∈ range (N + 1),
      (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t)) := by
    ext t; exact Finset.sum_smul
  rw [h_rw]

  have h_int_outer : ∀ k, k ∈ range (N + 1) →
      Integrable (fun t => (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
        (fourier n t : ℂ)) • f (x - t)) haarAddCircle := by
    intro k _
    simp_rw [smul_eq_mul, Finset.sum_mul]
    apply integrable_finset_sum
    intro n _
    have := fourier_smul_integrable f hf n x
    simp only [smul_eq_mul] at this
    exact this

  rw [integral_finset_sum _ h_int_outer]
  congr 1; ext k

  have h_rw2 : (fun t => (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ)) • f (x - t)) = (fun t => ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ) • f (x - t)) := by
    ext t; exact Finset.sum_smul
  rw [h_rw2]

  rw [integral_finset_sum _ (fun n _ => fourier_smul_integrable f hf n x)]

  unfold partialFourierSum
  congr 1; ext n
  exact (fourier_integral_convolution f hf n x).symm

end FourierSeries

section FejerTheorem

variable {T : ℝ} [hT : Fact (0 < T)]
open MeasureTheory AddCircle Finset Filter Complex FourierSeries

/-- The Fejér kernel is in fact a nonnegative real number (coerced into `ℂ`):
`K_N(x) = (N+1)⁻¹ · |∑_{k=0}^{N} e^{2πi k x / T}|²`, written with `normSq`. This
makes `‖K_N(x)‖ = Re K_N(x)`. -/
theorem fejerKernel_eq_ofReal (N : ℕ) (x : AddCircle T) :
    fejerKernel N x = ↑(((N : ℝ) + 1)⁻¹ *
      normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) := by
  unfold fejerKernel
  simp only [smul_eq_mul]
  have h_inv : ((N : ℂ) + 1)⁻¹ = ↑(((N : ℝ) + 1)⁻¹) := by
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  have h_sum : (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n x : ℂ)) =
      ↑(normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) := by
    rw [fejer_dirichlet_sum_eq_sq, mul_conj]
  rw [h_inv, h_sum, ← Complex.ofReal_mul]

/-- Since `K_N ≥ 0`, its `L¹` norm coincides with its integral:
`∫ ‖K_N(t)‖ dt = 1`. Used to control the convolution `‖K_N * (f - f(x - ·))‖` in
the proof of Fejér's theorem. -/
theorem integral_norm_fejerKernel (N : ℕ) :
    ∫ t : AddCircle T, ‖fejerKernel N t‖ ∂haarAddCircle = 1 := by
  have h_eq : ∀ t : AddCircle T, ‖fejerKernel N t‖ = (fejerKernel N t).re := by
    intro t
    rw [fejerKernel_eq_ofReal]
    simp only [Complex.ofReal_re, Complex.norm_real]
    exact abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1))
      (normSq_nonneg _))
  simp_rw [h_eq]
  have h_re : (fun t : AddCircle T => (fejerKernel N t).re) =
      fun t => RCLike.re (fejerKernel N t) := rfl
  rw [h_re, integral_re (fejerKernel_integrable N)]
  have h1 := integral_fejerKernel (T := T) N
  exact_mod_cast congrArg Complex.re h1

/-- Quantitative form of Fejér's theorem: given `ε > 0` and a modulus of continuity
`δ > 0` for `f ∈ C(AddCircle T, ℂ)` at scale `ε/2`, there exists `N₀` such that
`∀ N ≥ N₀, ∀ x, dist (f x) (σ_N f x) < ε`. The proof splits the convolution integral
into the region `‖t‖ < δ` (where `f(x) − f(x − t)` is small) and its complement
(where the Fejér kernel decays as `O(1/((N+1)δ²))`). -/
theorem cesaroMean_uniform_bound (f : C(AddCircle T, ℂ))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ : ∀ ⦃a b : AddCircle T⦄, dist a b < δ → dist (f a) (f b) < ε / 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : AddCircle T,
      dist (f x) (cesaroFourierMean (⇑f) N x) < ε := by

  have hf_int : Integrable (⇑f) haarAddCircle :=
    (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


  have hcont_norm : Continuous (fun t : AddCircle T => ‖(1 : ℂ) - fourier (1 : ℤ) t‖) :=
    continuous_norm.comp (continuous_const.sub (map_continuous (fourier 1)))


  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ : ∃ δ' : ℝ, 0 < δ' ∧
      ∀ t : AddCircle T, δ ≤ dist t (0 : AddCircle T) →
        δ' ≤ ‖(1 : ℂ) - fourier (1 : ℤ) t‖ := by


    have hS_compact : IsCompact {t : AddCircle T | δ ≤ dist t (0 : AddCircle T)} :=
      (isClosed_le continuous_const (Continuous.dist continuous_id continuous_const)).isCompact
    by_cases hne : ({t : AddCircle T | δ ≤ dist t (0 : AddCircle T)} : Set _).Nonempty
    · obtain ⟨t_min, ht_min_mem, ht_min_le⟩ :=
        hS_compact.exists_isMinOn hne hcont_norm.continuousOn
      refine ⟨‖(1 : ℂ) - fourier (1 : ℤ) t_min‖, ?_, fun t ht => ht_min_le ht⟩
      rw [norm_pos_iff, sub_ne_zero]
      intro h_eq
      have h_dist : dist t_min (0 : AddCircle T) = 0 := by


        have hfourier_eq : (fourier (1 : ℤ) t_min : ℂ) = fourier (1 : ℤ) (0 : AddCircle T) := by
          simp [h_eq.symm, map_zero]

        have hinj := AddCircle.injective_toCircle (ne_of_gt hT.out)
        have h_val : fourier (1 : ℤ) t_min = fourier (1 : ℤ) (0 : AddCircle T) := by
          exact_mod_cast hfourier_eq
        simp only [fourier_apply, one_zsmul] at h_val
        rw [dist_eq_zero]
        exact hinj (Subtype.coe_injective h_val)
      linarith [show δ ≤ dist t_min (0 : AddCircle T) from ht_min_mem]
    ·
      exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩

  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (16 * ‖f‖ / (ε * δ' ^ 2))
  refine ⟨N₀, fun N hN x => ?_⟩

  rw [dist_eq_norm, cesaroMean_eq_fejer_convolution (⇑f) hf_int N x]

  have h_fx_eq : f x = ∫ t : AddCircle T, fejerKernel N t • f x ∂haarAddCircle := by
    have h1 : ∫ t : AddCircle T, fejerKernel N t • f x ∂haarAddCircle =
        (∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle) • f x := integral_smul_const _ (f x)
    rw [h1, integral_fejerKernel, one_smul]
  rw [h_fx_eq]

  have hfx_int : Integrable (fun t : AddCircle T => fejerKernel N t • f x) haarAddCircle :=
    (fejerKernel_integrable N).smul_const (f x)
  have hfxt_int : Integrable (fun t : AddCircle T => fejerKernel N t • f (x - t)) haarAddCircle :=
    (Continuous.smul (fejerKernel_continuous N)
      (f.continuous.comp (continuous_const.sub continuous_id'))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hfx_int hfxt_int]
  have h_integrand : (fun t => fejerKernel N t • f x - fejerKernel N t • f (x - t)) =
      (fun t => fejerKernel N t • (f x - f (x - t))) := by
    ext t; rw [← smul_sub]
  rw [h_integrand]

  have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hδ'_sq_pos : (0 : ℝ) < δ' ^ 2 := by positivity
  have hdecay := (fejer_kernel_properties (T := T) N).2.2.2.2
  set C := 4 / (((N : ℝ) + 1) * δ' ^ 2)
  have hC_nonneg : (0 : ℝ) ≤ C := by positivity

  have h2fC_lt : 2 * ‖f‖ * C < ε / 2 := by
    have hN_ge : (N₀ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    have hN1 : (N₀ : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have := hN₀
    show 2 * ‖f‖ * (4 / (((N : ℝ) + 1) * δ' ^ 2)) < ε / 2
    by_cases hf_zero : ‖f‖ = 0
    · simp [hf_zero]; linarith
    · have hf_pos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf_zero)
      have h_denom_pos : (0:ℝ) < ((N : ℝ) + 1) * δ' ^ 2 := by positivity
      calc 2 * ‖f‖ * (4 / (((N : ℝ) + 1) * δ' ^ 2))
          = 8 * ‖f‖ / (((N : ℝ) + 1) * δ' ^ 2) := by ring
        _ < ε / 2 := by
          rw [div_lt_iff₀ h_denom_pos]
          have h16 : 16 * ‖f‖ < (↑N + 1) * (ε * δ' ^ 2) := by
            have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hN₀ hN1)
              (show (0:ℝ) < ε * δ' ^ 2 from by positivity)
            rwa [div_mul_cancel₀] at this
            exact ne_of_gt (by positivity : (0:ℝ) < ε * δ' ^ 2)
          linarith


  have hpw : ∀ t : AddCircle T,
      ‖fejerKernel N t • (f x - f (x - t))‖ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C := by
    intro t
    rw [norm_smul]
    by_cases ht : dist t (0 : AddCircle T) < δ
    ·
      have hfx_close : ‖f x - f (x - t)‖ < ε / 2 := by
        have hd : dist x (x - t) < δ := by
          rw [dist_eq_norm, sub_sub_cancel]
          rwa [dist_eq_norm, sub_zero] at ht
        have := hδ hd

        rwa [dist_eq_norm] at this
      calc ‖fejerKernel N t‖ * ‖f x - f (x - t)‖
          ≤ ‖fejerKernel N t‖ * (ε / 2) := by
            apply mul_le_mul_of_nonneg_left (le_of_lt hfx_close) (norm_nonneg _)
        _ = ε / 2 * ‖fejerKernel N t‖ := by ring
        _ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C := le_add_of_nonneg_right (by positivity)
    ·
      push_neg at ht
      have h_decay_t : ‖fejerKernel N t‖ ≤ C :=
        hdecay δ' hδ'_pos t (hδ'_bound t ht)
      have hf_bound : ‖f x - f (x - t)‖ ≤ 2 * ‖f‖ :=
        calc ‖f x - f (x - t)‖ ≤ ‖f x‖ + ‖f (x - t)‖ := norm_sub_le _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (ContinuousMap.norm_coe_le_norm f x)
              (ContinuousMap.norm_coe_le_norm f (x - t))
          _ = 2 * ‖f‖ := by ring
      calc ‖fejerKernel N t‖ * ‖f x - f (x - t)‖
          ≤ C * (2 * ‖f‖) := mul_le_mul h_decay_t hf_bound (norm_nonneg _) hC_nonneg
        _ = 2 * ‖f‖ * C := by ring
        _ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C :=
            le_add_of_nonneg_left (by positivity)

  have hg_int : Integrable (fun t : AddCircle T =>
      ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C) haarAddCircle := by
    apply Integrable.add
    · exact (fejerKernel_integrable N).norm.const_mul _
    · exact integrable_const _
  calc ‖∫ t : AddCircle T, fejerKernel N t • (f x - f (x - t)) ∂haarAddCircle‖
      ≤ ∫ t : AddCircle T, ‖fejerKernel N t • (f x - f (x - t))‖ ∂haarAddCircle :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : AddCircle T, (ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C) ∂haarAddCircle := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun t => norm_nonneg _)) hg_int
        exact ae_of_all _ hpw
    _ = ε / 2 * (∫ t : AddCircle T, ‖fejerKernel N t‖ ∂haarAddCircle) + 2 * ‖f‖ * C := by
        rw [integral_add ((fejerKernel_integrable N).norm.const_mul _) (integrable_const _)]
        congr 1
        · rw [show (fun t => ε / 2 * ‖fejerKernel N t‖) =
              (fun t => (ε / 2) • ‖fejerKernel N t‖) from by ext; simp [smul_eq_mul]]
          rw [integral_smul]; simp [smul_eq_mul]
        · rw [integral_const]; simp
    _ = ε / 2 + 2 * ‖f‖ * C := by rw [integral_norm_fejerKernel]; ring
    _ < ε := by linarith

/-- Fejér's theorem on `AddCircle T`: for every continuous function
`f : AddCircle T → ℂ` (equivalently, every continuous `T`-periodic function on `ℝ`),
the Cesàro–Fourier means `σ_N f` converge uniformly to `f` as `N → ∞`. -/
theorem fejer_uniform_convergence (f : C(AddCircle T, ℂ)) :
    TendstoUniformly (fun N => cesaroFourierMean (⇑f) N) (⇑f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  rw [Filter.eventually_atTop]
  have hf_uc : UniformContinuous (⇑f) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.uniformContinuous_iff] at hf_uc
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_uc (ε / 2) (half_pos hε)
  exact cesaroMean_uniform_bound f ε hε δ hδ_pos hδ

end FejerTheorem
