/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Atlas.DifferentialAnalysis.code.TestFunctions
import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Existence form of the Schwartz Fourier isomorphism (Theorem 9.1 of
Melrose): the Fourier transform on the Schwartz space is a continuous
`ℂ`-linear equivalence whose inverse is the inverse Fourier transform. -/
theorem fourier_schwartz_isomorphism :
    ∃ e : 𝓢(V, E) ≃L[ℂ] 𝓢(V, E),
      (∀ f, e f = 𝓕 f) ∧ (∀ f, e.symm f = 𝓕⁻ f) := by
  exact ⟨FourierTransform.fourierCLE ℂ 𝓢(V, E),
    fun f => FourierTransform.fourierCLE_apply f,
    fun f => FourierTransform.fourierCLE_symm_apply f⟩

/-- The Fourier transform as a continuous `ℂ`-linear equivalence on the
Schwartz space `𝓢(V, E)`. -/
def fourierSchwartzCLE : 𝓢(V, E) ≃L[ℂ] 𝓢(V, E) :=
  FourierTransform.fourierCLE ℂ 𝓢(V, E)

/-- The continuous linear equivalence `fourierSchwartzCLE` acts as the
Fourier transform `𝓕` on Schwartz functions. -/
@[simp]
theorem fourierSchwartzCLE_apply (f : 𝓢(V, E)) : fourierSchwartzCLE f = 𝓕 f := rfl

/-- The inverse of `fourierSchwartzCLE` acts as the inverse Fourier
transform `𝓕⁻` on Schwartz functions. -/
@[simp]
theorem fourierSchwartzCLE_symm_apply (f : 𝓢(V, E)) : fourierSchwartzCLE.symm f = 𝓕⁻ f := rfl

end Isomorphism

/-- Parseval's identity (Lemma 9.2 of Melrose): for two Schwartz functions
`φ, ψ : V → ℂ`, the integral of `φ(x) · conj(ψ(x))` equals the integral of
`𝓕φ(ξ) · conj(𝓕ψ(ξ))`. -/
theorem parseval_identity (φ ψ : SchwartzMap V ℂ) :
    ∫ x, φ x * starRingEnd ℂ (ψ x) = ∫ ξ, 𝓕 φ ξ * starRingEnd ℂ (𝓕 ψ ξ) := by
  have key : ∀ (f g : SchwartzMap V ℂ) (x : V),
      f x * starRingEnd ℂ (g x) = @inner ℂ ℂ _ (g x) (f x) := fun f g x => by
    simp [inner]
  simp_rw [key]
  exact (SchwartzMap.integral_inner_fourier_fourier ψ φ).symm

section TemperedDistributionIsomorphism

open FourierTransform TemperedDistribution LineDeriv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Fourier transform on tempered distributions packaged as a `ℂ`-linear
equivalence `𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F)`. -/
def fourierTemperedDistributionEquiv : 𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F) :=
  fourierEquiv ℂ 𝓢'(E, F)

/-- Fourier inversion on tempered distributions: `𝓕⁻(𝓕 u) = u`. -/
@[simp]
theorem fourier_inverse_left (u : 𝓢'(E, F)) : 𝓕⁻ (𝓕 u) = u :=
  fourierInv_fourier_eq u

/-- Fourier inversion on tempered distributions: `𝓕(𝓕⁻ u) = u`. -/
theorem fourier_inverse_right (u : 𝓢'(E, F)) : 𝓕 (𝓕⁻ u) = u :=
  fourier_fourierInv_eq u

variable {n : ℕ}

/-- The `k`-fold iterated distributional derivative in the `j`-th coordinate
direction, applied to a tempered distribution `u`. -/
def iterDistribDerivCoord (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => ∂_{EuclideanSpace.single j (1 : ℝ)} v)^[k] u

/-- The mixed iterated distributional derivative `∂^α u` indexed by a
multi-index `α : Fin n → ℕ`, defined by composing the per-coordinate iterated
derivatives over all coordinates. -/
def iterDistribDeriv (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterDistribDerivCoord j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `2πi·ξ_j` on a
tempered distribution, which is the Fourier-side counterpart of the iterated
derivative in the `j`-th coordinate. -/
def iterCoordMulFourier (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => (2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun ξ => ↑(@inner ℝ _ _ ξ (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication operation `(2πi)^|α| ξ^α u` on a
tempered distribution, Fourier-dual to the multi-index derivative `∂^α`. -/
def iterMulFourier (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordMulFourier j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `-2πi·x_j` on a
tempered distribution, used to express the iterated coordinate derivative on
the Fourier side after inversion. -/
def iterCoordNegMulDistrib (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => -(2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun x => ↑(@inner ℝ _ _ x (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication `(-2πi)^|α| x^α u` on a tempered
distribution, packaged via a fold over coordinates. -/
def iterNegMulDistrib (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordNegMulDistrib j (α j) v) u

/-- The Fourier transform exchanges iterated coordinate derivatives with
iterated coordinate multiplication by `2πi·ξ_j`:
`𝓕 (∂_j^k u) = (2πi ξ_j)^k · 𝓕 u`. -/
theorem fourier_iterDerivCoord_eq (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕 (iterDistribDerivCoord j k u) = iterCoordMulFourier j k (𝓕 u) := by
  induction k generalizing u with
  | zero => simp [iterDistribDerivCoord, iterCoordMulFourier]
  | succ k ih =>
    simp only [iterDistribDerivCoord, iterCoordMulFourier, Function.iterate_succ', Function.comp]
    rw [TemperedDistribution.fourier_lineDerivOp_eq]
    congr 1; congr 1
    exact ih u

/-- Multi-index version of the Fourier-derivative exchange:
`𝓕 (∂^α u) = (2πi ξ)^α · 𝓕 u`. -/
theorem fourier_iterDeriv_eq (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕 (iterDistribDeriv α u) = iterMulFourier α (𝓕 u) := by
  unfold iterDistribDeriv iterMulFourier
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [fourier_iterDerivCoord_eq]
    congr 1

/-- Dual identity: the iterated coordinate derivative on `𝓕 u` equals the
Fourier transform of `(-2πi x_j)^k u`. -/
theorem iterDerivCoord_fourier_eq (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterDistribDerivCoord j k (𝓕 u) = 𝓕 (iterCoordNegMulDistrib j k u) := by
  induction k generalizing u with
  | zero => simp [iterDistribDerivCoord, iterCoordNegMulDistrib]
  | succ k ih =>
    simp only [iterDistribDerivCoord, iterCoordNegMulDistrib, Function.iterate_succ',
      Function.comp]
    show ∂_{EuclideanSpace.single j (1 : ℝ)} (iterDistribDerivCoord j k (𝓕 u)) =
      𝓕 (-(2 * ↑Real.pi * Complex.I) •
        smulLeftCLM ℂ (fun x => ↑(@inner ℝ _ _ x (EuclideanSpace.single j 1)))
        (iterCoordNegMulDistrib j k u))
    rw [ih]
    exact TemperedDistribution.lineDerivOp_fourier_eq _ _

end TemperedDistributionIsomorphism

end FourierInversion

open scoped SchwartzMap
open TestFunctions

namespace SobolevSpace

variable (n : ℕ)

/-- The Sobolev weight `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}`, written using the
Japanese bracket. This is the standard symbol whose `L²`-decay determines
the Sobolev exponent `s`. -/
def sobolevWeight (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (japaneseBracket n ξ) ^ s

/-- The Sobolev weight `⟨ξ⟩^s` is strictly positive for every `ξ` and every
real exponent `s`. -/
theorem sobolevWeight_pos (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    0 < sobolevWeight n s ξ :=
  Real.rpow_pos_of_pos (japaneseBracket_pos n ξ) s

/-- The Sobolev weight is nonzero, which is needed when inverting it inside
integrals. -/
theorem sobolevWeight_ne_zero (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    sobolevWeight n s ξ ≠ 0 :=
  ne_of_gt (sobolevWeight_pos n s ξ)

/-- Membership in the Sobolev space `H^s(ℝⁿ)`: a tempered distribution `u`
belongs to `H^s` if there exists `g ∈ L²` such that, for every Schwartz
function `φ`, `(𝓕 u)(φ) = ∫ ⟨ξ⟩^{-s} g(ξ) φ(ξ) dξ`. Equivalently, `𝓕 u`
is given by integration against the `L²` function `⟨ξ⟩^{-s} g`. -/
def MemHs (s : ℝ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
    MemLp g 2 ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ

/-- Monotonicity of Sobolev spaces: `H^s ⊆ H^t` whenever `t ≤ s`. The
witness `L²` function for `H^t` is obtained by multiplying the witness for
`H^s` by `⟨ξ⟩^{t-s} ≤ 1`. -/
theorem memHs_of_le {n : ℕ} {s t : ℝ} (hst : t ≤ s)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : MemHs n s u) :
    MemHs n t u := by
  obtain ⟨g, hg_mem, hg_eq⟩ := hu

  refine ⟨fun ξ => (sobolevWeight n (t - s) ξ : ℂ) * g ξ, ?_, ?_⟩
  ·

    have hweight_le_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
        sobolevWeight n (t - s) ξ ≤ 1 := by
      intro ξ
      simp only [sobolevWeight, japaneseBracket]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (Real.one_le_sqrt.mpr (by linarith [sq_nonneg (‖ξ‖ : ℝ)]))
        (by linarith)
    have hweight_nonneg : ∀ ξ : EuclideanSpace ℝ (Fin n),
        0 ≤ sobolevWeight n (t - s) ξ :=
      fun ξ => le_of_lt (sobolevWeight_pos n (t - s) ξ)

    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖(sobolevWeight n (t - s) ξ : ℂ) * g ξ‖ ≤ 1 * ‖g ξ‖ := by
      intro ξ
      rw [norm_mul, one_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_of_nonneg (hweight_nonneg ξ)]
      exact hweight_le_one ξ

    have hweight_cont : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (sobolevWeight n (t - s) ξ : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      show Continuous (fun ξ => japaneseBracket n ξ ^ (t - s))
      apply Continuous.rpow_const
      · exact continuous_sqrt.comp (by continuity)
      · intro ξ; exact Or.inl (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hweight_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)
  ·
    intro φ
    rw [hg_eq φ]
    congr 1
    ext ξ

    have hjb_pos : (0 : ℝ) < japaneseBracket n ξ := japaneseBracket_pos n ξ
    have hkey : (sobolevWeight n t ξ : ℂ)⁻¹ * (sobolevWeight n (t - s) ξ : ℂ) =
        (sobolevWeight n s ξ : ℂ)⁻¹ := by
      simp only [sobolevWeight]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
      congr 1
      have h1 : (japaneseBracket n ξ ^ t)⁻¹ = japaneseBracket n ξ ^ (-t) :=
        (Real.rpow_neg hjb_pos.le t).symm
      have h2 : (japaneseBracket n ξ ^ s)⁻¹ = japaneseBracket n ξ ^ (-s) :=
        (Real.rpow_neg hjb_pos.le s).symm
      rw [h1, h2, ← Real.rpow_add hjb_pos]
      congr 1
      linarith
    rw [← hkey]; ring

/-- The Sobolev space `H^s(ℝⁿ)` realised as the subtype of tempered
distributions satisfying `MemHs n s`. -/
def Hs (s : ℝ) : Type :=
  { u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) // MemHs n s u }

/-- The `L²` "witness" function attached to a Sobolev distribution: it is
the function `g` produced by the existential in `MemHs`. Concretely,
`𝓕 u = ⟨ξ⟩^{-s} · witnessFunc s u` as distributions. -/
def Hs.witnessFunc (s : ℝ) (u : Hs n s) : EuclideanSpace ℝ (Fin n) → ℂ :=
  u.2.choose

/-- The witness function attached to a Sobolev distribution is in `L²`. -/
lemma Hs.witnessFunc_memLp (s : ℝ) (u : Hs n s) :
    MemLp (Hs.witnessFunc n s u) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  u.2.choose_spec.1

/-- The witness function packaged as an honest element of the Hilbert space
`L²(ℝⁿ; ℂ)`. -/
def Hs.witnessL2 (s : ℝ) (u : Hs n s) :
    MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)

/-- The defining property of `Hs.witnessFunc`: pairing `𝓕 u` against a
Schwartz function recovers the integral of `⟨ξ⟩^{-s} · witnessFunc · φ`. -/
lemma Hs.witnessFunc_spec (s : ℝ) (u : Hs n s) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ :=
  u.2.choose_spec.2


/-- Given an `L²` function `f`, construct the element of `H^s` whose witness
function is `f`: namely, `𝓕⁻¹ (⟨ξ⟩^{-s} f)` as a tempered distribution. -/
def Hs.fromL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs n s := by

  set w : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹


  set v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
    TemperedDistribution.smulLeftCLM ℂ w (Lp.toTemperedDistribution f)

  set u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) := 𝓕⁻ v

  have hmem : MemHs n s u := by
    refine ⟨↑↑f, Lp.memLp f, fun φ => ?_⟩

    have hFu : 𝓕 u = v := FourierInversion.fourier_inverse_right v
    rw [hFu]


    simp only [v, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply]


    have hw_temp : w.HasTemperateGrowth := by
      show (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth

      have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
          (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
        ext ξ
        simp only [sobolevWeight]
        rw [← Complex.ofReal_inv]
        congr 1
        exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
      rw [heq]

      apply Function.Complex.hasTemperateGrowth_ofReal.comp
      show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
      show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
      have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
        Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
      suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
          (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
        rw [h]; exact this
      ext ξ
      simp only [japaneseBracket]
      rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
      congr 1
      ring

    congr 1
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp]
    simp only [smul_eq_mul, w]
    ring
  exact ⟨u, hmem⟩

/-- Right inverse: extracting the `L²` witness from `Hs.fromL2 s f` recovers
`f`. Uses Lebesgue uniqueness of integration against smooth, compactly
supported test functions to conclude the underlying functions are equal a.e. -/
theorem Hs.fromL2_witnessL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs.witnessL2 n s (Hs.fromL2 n s f) = f := by

  apply MeasureTheory.Lp.ext

  have h_wl2 : ↑↑(Hs.witnessL2 n s (Hs.fromL2 n s f)) =ᵐ[volume]
      Hs.witnessFunc n s (Hs.fromL2 n s f) :=
    MeasureTheory.MemLp.coeFn_toLp _

  refine h_wl2.trans ?_


  set u := Hs.fromL2 n s f
  set g₁ := Hs.witnessFunc n s u
  set g₂ : EuclideanSpace ℝ (Fin n) → ℂ := ↑↑f

  have hg₁_spec := Hs.witnessFunc_spec n s u

  have hg₂_spec : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ


    have hFu : 𝓕 u.1 = TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹)
        (MeasureTheory.Lp.toTemperedDistribution f) :=
      FourierInversion.fourier_inverse_right _
    rw [hFu]
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hw_temp : (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
      have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
          (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
        ext ξ
        simp only [sobolevWeight]
        rw [← Complex.ofReal_inv]
        congr 1
        exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
      rw [heq]
      apply Function.Complex.hasTemperateGrowth_ofReal.comp
      show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
      show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
      have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
        Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
      suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
          (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
        rw [h]; exact this
      ext ξ
      simp only [japaneseBracket]
      rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
      congr 1
      ring
    congr 1
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp]
    simp only [smul_eq_mul]
    ring

  have hint_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₁ ξ * φ ξ =
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ
    rw [← hg₁_spec φ, ← hg₂_spec φ]


  have hg₁_li : MeasureTheory.LocallyIntegrable g₁ volume :=
    (Hs.witnessFunc_memLp n s u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg₂_li : MeasureTheory.LocallyIntegrable g₂ volume :=
    (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_of_integral_contDiff_smul_eq hg₁_li hg₂_li
  intro g_test hg_smooth hg_supp


  have hw_htg : (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1; ring
  have hψ_smooth := hg_smooth.mul hw_htg.1
  have hψ_supp : HasCompactSupport (fun ξ => g_test ξ * sobolevWeight n s ξ) :=
    hg_supp.mul_right

  set φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hψ_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ_smooth)

  have key := hint_eq φ


  have heq_lhs : (fun x => g_test x • g₁ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  have heq_rhs : (fun x => g_test x • g₂ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  calc ∫ x, g_test x • g₁ x
      = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x := congr_arg _ heq_lhs
    _ = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x := key
    _ = ∫ x, g_test x • g₂ x := congr_arg _ heq_rhs.symm

/-- Left inverse: starting from a Sobolev distribution `u`, taking the
`L²` witness and then applying `Hs.fromL2` returns `u`. Uses Fourier
inversion on tempered distributions. -/
theorem Hs.witnessL2_fromL2 (s : ℝ) (u : Hs n s) :
    Hs.fromL2 n s (Hs.witnessL2 n s u) = u := by
  apply Subtype.ext

  simp only [Hs.fromL2, Hs.witnessL2]


  suffices h : (TemperedDistribution.smulLeftCLM ℂ
      (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u))) =
      𝓕 u.val by
    rw [h]
    exact FourierInversion.fourier_inverse_left u.val

  apply ContinuousLinearMap.ext
  intro φ


  have hw_temp : (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
    have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
        (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
      ext ξ
      simp only [sobolevWeight]
      rw [← Complex.ofReal_inv]
      congr 1
      exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
    rw [heq]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
    show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
    suffices hh : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
      rw [hh]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring


  trans (∫ ξ : EuclideanSpace ℝ (Fin n),
    (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ)
  ·
    show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      ∫ ξ : EuclideanSpace ℝ (Fin n),
        (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ
    rw [show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))
        (SchwartzMap.smulLeftCLM ℂ (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹) φ) from
      TemperedDistribution.smulLeftCLM_apply_apply _ _ _]
    rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    refine MeasureTheory.integral_congr_ae ?_
    have hae := MeasureTheory.MemLp.coeFn_toLp
      (f := Hs.witnessFunc n s u) (hf := Hs.witnessFunc_memLp n s u)
    filter_upwards [hae] with ξ hξ
    simp only [smul_eq_mul]
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp, smul_eq_mul, hξ]
    ring
  ·
    exact (Hs.witnessFunc_spec n s u φ).symm

/-- The set-level bijection `Hs n s ≃ L²(ℝⁿ; ℂ)` provided by the witness
function construction. -/
noncomputable def Hs.equivLp (s : ℝ) :
    Hs n s ≃ MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := Hs.witnessL2 n s
  invFun := Hs.fromL2 n s
  left_inv := Hs.witnessL2_fromL2 n s
  right_inv := Hs.fromL2_witnessL2 n s


/-- Transport the `NormedAddCommGroup` structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. -/
@[reducible]
noncomputable def Hs.instNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (Hs n s) :=
  (Hs.equivLp n s).normedAddCommGroup
attribute [instance] Hs.instNormedAddCommGroup


/-- Transport the complex inner-product-space structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. The inner product on `H^s` is
`⟨u, v⟩_{H^s} := ⟨witnessL2 u, witnessL2 v⟩_{L²}`. -/
@[reducible]
noncomputable def Hs.instInnerProductSpace (s : ℝ) : InnerProductSpace ℂ (Hs n s) := by
  letI := Hs.instNormedAddCommGroup n s
  letI : NormedSpace ℂ (Hs n s) := Equiv.normedSpace ℂ (Hs.equivLp n s)
  letI : Inner ℂ (Hs n s) :=
    ⟨fun x y => (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y) : ℂ)⟩
  exact {
    norm_sq_eq_re_inner := fun x => by
      show ‖x‖ ^ 2 = RCLike.re (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s x))
      have h : ‖x‖ = ‖Hs.equivLp n s x‖ := rfl
      rw [h]
      exact InnerProductSpace.norm_sq_eq_re_inner (Hs.equivLp n s x)
    conj_inner_symm := fun x y => by
      show starRingEnd ℂ (inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s x)) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      exact InnerProductSpace.conj_inner_symm (Hs.equivLp n s x) (Hs.equivLp n s y)
    add_left := fun x y z => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (x + y)) (Hs.equivLp n s z) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s z) +
           inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s z)
      have hadd : (Hs.equivLp n s) (x + y) = (Hs.equivLp n s) x + (Hs.equivLp n s) y := by
        simp [show (x + y : Hs n s) = (Hs.equivLp n s).symm
          ((Hs.equivLp n s) x + (Hs.equivLp n s) y) from rfl]
      rw [hadd]
      exact inner_add_left _ _ _
    smul_left := fun x y r => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (r • x)) (Hs.equivLp n s y) =
           starRingEnd ℂ r * inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      have hsmul : (Hs.equivLp n s) (r • x) = r • (Hs.equivLp n s) x := by
        simp [show (r • x : Hs n s) = (Hs.equivLp n s).symm
          (r • (Hs.equivLp n s) x) from rfl]
      rw [hsmul]
      exact inner_smul_left _ _ _
  }
attribute [instance] Hs.instInnerProductSpace


/-- The Sobolev space `H^s` is complete: it inherits completeness from
`L²(ℝⁿ; ℂ)` via the isometric bijection `Hs.equivLp`. -/
theorem Hs.instCompleteSpace (s : ℝ) : CompleteSpace (Hs n s) :=
  (completeSpace_congr (Isometry.of_dist_eq (fun _ _ => rfl)).isUniformEmbedding
    (e := Hs.equivLp n s)).mpr inferInstance
attribute [instance] Hs.instCompleteSpace


/-- The norm on `H^s` is defined to equal the `L²` norm of the witness:
`‖u‖_{H^s} = ‖witnessL2 u‖_{L²}`. -/
theorem Hs.norm_witnessL2 (s : ℝ) (u : Hs n s) :
    ‖u‖ = ‖Hs.witnessL2 n s u‖ := rfl


/-- The witness map `Hs n s → L²` is additive. -/
theorem Hs.witnessL2_add (s : ℝ) (u v : Hs n s) :
    Hs.witnessL2 n s (u + v) = Hs.witnessL2 n s u + Hs.witnessL2 n s v := by
  show (Hs.equivLp n s) (u + v) = (Hs.equivLp n s) u + (Hs.equivLp n s) v
  simp [show (u + v : Hs n s) = (Hs.equivLp n s).symm
    ((Hs.equivLp n s) u + (Hs.equivLp n s) v) from rfl]


/-- The witness map `Hs n s → L²` is `ℂ`-linear. -/
theorem Hs.witnessL2_smul (s : ℝ) (c : ℂ) (u : Hs n s) :
    Hs.witnessL2 n s (c • u) = c • Hs.witnessL2 n s u := by
  show (Hs.equivLp n s) (c • u) = c • (Hs.equivLp n s) u
  simp [show (c • u : Hs n s) = (Hs.equivLp n s).symm
    (c • (Hs.equivLp n s) u) from rfl]

/-- The "Fourier-weight" linear isometric equivalence between `H^s(ℝⁿ)` and
`L²(ℝⁿ; ℂ)` sending each `u` to its `L²` witness `⟨ξ⟩^s · 𝓕u`. This is the
fundamental Hilbert-space identification underlying the definition of
`H^s`. -/
noncomputable def fourierWeightEquiv (s : ℝ) :
    Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap :=
        { toFun := Hs.witnessL2 n s
          map_add' := Hs.witnessL2_add n s
          map_smul' := Hs.witnessL2_smul n s }
       norm_map' := fun u => (Hs.norm_witnessL2 n s u).symm } : Hs n s →ₗᵢ[ℂ]
         MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (fun f => ⟨Hs.fromL2 n s f, Hs.fromL2_witnessL2 n s f⟩)

/-- Schwartz functions are dense in `H^s`: for any linear isometric
identification `Φ : H^s ≃ₗᵢ L²`, the composition `Φ⁻¹ ∘ toLp` of the
canonical Schwartz-to-`L²` map has dense range. -/
theorem schwartz_dense_in_Hs
    (s : ℝ) [NormedAddCommGroup (Hs n s)] [NormedSpace ℝ (Hs n s)]
    [NormedSpace ℂ (Hs n s)]
    (Φ : Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    DenseRange (Φ.symm ∘
      (SchwartzMap.toLpCLM ℝ ℂ 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
  DenseRange.comp
    ((EquivLike.surjective Φ.symm).denseRange)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (LinearIsometryEquiv.continuous Φ.symm)

/-- The Sobolev duality identification: `H^{-s} ≃ (H^s)'` as anti-linear
isometric equivalences, obtained by composing the two Fourier-weight
isometries with the Riesz representation `H^s ≃ (H^s)'`. This is part of
Proposition 9.8 of Melrose. -/
noncomputable def dualIdentification (s : ℝ) :
    Hs n (-s) ≃ₗᵢ⋆[ℂ] (Hs n s →L[ℂ] ℂ) :=
  ((fourierWeightEquiv n (-s)).trans (fourierWeightEquiv n s).symm).trans
    (InnerProductSpace.toDual ℂ (Hs n s))

/-- The duality identification is norm-preserving:
`‖dualIdentification s u'‖ = ‖u'‖`. -/
theorem dualIdentification_norm_map (s : ℝ) (u' : Hs n (-s)) :
    ‖dualIdentification n s u'‖ = ‖u'‖ :=
  (dualIdentification n s).norm_map u'

/-- The duality identification is a bijection between `H^{-s}` and the
continuous dual `(H^s)'`. -/
theorem dualIdentification_bijective (s : ℝ) :
    Function.Bijective (dualIdentification n s) :=
  (dualIdentification n s).bijective

/-- Proposition 9.8 of Melrose: for each `s ∈ ℝ`, the Sobolev space `H^s`
is a Hilbert space (linearly isometric to `L²` with Schwartz functions
dense), and there is an anti-linear isometric identification of `H^{-s}` with
the continuous dual of `H^s`. -/
theorem proposition_9_8 (s : ℝ) :

    (∃ Φ : Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),

      DenseRange (Φ.symm ∘
        (SchwartzMap.toLpCLM ℝ ℂ 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧

    Nonempty (Hs n (-s) ≃ₗᵢ⋆[ℂ] (Hs n s →L[ℂ] ℂ)) := by
  constructor
  · exact ⟨fourierWeightEquiv n s,
      schwartz_dense_in_Hs n s (fourierWeightEquiv n s)⟩
  · exact ⟨dualIdentification n s⟩

/-- The complex-valued Sobolev weight `ξ ↦ ⟨ξ⟩^s` has temperate growth, so
multiplication by it acts on Schwartz functions. -/
lemma sobolevWeight_complex_hasTemperateGrowth (s : ℝ) :
    (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)).HasTemperateGrowth := by


  have hreal : (fun ξ : EuclideanSpace ℝ (Fin n) =>
      sobolevWeight n s ξ).HasTemperateGrowth := by


    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth


    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring
  exact Function.Complex.hasTemperateGrowth_ofReal.comp hreal

/-- Every Schwartz function belongs to `H^s` for every real `s`: the
witness function is `⟨ξ⟩^s · 𝓕f`, which is again Schwartz and in particular
in `L²`. -/
theorem schwartz_memHs (s : ℝ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemHs n s (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by


  set weight : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (sobolevWeight n s ξ : ℂ)
  have htemp : weight.HasTemperateGrowth := sobolevWeight_complex_hasTemperateGrowth n s

  set h : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := SchwartzMap.smulLeftCLM ℂ weight (𝓕 f)

  refine ⟨fun ξ => h ξ, h.memLp 2, fun φ => ?_⟩

  have key : ∀ ξ : EuclideanSpace ℝ (Fin n),
      (sobolevWeight n s ξ : ℂ)⁻¹ * h ξ * φ ξ = (𝓕 f) ξ * φ ξ := fun ξ => by
    have hval : h ξ = (sobolevWeight n s ξ : ℂ) * (𝓕 f) ξ := by
      have := SchwartzMap.smulLeftCLM_apply_apply htemp (𝓕 f) ξ
      simp only [smul_eq_mul] at this
      exact this
    rw [hval]
    have hne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sobolevWeight_ne_zero n s ξ)
    field_simp
  simp_rw [key]


  rw [TemperedDistribution.fourier_apply, SchwartzMap.coe_apply]


  rw [SchwartzMap.integral_fourier_mul_eq f φ]

  congr 1
  ext x
  simp [smul_eq_mul, mul_comm]







/-- The Japanese bracket `⟨ξ⟩ = √(1 + ‖ξ‖²)` is at least `1`. -/
theorem one_le_japaneseBracket (ξ : EuclideanSpace ℝ (Fin n)) :
    1 ≤ japaneseBracket n ξ := by
  unfold japaneseBracket
  rw [Real.le_sqrt (by linarith) (by positivity)]
  nlinarith [sq_nonneg ‖ξ‖]


/-- Each coordinate `|ξ i|` is bounded by the Japanese bracket `⟨ξ⟩`. -/
theorem abs_coord_le_japaneseBracket (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |ξ i| ≤ japaneseBracket n ξ := by
  unfold japaneseBracket
  have h1 : |ξ i| ≤ ‖ξ‖ := by
    have h_sq : |ξ i| ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc |ξ i| ^ 2 = ‖(ξ.ofLp i : ℝ)‖ ^ 2 := by rw [Real.norm_eq_abs]
        _ ≤ ∑ j, ‖ξ.ofLp j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖ξ.ofLp j‖ ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg _)).2
  calc |ξ i| ≤ ‖ξ‖ := h1
    _ ≤ sqrt (1 + ‖ξ‖ ^ 2) := by
        rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
        nlinarith [sq_nonneg ‖ξ‖]

/-- Pointwise norm bound: for any multi-index `α` of order at most `m`, the
product of the monomial `ξ^α` and the negative-Sobolev weight
`⟨ξ⟩^{-m}` has complex norm at most `1`. This is the key bound that makes
the construction of `L²` witnesses for `H^{-m}` work. -/
theorem monomial_sobolevWeight_norm_le_one
    {n : ℕ} (m : ℕ) (α : Fin n → ℕ)
    (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖SchwartzRepresentation.monomial α ξ * (sobolevWeight n (-(m : ℝ)) ξ : ℂ)‖ ≤ 1 := by
  have hα_ord : SchwartzRepresentation.multiIndexOrder α ≤ m :=
    SchwartzRepresentation.mem_multiIndicesBall_iff.mp hα
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hjb_pos : 0 < japaneseBracket n ξ := japaneseBracket_pos n ξ
  have hjb_ge : 1 ≤ japaneseBracket n ξ := one_le_japaneseBracket n ξ
  have hsw_pos : 0 < sobolevWeight n (-(m : ℝ)) ξ := sobolevWeight_pos n _ ξ
  rw [abs_of_pos hsw_pos]

  unfold SchwartzRepresentation.monomial
  rw [norm_prod]
  simp_rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]

  have h_prod : ∏ i : Fin n, |ξ i| ^ (α i) ≤ (japaneseBracket n ξ) ^ (∑ i, α i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod
    · intro i _; exact pow_nonneg (abs_nonneg _) _
    · intro i _; exact pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le_japaneseBracket n ξ i) _

  unfold sobolevWeight
  calc (∏ i : Fin n, |ξ i| ^ α i) * japaneseBracket n ξ ^ (-(m : ℝ))
      ≤ japaneseBracket n ξ ^ (∑ i, α i) * japaneseBracket n ξ ^ (-(m : ℝ)) := by
        apply mul_le_mul_of_nonneg_right h_prod (le_of_lt (Real.rpow_pos_of_pos hjb_pos _))
    _ = japaneseBracket n ξ ^ ((↑(∑ i : Fin n, α i) : ℝ) + (-(m : ℝ))) := by
        rw [← Real.rpow_natCast (japaneseBracket n ξ) (∑ i, α i),
            ← Real.rpow_add hjb_pos]
    _ ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hjb_ge
        have : (SchwartzRepresentation.multiIndexOrder α : ℝ) ≤ (m : ℝ) :=
          Nat.cast_le.mpr hα_ord
        simp only [SchwartzRepresentation.multiIndexOrder] at this
        linarith




/-- Restatement of `monomial_sobolevWeight_norm_le_one` using the explicit
product `∏ ξ_i^{α_i}` instead of `monomial α`. -/
theorem monomial_sobolev_weight_bound
    (m : ℕ) (α : Fin n → ℕ)
    (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖(∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) *
      (sobolevWeight n (-(m : ℝ)) ξ : ℂ)‖ ≤ 1 :=
  monomial_sobolevWeight_norm_le_one m α hα ξ


/-- If `h` is bounded by `1` almost everywhere and `g ∈ L²`, then the
pointwise product `h · g` lies in `L²`. This is the order in which the
measurability argument is most convenient. -/
theorem memLp_mul_of_bound_one_backward
    (h g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hh_meas : AEStronglyMeasurable h (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hh : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖h x‖ ≤ 1)
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => h x * g x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply MemLp.of_le_mul hg (hh_meas.mul hg.aestronglyMeasurable)
  filter_upwards [hh] with x hx
  calc ‖h x * g x‖ = ‖h x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ 1 * ‖g x‖ := by gcongr


/-- A finite product of functions with temperate growth has temperate
growth. The proof is a Finset induction using closure of temperate growth
under multiplication. -/
lemma hasTemperateGrowth_prod' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → E → R)
    (hf : ∀ i ∈ s, Function.HasTemperateGrowth (f i)) :
    Function.HasTemperateGrowth (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const 1
  | @insert a s' has' ih =>
    have hconv : (fun x => ∏ i ∈ Insert.insert a s', f i x) =
        (fun x => f a x * ∏ i ∈ s', f i x) := by
      ext x; exact Finset.prod_insert has'

    rw [hconv]
    exact (hf a (Finset.mem_insert_self a s')).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))


/-- The monomial `ξ ↦ ∏_i (ξ_i)^{α_i}` (as a complex-valued function) has
temperate growth. -/
lemma monomial_hasTemperateGrowth (α : Fin n → ℕ) :
    Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin n) => ∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) :=
  hasTemperateGrowth_prod' _ _ (fun i _ =>
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth).pow (α i))

/-- The integrand `ξ^α · f · φ` is integrable when `f ∈ L²` and `φ` is a
Schwartz function (so `ξ^α · φ` is still Schwartz, hence in `L²`). -/
theorem memLp_monomial_mul
    (m : ℕ) (α : Fin n → ℕ)
    (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m)
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MeasureTheory.Integrable
      (fun ξ => (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) * f ξ * φ ξ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by

  let monφ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    SchwartzMap.bilinLeftCLM (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ).flip
      (monomial_hasTemperateGrowth n α) φ

  suffices h : MeasureTheory.Integrable (fun ξ => f ξ * monφ ξ) MeasureTheory.volume from
    h.congr (by filter_upwards with ξ; simp only [monφ,
      SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply']; ring)

  exact hf.integrable_mul (monφ.memLp 2)




/-- Polar-form identity: for any complex number `z`, the product
`z · (conj(z) / ‖z‖)` equals `‖z‖` (with the convention that the formula
holds even for `z = 0`). -/
lemma mul_conj_div_norm_eq_norm (z : ℂ) :
    z * (starRingEnd ℂ z / (↑‖z‖ : ℂ)) = ↑‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [div_eq_mul_inv, ← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, sq, mul_assoc, mul_inv_cancel₀ hn, mul_one]


/-- Convenience reordering of `memLp_mul_of_bound_one_backward`: if `h` is
a.e. bounded by `1` (and strongly measurable) and `g ∈ L²`, then `h · g`
is in `L²`. -/
theorem memLp_mul_of_bound_one
    (h g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hh : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖h x‖ ≤ 1)
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hh_meas : AEStronglyMeasurable h (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => h x * g x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply MemLp.of_le_mul hg (hh_meas.mul hg.aestronglyMeasurable)
  filter_upwards [hh] with x hx
  calc ‖h x * g x‖ = ‖h x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ 1 * ‖g x‖ := by gcongr








/-- Pointwise algebraic identity for the explicit `v_α` used in the
Sobolev decomposition: if `v_α(ξ) = sign(ξ^α) · (∑_β ‖ξ^β‖)⁻¹ · ⟨ξ⟩^m · g(ξ)`
for every `α` of order at most `m`, then `∑_α ξ^α · v_α(ξ) = ⟨ξ⟩^m · g(ξ)`. -/
theorem sgn_denom_algebraic_identity
    (m : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (v : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_def : ∀ α ξ,
      v α ξ = (starRingEnd ℂ (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) /
        (↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ : ℂ)) *
        (↑(∑ β ∈ SchwartzRepresentation.multiIndicesBall n m,
            ‖∏ i : Fin n, ((ξ i : ℂ) ^ (β i))‖) : ℂ)⁻¹ *
        (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹ * g ξ) :
    ∀ ξ : EuclideanSpace ℝ (Fin n),
      ∑ α ∈ SchwartzRepresentation.multiIndicesBall n m,
        (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) * v α ξ =
        (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹ * g ξ := by
  intro ξ
  simp_rw [hv_def]


  set W := (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹
  set S := (↑(∑ β ∈ SchwartzRepresentation.multiIndicesBall n m,
      ‖∏ i : Fin n, ((ξ i : ℂ) ^ (β i))‖) : ℂ) with hS_def
  have hS_ne : S ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr; apply ne_of_gt
    calc (0 : ℝ) < 1 := one_pos
      _ = ‖∏ i : Fin n, ((ξ i : ℂ) ^ ((0 : Fin n → ℕ) i))‖ := by simp
      _ ≤ ∑ β ∈ SchwartzRepresentation.multiIndicesBall n m,
            ‖∏ i, ((ξ i : ℂ) ^ (β i))‖ :=
          Finset.single_le_sum (f := fun β => ‖∏ i, ((ξ i : ℂ) ^ (β i))‖)
            (fun _ _ => norm_nonneg _)
            (SchwartzRepresentation.zero_mem_multiIndicesBall n m)

  have step : ∀ α ∈ SchwartzRepresentation.multiIndicesBall n m,
      (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) *
        ((starRingEnd ℂ (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) /
          (↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ : ℂ)) * S⁻¹ * W * (g ξ)) =
        ↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ * S⁻¹ * W * (g ξ) := by
    intro α _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
      mul_conj_div_norm_eq_norm (∏ i : Fin n, ((ξ i : ℂ) ^ (α i)))]
  rw [Finset.sum_congr rfl step]

  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Complex.ofReal_sum, hS_def, mul_inv_cancel₀ hS_ne, one_mul]



end SobolevSpace

end
