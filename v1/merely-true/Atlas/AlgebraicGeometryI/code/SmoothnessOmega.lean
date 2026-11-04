/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section

open KaehlerDifferential Algebra

universe u v

section EmbeddingDimension

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **Embedding dimension** of a Noetherian local ring `R`: the minimal number
of generators of the maximal ideal, equivalently `dim_κ(𝔪/𝔪²)`. -/
abbrev embDim : ℕ := Submodule.spanFinrank (IsLocalRing.maximalIdeal R)

/-- **Regular local ring**: Krull dimension equals embedding dimension. -/
def IsRegularLocal : Prop :=
  ringKrullDim R = ↑(embDim R)

/-- General inequality: Krull dimension is at most embedding dimension. -/
theorem krullDim_le_embDim : ringKrullDim R ≤ ↑(embDim R) := by
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (IsLocalRing.maximalIdeal R) (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ le_refl _)
  have h2 : ringKrullDim (R ⧸ (IsLocalRing.maximalIdeal R : Ideal R)) = 0 :=
    ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (IsLocalRing.maximalIdeal.isMaximal R))
  rw [h2, zero_add] at h1
  exact h1


omit [IsNoetherianRing R] in
/-- A field is a regular local ring of dimension zero. -/
theorem isRegularLocal_of_field (hR : IsField R) : IsRegularLocal R := by
  unfold IsRegularLocal embDim
  simp [ringKrullDim_eq_zero_of_isField hR, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR,
      Submodule.spanFinrank_bot]

end EmbeddingDimension

section FormalSmoothnessKahler

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- For a formally smooth `R`-algebra `A`, `Ω_{A/R}` is projective. -/
theorem formallySmooth_implies_kahler_projective [FormallySmooth R A] :
    Module.Projective A Ω[A⁄R] :=
  FormallySmooth.projective_kaehlerDifferential

/-- `A` is formally smooth over `R` iff `Ω_{A/R}` is projective and the first
André–Quillen cotangent homology `H₁(L_{A/R})` vanishes. -/
theorem formallySmooth_iff_projective_and_H1_vanishes :
    FormallySmooth R A ↔
      Module.Projective A Ω[A⁄R] ∧ Subsingleton (H1Cotangent R A) :=
  formallySmooth_iff R A

end FormalSmoothnessKahler

section SmoothLocusSection

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- **Smooth locus is open**: for a finitely presented `R`-algebra `A`, the
smooth locus inside `Spec A` is open. -/
theorem smoothLocus_isOpen [FinitePresentation R A] :
    IsOpen (Algebra.smoothLocus R A) :=
  Algebra.isOpen_smoothLocus

/-- The smooth locus equals the locus where `H₁` cotangent vanishes intersected
with the free locus of `Ω_{A/R}`. -/
theorem smoothLocus_eq_kahler_free_locus [EssFiniteType R A] :
    Algebra.smoothLocus R A =
      (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] :=
  Algebra.smoothLocus_eq_compl_support_inter

/-- For a smooth algebra, the smooth locus is the whole spectrum. -/
theorem smoothLocus_eq_univ_of_smooth [Smooth R A] :
    Algebra.smoothLocus R A = Set.univ :=
  Algebra.smoothLocus_eq_univ

/-- Smoothness is equivalent to the smooth locus being the whole spectrum
(for finitely presented algebras). -/
theorem smooth_iff_smoothLocus_univ [FinitePresentation R A] :
    Algebra.smoothLocus R A = Set.univ ↔ FormallySmooth R A :=
  Algebra.smoothLocus_eq_univ_iff

/-- **Local-to-global smoothness**: if `A` is smooth over `R` at the prime `p`,
then some basic open `D(f)` with `f ∉ p` is smooth over `R`. -/
theorem exists_localization_smooth_of_smooth_at
    [FinitePresentation R A] (p : Ideal A) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ f ∉ p, Smooth R (Localization.Away f) :=
  IsSmoothAt.exists_notMem_smooth R p

end SmoothLocusSection

section SmoothLocusAlgebraicDense

variable {K : Type u} [Field K] [PerfectField K]
  {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- Localizing an integral domain at the zero ideal yields a field
(the fraction field). -/
lemma isField_localization_atPrime_bot :
    IsField (Localization.AtPrime (⊥ : Ideal A)) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  symm; rw [← Localization.AtPrime.eq_maximalIdeal_iff_comap_eq]; simp

/-- **Smoothness at the generic point** over a perfect field: a finite-type
algebra over a perfect field `K` is smooth at the generic point of an integral
variety. -/
lemma isSmoothAt_genericPoint : Algebra.IsSmoothAt K (⊥ : Ideal A) := by
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) :=
    isField_localization_atPrime_bot.toField
  haveI : Algebra.EssFiniteType K (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.instEssFiniteTypeLocalization K A _
  exact Algebra.FormallySmooth.of_perfectField

/-- **Smooth locus is dense** over a perfect field: for an integral domain of
finite type over a perfect field, the smooth locus is dense in `Spec A`. This is
generic smoothness. -/
theorem smoothLocus_isDense [Algebra.FinitePresentation K A] :
    Dense (Algebra.smoothLocus K A) := by
  haveI := PrimeSpectrum.irreducibleSpace (R := A)
  apply IsOpen.dense Algebra.isOpen_smoothLocus
  exact ⟨⟨⊥, Ideal.isPrime_bot⟩, isSmoothAt_genericPoint⟩

/-- Combination: the smooth locus over a perfect field is both open and dense. -/
theorem smoothLocus_isOpen_and_dense [Algebra.FinitePresentation K A] :
    IsOpen (Algebra.smoothLocus K A) ∧ Dense (Algebra.smoothLocus K A) :=
  ⟨Algebra.isOpen_smoothLocus, smoothLocus_isDense⟩

end SmoothLocusAlgebraicDense

section SmoothLocusDense

open AlgebraicGeometry

variable {X : Scheme.{u}} {K : Type u} [Field K] [PerfectField K]

/-- Scheme-theoretic generic smoothness: the smooth locus of a finite-presentation
morphism to `Spec K` from a reduced scheme is dense (when `K` is perfect). -/
theorem smoothLocus_isDense_scheme [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    Dense (f.smoothLocus : Set X) :=
  f.dense_smoothLocus_of_perfectField

/-- The scheme-theoretic smooth locus is open and dense. -/
theorem smoothLocus_isOpen_and_dense_scheme [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    IsOpen (f.smoothLocus : Set X) ∧ Dense (f.smoothLocus : Set X) :=
  ⟨f.smoothLocus.2, f.dense_smoothLocus_of_perfectField⟩

end SmoothLocusDense

section SmoothImpliesRegular

variable (k : Type u) [Field k]

/-- `dim k[x₁,…,xₙ] = n`. -/
theorem smooth_ringKrullDim_mvPolynomial (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]; simp

/-- `dim k[x] = 1`. -/
theorem smooth_ringKrullDim_polynomial :
    ringKrullDim (Polynomial k) = 1 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing]; simp

/-- Localizing the polynomial ring at any prime gives a ring of Krull dimension
at most `n`. -/
theorem localization_mvPoly_krullDim_le (n : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin n) k)) [𝔭.IsPrime] :
    ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑n := by
  calc ringKrullDim (Localization.AtPrime 𝔭)
      ≤ ringKrullDim (MvPolynomial (Fin n) k) := by
        unfold ringKrullDim
        apply Order.krullDim_le_of_strictMono
          (PrimeSpectrum.comap (algebraMap _ (Localization.AtPrime 𝔭)))
        intro a b hab
        exact lt_of_le_of_ne (Ideal.comap_mono hab.le) fun heq =>
          hab.ne (PrimeSpectrum.localization_comap_injective _ 𝔭.primeCompl heq)
    _ = n := smooth_ringKrullDim_mvPolynomial k n

/-- Affine space `𝔸ⁿ_k = Spec k[x₁,…,xₙ]` is smooth over `k`. -/
theorem mvPolynomial_smooth (n : ℕ) : Smooth k (MvPolynomial (Fin n) k) :=
  Smooth.mk

/-- For any prime in the polynomial ring, the localization satisfies the
fundamental inequality `dim ≤ embDim`. -/
theorem localization_mvPoly_krullDim_le_embDim (n : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin n) k)) [𝔭.IsPrime] :
    ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑(embDim (Localization.AtPrime 𝔭)) :=
  krullDim_le_embDim _

end SmoothImpliesRegular

section LocalPIDRegular

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsPrincipalIdealRing R] [IsNoetherianRing R]

omit [IsDomain R] [IsNoetherianRing R] in
/-- In a non-field local PID, a generator of the maximal ideal is non-zero. -/
lemma maximalIdeal_generator_ne_zero (hR : ¬ IsField R) :
    Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal R) ≠ 0 := by
  intro h
  apply hR
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  rw [← Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal R)]
  simp [h]

omit [IsDomain R] [IsNoetherianRing R] in
/-- The embedding dimension of a non-field local PID is `1`. -/
theorem embDim_eq_one_of_localPID (hR : ¬ IsField R) : embDim R = 1 := by
  show Submodule.spanFinrank (IsLocalRing.maximalIdeal R) = 1
  rw [← Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal R)]
  exact Submodule.spanFinrank_singleton (maximalIdeal_generator_ne_zero R hR)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The Krull dimension of a non-field PID is `1`. -/
theorem ringKrullDim_eq_one_of_localPID (hR : ¬ IsField R) :
    ringKrullDim R = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one R hR

omit [IsNoetherianRing R] in
/-- A non-field local PID is regular: `dim = 1 = embDim`. -/
theorem isRegularLocal_of_localPID (hR : ¬ IsField R) :
    IsRegularLocal R := by
  unfold IsRegularLocal
  rw [ringKrullDim_eq_one_of_localPID R hR, embDim_eq_one_of_localPID R hR]
  simp

end LocalPIDRegular

section DVRRegular

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Any discrete valuation ring is a regular local ring of dimension `1`. -/
theorem isRegularLocal_of_DVR :
    IsRegularLocal R :=
  isRegularLocal_of_localPID R (IsDiscreteValuationRing.not_isField R)

end DVRRegular

section PowerSeriesRegular

variable (k : Type u) [Field k]

/-- The formal power series ring `k[[x]]` is a discrete valuation ring. -/
theorem smooth_powerSeries_isDVR :
    @IsDiscreteValuationRing (PowerSeries k) _ PowerSeries.instIsDomain :=
  PowerSeries.instIsDiscreteValuationRing

/-- `dim k[[x]] = 1`. -/
theorem powerSeries_ringKrullDim :
    ringKrullDim (PowerSeries k) = 1 :=
  @IsPrincipalIdealRing.ringKrullDim_eq_one (PowerSeries k) _
    PowerSeries.instIsDomain
    (@IsDiscreteValuationRing.toIsPrincipalIdealRing _ _ PowerSeries.instIsDomain
      PowerSeries.instIsDiscreteValuationRing)
    PowerSeries.not_isField

/-- The power series ring over a field is not itself a field. -/
theorem powerSeries_not_isField : ¬ IsField (PowerSeries k) :=
  PowerSeries.not_isField

/-- Adjoining a power series variable raises Krull dimension by at least one. -/
theorem powerSeries_ringKrullDim_succ_le (R : Type*) [CommRing R] :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_ringKrullDim_powerseries

/-- The multivariate power series ring `k[[x₁,…,x_d]]` is a local ring. -/
theorem mvPowerSeries_isLocalRing (d : ℕ) :
    IsLocalRing (MvPowerSeries (Fin d) k) :=
  inferInstance

/-- The maximal ideal of `k[[x]]` is the principal ideal `(x)`. -/
theorem powerSeries_maximalIdeal_eq :
    IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {PowerSeries.X} :=
  PowerSeries.maximalIdeal_eq_span_X

end PowerSeriesRegular

end
