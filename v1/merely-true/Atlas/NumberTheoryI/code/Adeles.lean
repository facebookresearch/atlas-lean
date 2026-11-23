/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Atlas.NumberTheoryI.code.KroneckerWeber
import Atlas.NumberTheoryI.code.AdicCompletionAlgebra

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField.Adeles

inductive Place (K : Type*) [Field K] [NumberField K] where
  | finite : HeightOneSpectrum (𝓞 K) → Place K
  | infinite : InfinitePlace K → Place K

instance instDecidableEqPlace (K : Type*) [Field K] [NumberField K] :
    DecidableEq (Place K) :=
  Classical.decEq _

variable {K : Type*} [Field K] [NumberField K]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem adicCompletion_finite_residueField
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (KroneckerWeber.completion_residueFieldEquiv (𝓞 K) K v).symm.toEquiv

noncomputable instance adicCompletion_compactSpace_integer
    (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    adicCompletion_finite_residueField K v⟩

noncomputable instance adicCompletion_properSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr
    (adicCompletion_compactSpace_integer v)

lemma isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have := (adicCompletion_compactSpace_integer v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at this

abbrev adeleRing := AdeleRing (𝓞 K) K

def placeNorm (v : Place K) (x : K) : ℝ :=
  match v with
  | .finite vi => NumberField.HeightOneSpectrum.adicAbv K vi x
  | .infinite w => w x

lemma placeNorm_mul (v : Place K) (x y : K) :
    placeNorm v (x * y) = placeNorm v x * placeNorm v y := by
  match v with
  | .finite vi => exact map_mul (NumberField.HeightOneSpectrum.adicAbv K vi) x y
  | .infinite w => exact w.1.map_mul x y

lemma placeNorm_nonneg (v : Place K) (x : K) : 0 ≤ placeNorm v x := by
  match v with
  | .finite vi => exact (NumberField.HeightOneSpectrum.adicAbv K vi).nonneg x
  | .infinite w => exact w.1.nonneg x

def placeNormAdele (v : Place K) (a : adeleRing (K := K)) : ℝ :=
  match v with
  | .finite vi => ‖a.2 vi‖
  | .infinite w => ‖a.1 w‖

lemma placeNorm_eq_placeNormAdele_algebraMap (v : Place K) (x : K) :
    placeNorm v x = placeNormAdele v (algebraMap K (adeleRing (K := K)) x) := by
  match v with
  | .infinite w =>
    show w x = ‖(algebraMap K (InfiniteAdeleRing K) x) w‖
    rw [show (algebraMap K (InfiniteAdeleRing K) x) w = algebraMap K w.Completion x from rfl]
    rw [show algebraMap K w.Completion x =
      (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]
    simp
  | .finite vi =>
    show NumberField.HeightOneSpectrum.adicAbv K vi x =
      ‖(algebraMap K (adeleRing (K := K)) x).2 vi‖
    rw [show (algebraMap K (adeleRing (K := K)) x).2 vi =
      algebraMap K (vi.adicCompletion K) x from rfl]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl]
    rw [FinitePlace.norm_embedding]

def adelicAbsVal (a : adeleRing (K := K)) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) *
  (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)

section RestrictedProductDirectLimit

open Filter Set Topology

theorem restrictedProduct_topology_eq_iSup {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    (𝓕 : Filter ι) :
    RestrictedProduct.topologicalSpace X U 𝓕 =
      ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
        TopologicalSpace.coinduced (RestrictedProduct.inclusion X U hS)
          (RestrictedProduct.topologicalSpace X U (𝓟 S)) :=
  RestrictedProduct.topologicalSpace_eq_iSup 𝓕

open scoped RestrictedProduct in
theorem restrictedProduct_inclusion_isEmbedding {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    {𝓕 : Filter ι} {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    Topology.IsEmbedding (RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.isEmbedding_inclusion_principal hS

open scoped RestrictedProduct in
theorem restrictedProduct_inclusion_isOpenEmbedding {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    (hU_open : ∀ i, IsOpen (U i))
    {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    Topology.IsOpenEmbedding (RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal hU_open hS

open scoped RestrictedProduct in
theorem restrictedProduct_continuous_iff {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    {𝓕 : Filter ι}
    {Y : Type*} [TopologicalSpace Y]
    {f : (Πʳ i, [X i, U i]_[𝓕]) → Y} :
    Continuous f ↔
      ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
        Continuous (f ∘ RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.continuous_dom

theorem finiteAdeleRing_topology_eq_iSup :
    RestrictedProduct.topologicalSpace
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K))
      cofinite =
    ⨆ (S : Set (HeightOneSpectrum (𝓞 K))) (hS : cofinite ≤ 𝓟 S),
      TopologicalSpace.coinduced
        (RestrictedProduct.inclusion
          (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) hS)
        (RestrictedProduct.topologicalSpace
          (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) (𝓟 S)) :=
  RestrictedProduct.topologicalSpace_eq_iSup cofinite

theorem finiteAdeleRing_inclusion_isOpenEmbedding
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : cofinite ≤ 𝓟 S) :
    Topology.IsOpenEmbedding
      (RestrictedProduct.inclusion
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K)) hS) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1) hS

end RestrictedProductDirectLimit

instance adeleRing_isTopologicalRing : IsTopologicalRing (adeleRing (K := K)) :=
  inferInstance

instance infiniteAdeleRing_t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

instance finiteAdeleRing_t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

instance adeleRing_t2Space : T2Space (adeleRing (K := K)) :=
  Prod.t2Space

instance finiteAdeleRing_locallyCompactSpace :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by


  letI wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)
      (Filter.Eventually.of_forall (fun v => isCompact_adicCompletionIntegers v))

  letI : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs

  infer_instance

instance adeleRing_locallyCompactSpace : LocallyCompactSpace (adeleRing (K := K)) :=
  Prod.locallyCompactSpace _ _

theorem diag_injective : Function.Injective (algebraMap K (adeleRing (K := K))) :=
  AdeleRing.algebraMap_injective (𝓞 K) K

abbrev principalSubgroup : AddSubgroup (adeleRing (K := K)) :=
  AdeleRing.principalSubgroup (𝓞 K) K

lemma eq_zero_of_integral_and_inf_lt_one (k : 𝓞 K)
    (hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1) :
    k = 0 := by
  suffices h : (algebraMap (𝓞 K) K) k = 0 from Subtype.coe_injective h
  by_contra hk
  have h_prod_lt : ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) ^ w.mult < 1 := by
    classical
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [(Finset.mul_prod_erase Finset.univ
        (fun w : InfinitePlace K => w (algebraMap (𝓞 K) K k) ^ w.mult)
        (Finset.mem_univ w₀)).symm]
    calc _ ≤ (w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult) * 1 := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.prod_le_one
            · intro w _; exact pow_nonneg (w.1.nonneg _) _
            · intro w _; exact pow_le_one₀ (w.1.nonneg _) (le_of_lt (hinf w))
          · exact le_of_lt (pow_pos (w₀.1.pos hk) _)
        _ = w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult := mul_one _
        _ < 1 := pow_lt_one₀ (w₀.1.nonneg _) (hinf w₀) w₀.mult_pos.ne'
  have h_prod := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K k)
  have h_norm_loc : (Algebra.norm ℚ) ((algebraMap (𝓞 K) K) k) =
    algebraMap ℤ ℚ ((Algebra.norm ℤ) k) :=
    Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ) k
  rw [h_norm_loc] at h_prod; rw [h_prod] at h_prod_lt
  have h_norm_zero : (Algebra.norm ℤ) k = 0 := by
    by_contra hn
    have h1 : |(((Algebra.norm ℤ) k : ℤ) : ℝ)| < 1 := by
      have : ((Algebra.norm ℤ k : ℤ) : ℝ) =
        ((algebraMap ℤ ℚ ((Algebra.norm ℤ) k) : ℚ) : ℝ) := rfl
      rw [this]; exact_mod_cast h_prod_lt
    have h2 := abs_lt.mp h1
    have h3 : (-1 : ℤ) < (Algebra.norm ℤ) k := by exact_mod_cast h2.1
    have h4 : ((Algebra.norm ℤ) k : ℤ) < 1 := by exact_mod_cast h2.2
    omega
  rw [Algebra.norm_eq_zero_iff] at h_norm_zero
  exact hk (by simp [h_norm_zero])

lemma mem_ringOfIntegers_of_finiteAdele_integral (x : K)
    (h : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈
      Set.range (RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)) :
    x ∈ (algebraMap (𝓞 K) K).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K x
  intro v
  obtain ⟨a, ha⟩ := h
  suffices Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 by
    rwa [show Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x from by
      rw [v.valuedAdicCompletion_def K]
      show Valued.extensionValuation ((x : v.adicCompletion K)) = _
      rw [Valued.extensionValuation_apply_coe]; rfl] at this
  change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v) ≤ 1
  rw [show (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v =
    (RestrictedProduct.structureMap _ _ _ a).val v from
    congr_arg (fun y => y.val v) ha.symm]
  exact (a v).prop

theorem principalAdeles_discrete :
    DiscreteTopology (principalSubgroup (K := K)) := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  let U_inf := {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
  let U_fin := Set.range (RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)
  refine ⟨U_inf ×ˢ U_fin, ?_, ?_⟩
  ·
    apply IsOpen.prod
    ·
      change IsOpen {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
      have : {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1} =
          ⋂ w, {f : InfiniteAdeleRing K | ‖f w‖ < 1} := by
        ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact isOpen_iInter_of_finite (fun w =>
        isOpen_lt (continuous_norm.comp (continuous_apply w)) continuous_const)
    ·
      exact (RestrictedProduct.isOpenEmbedding_structureMap
        (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)).isOpen_range
  ·
    ext ⟨a, ha⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, AddSubgroup.mk_eq_zero]
    constructor
    ·
      intro ⟨h_inf, h_fin⟩
      obtain ⟨x, hx⟩ := ha

      have hx_int : x ∈ (algebraMap (𝓞 K) K).range := by
        apply mem_ringOfIntegers_of_finiteAdele_integral
        rw [show algebraMap K (FiniteAdeleRing (𝓞 K) K) x = a.2 from by rw [← hx]; rfl]
        exact h_fin
      obtain ⟨k, hk⟩ := hx_int

      have hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1 := by
        intro w
        have hw := h_inf w
        rw [hk]
        have ha1 : a.1 = algebraMap K (InfiniteAdeleRing K) x := by rw [← hx]; rfl
        rw [ha1] at hw
        rw [show (algebraMap K (InfiniteAdeleRing K) x w : w.Completion) =
          algebraMap K w.Completion x from rfl] at hw
        rwa [show ‖algebraMap K w.Completion x‖ = w x from by
          rw [show algebraMap K w.Completion x =
            (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
          rw [InfinitePlace.Completion.norm_coe]; simp] at hw

      have hk0 := eq_zero_of_integral_and_inf_lt_one k hinf
      rw [← hx, ← hk, hk0, map_zero, map_zero]
    ·
      intro h0; subst h0
      exact ⟨fun w => by show ‖(0 : w.Completion)‖ < 1; rw [norm_zero]; exact one_pos,
             ⟨0, by ext v; rfl⟩⟩

instance infinitePlace_properSpace (v : InfinitePlace K) :
    ProperSpace v.Completion := by
  open InfinitePlace.Completion in
  constructor
  intro x r
  rcases v.isReal_or_isComplex with hv | hv
  · have e := isometryEquivRealOfIsReal hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩
  · have e := isometryEquivComplexOfIsComplex hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩

lemma isCompact_finiteAdeleRing_integralSet :
    IsCompact {a : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} := by
  have heq : {a : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} =
      Set.range (RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K))
        Filter.cofinite) := by
    rw [RestrictedProduct.range_structureMap]
    ext a; simp only [Set.mem_setOf_eq]
    exact ⟨fun h v => h v, fun h v => h v⟩
  rw [heq]
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ↑(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v; change CompactSpace (Valued.integer (v.adicCompletion K)); infer_instance
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

lemma adeles_integral_set_compact :
    IsCompact
      ((Set.pi Set.univ (fun (v : InfinitePlace K) =>
        Metric.closedBall (0 : v.Completion) 1)) ×ˢ
       {a : FiniteAdeleRing (𝓞 K) K |
         ∀ v : HeightOneSpectrum (𝓞 K),
           a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}) := by
  apply IsCompact.prod
  · exact isCompact_univ_pi (fun v => isCompact_closedBall 0 1)
  · exact isCompact_finiteAdeleRing_integralSet


lemma valued_algebraMap_eq_valuation_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = (v.valuation K) x := by
  rw [show algebraMap K (v.adicCompletion K) x =
    ↑((WithVal.equiv (v.valuation K)).symm x) from rfl]
  exact v.valuedAdicCompletion_eq_valuation' x

lemma algebraMap_div_mem_adicCompletionIntegers_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r d : 𝓞 K)
    (h : v.intValuation r ≤ v.intValuation d) :
    algebraMap K (v.adicCompletion K) ((r : K) / (d : K)) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  show Valued.v (algebraMap K (v.adicCompletion K) ((r : K) / (d : K))) ≤ 1
  rw [valued_algebraMap_eq_valuation_crt, map_div₀,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact div_le_one_of_le₀ h (WithZero.zero_le _)

lemma intValuation_le_exp_of_mem_pow_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ)
    (hr : r ∈ v.asIdeal ^ n) : v.intValuation r ≤ WithZero.exp (-↑n) := by
  rw [v.intValuation_le_pow_iff_dvd]
  rwa [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]

lemma intValuation_le_of_mem_pow_ge_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r d : 𝓞 K) (hd : d ≠ 0)
    (n : ℕ) (hn : ((-WithZero.log (v.intValuation d)).toNat) ≤ n)
    (hr : r ∈ v.asIdeal ^ n) :
    v.intValuation r ≤ v.intValuation d := by
  have hne := HeightOneSpectrum.intValuation_ne_zero v d hd
  have hle : WithZero.log (v.intValuation d) ≤ 0 := by
    have h1 := v.intValuation_le_one d
    rw [← WithZero.exp_log hne] at h1
    rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  calc v.intValuation r
      ≤ WithZero.exp (-↑n) := intValuation_le_exp_of_mem_pow_crt v r n hr
    _ ≤ WithZero.exp (-↑((-WithZero.log (v.intValuation d)).toNat)) := by
        rw [WithZero.exp_le_exp]; omega
    _ = v.intValuation d := by
        conv_rhs => rw [← WithZero.exp_log hne]
        congr 1; rw [Int.toNat_of_nonneg (neg_nonneg.mpr hle), neg_neg]

set_option maxHeartbeats 800000 in
lemma exists_integral_approx_at_place {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ∃ c : K, (x - algebraMap K (v.adicCompletion K) c) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  set U := (fun y => x - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hU_open : IsOpen U :=
    (continuous_const.sub continuous_id).isOpen_preimage _ (Valued.isOpen_valuationSubring _)
  have hU_ne : U.Nonempty :=
    ⟨x, show x - x ∈ (v.adicCompletionIntegers K : Set _) by
      rw [sub_self]; exact (v.adicCompletionIntegers K).zero_mem⟩
  obtain ⟨c, hc⟩ := (v.denseRange_algebraMap K).exists_mem_open hU_open hU_ne
  exact ⟨c, hc⟩

set_option maxHeartbeats 3200000 in
theorem crt_finite_places_covering (K : Type*) [Field K] [NumberField K]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ c : K, ∀ v : HeightOneSpectrum (𝓞 K),
      (a v - algebraMap K (v.adicCompletion K) c) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  classical

  have ha := a.property
  rw [Filter.eventually_cofinite] at ha
  let S := ha.toFinset

  have hdense : ∀ v : HeightOneSpectrum (𝓞 K), ∃ c : K,
      (a v - algebraMap K (v.adicCompletion K) c) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => exists_integral_approx_at_place v (a v)
  choose c_all hc_all using hdense

  obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (S.image c_all)
  have hd_ne : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hd_K_ne : ((d : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hd_ne

  have hn_exists : ∀ v ∈ S, ∃ n : 𝓞 K,
      algebraMap (𝓞 K) K n = (d : 𝓞 K) • c_all v :=
    fun v hv => hd _ (Finset.mem_image_of_mem _ hv)

  let e : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => (-WithZero.log (v.intValuation d)).toNat

  have hT_finite : Set.Finite {v : HeightOneSpectrum (𝓞 K) | d ∈ v.asIdeal} := by
    have hI : Ideal.span ({d} : Set (𝓞 K)) ≠ 0 := by simp [hd_ne]
    exact (Ideal.finite_factors hI).subset
      (fun v hv => Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)))
  let T := hT_finite.toFinset \ S
  let ST := S ∪ T


  let hn_exists' : ∀ v ∈ S, 𝓞 K := fun v hv => (hn_exists v hv).choose
  have hn_spec : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S),
      algebraMap (𝓞 K) K (hn_exists' v hv) = (d : 𝓞 K) • c_all v :=
    fun v hv => (hn_exists v hv).choose_spec
  let target : {v // v ∈ ST} → 𝓞 K := fun ⟨v, hv⟩ =>
    if h : v ∈ S then hn_exists' v h else 0
  have hprime : ∀ i ∈ ST, Prime ((id i : HeightOneSpectrum (𝓞 K)).asIdeal) :=
    fun i _ => i.prime
  have hcoprime : ∀ i ∈ ST, ∀ j ∈ ST, i ≠ j →
      (id i : HeightOneSpectrum (𝓞 K)).asIdeal ≠ (id j).asIdeal :=
    fun _ _ _ _ h heq => h (HeightOneSpectrum.ext heq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) e hprime hcoprime target

  refine ⟨(y : K) / (d : K), fun v => ?_⟩
  by_cases hv_in_S : v ∈ S
  ·
    have hv_ST : v ∈ ST := Finset.mem_union_left T hv_in_S
    have hy_v := hy v hv_ST


    have htarget : target ⟨v, hv_ST⟩ = hn_exists' v hv_in_S := dif_pos hv_in_S
    rw [htarget] at hy_v

    have hmem_neg : hn_exists' v hv_in_S - y ∈ v.asIdeal ^ e v := by
      rw [show hn_exists' v hv_in_S - y = -(y - hn_exists' v hv_in_S) from by ring]
      exact neg_mem hy_v

    have hval_le : v.intValuation (hn_exists' v hv_in_S - y) ≤ v.intValuation d :=
      intValuation_le_of_mem_pow_ge_crt v (hn_exists' v hv_in_S - y) d hd_ne (e v) le_rfl hmem_neg

    have hdiv_mem : algebraMap K (v.adicCompletion K)
        ((hn_exists' v hv_in_S - y : 𝓞 K) / (d : K)) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      algebraMap_div_mem_adicCompletionIntegers_crt v _ d hval_le


    have hc_v_eq : c_all v = (hn_exists' v hv_in_S : K) / (d : K) := by
      have := hn_spec v hv_in_S
      rw [Algebra.smul_def] at this
      rw [eq_div_iff hd_K_ne, mul_comm]
      exact this.symm
    rw [show (y : K) / (d : K) = c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) from by
      rw [hc_v_eq]; field_simp; ring]
    rw [show a v - algebraMap K (v.adicCompletion K)
        (c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) =
      (a v - algebraMap K (v.adicCompletion K) (c_all v)) -
        algebraMap K (v.adicCompletion K) (((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) from by
      simp only [map_add]; ring]
    apply sub_mem (hc_all v)


    rw [show ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) =
      -((hn_exists' v hv_in_S : K) - (y : K)) / (d : K) from by ring]
    rw [neg_div]
    rw [map_neg]
    exact neg_mem hdiv_mem
  ·


    have hav : a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      by_contra h
      exact hv_in_S (ha.mem_toFinset.mpr h)

    suffices h_yd : algebraMap K (v.adicCompletion K) ((y : K) / (d : K)) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from by
      have := sub_mem hav h_yd
      convert this using 1
    by_cases hv_d : d ∈ v.asIdeal
    ·
      have hv_T : v ∈ T := by
        simp only [T, Finset.mem_sdiff]
        exact ⟨hT_finite.mem_toFinset.mpr hv_d, hv_in_S⟩
      have hv_ST : v ∈ ST := Finset.mem_union_right S hv_T
      have hy_v := hy v hv_ST
      have htarget : target ⟨v, hv_ST⟩ = 0 := dif_neg hv_in_S
      rw [htarget] at hy_v
      simp only [sub_zero] at hy_v

      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (intValuation_le_of_mem_pow_ge_crt v y d hd_ne (e v) le_rfl hy_v)
    ·
      have hval_d : v.intValuation d = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr hv_d
      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (by rw [hval_d]; exact v.intValuation_le_one y)

open scoped Classical in
noncomputable def coveringBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  max 1 (∑ i, ‖mixedEmbedding.latticeBasis K i‖)

lemma one_le_coveringBound (K : Type*) [Field K] [NumberField K] :
    1 ≤ coveringBound K :=
  le_max_left 1 _

lemma coveringBound_pos (K : Type*) [Field K] [NumberField K] :
    0 < coveringBound K :=
  lt_of_lt_of_le one_pos (one_le_coveringBound K)

lemma coveringBound_ne_zero (K : Type*) [Field K] [NumberField K] :
    coveringBound K ≠ 0 :=
  ne_of_gt (coveringBound_pos K)

lemma coveringBound_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ coveringBound K :=
  le_of_lt (coveringBound_pos K)


def PiTensorCompletion (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L] :=
  (v : InfinitePlace K) → (L ⊗[K] v.Completion)

instance piTensorCompletion_commRing (K L : Type*)
    [Field K] [NumberField K] [Field L] [Algebra K L] :
    CommRing (PiTensorCompletion K L) := Pi.commRing

attribute [local instance] WithAbs.algebraLeft

set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCompletionToFiberProd
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    L ⊗[K] v.Completion →+*
      ((w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) := by
  apply Pi.ringHom
  intro ⟨w, hw⟩
  letI : Algebra K w.Completion := Algebra.restrictScalars K L w.Completion
  haveI : IsScalarTower K L w.Completion := by
    constructor; intro x y z; change (x • y) • z = x • (y • z); simp [smul_assoc]
  haveI : w.1.LiesOver v.1 := ⟨by
    have h1 : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← h1]; rfl⟩
  haveI itv : IsTopologicalRing (WithAbs v.1) := inferInstance
  haveI itw : IsTopologicalRing (WithAbs w.1) := inferInstance
  haveI uv : IsUniformAddGroup (WithAbs v.1) := inferInstance
  haveI uw : IsUniformAddGroup (WithAbs w.1) := inferInstance
  have hiso := InfinitePlace.LiesOver.isometry_algebraMap w (v := v)
  let isoHom : v.Completion →+* w.Completion :=
    @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
      (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
  let vToW : v.Completion →ₐ[K] w.Completion := {
    toRingHom := isoHom
    commutes' := by
      intro r
      change @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
        (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
        (↑(algebraMap K (WithAbs v.1) r)) = algebraMap K w.Completion r
      rw [@Isometry.mapRingHom_coe _ _ _ _ itv uv _ _ uw itw _ hiso]
      congr 1
  }
  let lToW : L →ₐ[K] w.Completion := {
    toRingHom := algebraMap L w.Completion
    commutes' := fun _ => rfl
  }
  exact (Algebra.TensorProduct.productMap lToW vToW).toRingHom




def sigmaPiRegroup (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ((v : InfinitePlace K) →
      (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) ≃+*
    InfiniteAdeleRing L :=
  RingEquiv.mk
    { toFun := fun g w => g (w.comap (algebraMap K L)) ⟨w, rfl⟩
      invFun := fun h _v ⟨w, _⟩ => h w
      left_inv := fun g => by ext v ⟨w, hw⟩; subst hw; rfl
      right_inv := fun _ => rfl }
    (fun _ _ => rfl) (fun _ _ => rfl)




instance finAdeleRing_algebra_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

instance finAdeleRing_scalarTower_base_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K K (FiniteAdeleRing (𝓞 L) L) :=
  ⟨fun r s x => by simp [Algebra.smul_def, mul_assoc]⟩

instance finAdeleRing_scalarTower_base_ext (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) := by
  constructor; intro r l x; simp only [Algebra.smul_def]; rw [map_mul, mul_assoc]; rfl

noncomputable def primeBelow (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  isPrime := Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  ne_bot := by intro h; exact w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

noncomputable def localBaseChangeMap (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (HeightOneSpectrum.valuation K (primeBelow K L w)) →+*
      w.adicCompletion L :=
  (UniformSpace.Completion.coeRingHom (α := WithVal (HeightOneSpectrum.valuation L w))).comp
    ((WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))).toRingHom))

lemma localBaseChangeMap_continuous (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (localBaseChangeMap K L w) := by
  set v := primeBelow K L w
  set g : WithVal (HeightOneSpectrum.valuation K v) →+*
      WithVal (HeightOneSpectrum.valuation L w) :=
    (WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K v)).toRingHom) with hg_def

  show Continuous (UniformSpace.Completion.coeRingHom.comp g)
  apply Continuous.comp (UniformSpace.Completion.continuous_coe _)


  exact algebraMap_withVal_continuous_general K v w (le_refl _)

noncomputable def baseChangeAtPrime (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    (primeBelow K L w).adicCompletion K →+* w.adicCompletion L :=
  UniformSpace.Completion.extensionHom
    (localBaseChangeMap K L w) (localBaseChangeMap_continuous K L w)

lemma baseChangeAtPrime_mem_integers (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L))
    (x : (primeBelow K L w).adicCompletion K)
    (hx : x ∈ (primeBelow K L w).adicCompletionIntegers K) :
    (baseChangeAtPrime K L w) x ∈ w.adicCompletionIntegers L := by

  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx


  have hclosed : IsClosed {y : (primeBelow K L w).adicCompletion K |
      Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
    have h1 : {y : (primeBelow K L w).adicCompletion K |
        Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
    rw [h1]
    apply IsClosed.union
    ·
      have : {y : (primeBelow K L w).adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring :
            ValuationSubring ((primeBelow K L w).adicCompletion K)) :
            Set ((primeBelow K L w).adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring
        ((primeBelow K L w).adicCompletion K)).2.isClosed_compl
    ·
      have hf_cont : Continuous (baseChangeAtPrime K L w) :=
        UniformSpace.Completion.continuous_extension
      have : {y : (primeBelow K L w).adicCompletion K |
          Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
          (baseChangeAtPrime K L w :
            (primeBelow K L w).adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hf_cont

  have hdense : ∀ (k : WithVal (HeightOneSpectrum.valuation K (primeBelow K L w))),
      Valued.v (↑k : (primeBelow K L w).adicCompletion K) ≤ 1 →
        Valued.v ((baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hf_coe : (baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K) =
        localBaseChangeMap K L w k :=
      UniformSpace.Completion.extensionHom_coe _ (localBaseChangeMap_continuous K L w) k
    rw [hf_coe]


    have hval : Valued.v ((localBaseChangeMap K L w) k) =
        HeightOneSpectrum.valuation L w (algebraMap K L
          ((WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))) k)) := by
      simp only [localBaseChangeMap, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      erw [Valued.valuedCompletion_apply]
      rw [← WithVal.val_apply_equiv (HeightOneSpectrum.valuation L w)]
      simp only [RingEquiv.apply_symm_apply]
    rw [hval]


    haveI : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
    rw [valuation_extends_with_ramificationIdx K L (primeBelow K L w) w]
    rw [WithVal.val_apply_equiv]
    exact pow_le_one₀ (WithZero.zero_le _) hk


  exact UniformSpace.Completion.induction_on x hclosed (fun k => hdense k) hx

lemma baseChange_restricted_condition (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∀ᶠ (w : HeightOneSpectrum (𝓞 L)) in Filter.cofinite,
      (baseChangeAtPrime K L w) (a (primeBelow K L w)) ∈
        ↑(w.adicCompletionIntegers L) := by


  have ha := a.property

  rw [Filter.eventually_cofinite] at ha ⊢


  set S := {v : HeightOneSpectrum (𝓞 K) | a v ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} with hS_def

  apply Set.Finite.subset (s := primeBelow K L ⁻¹' S)
  ·


    have hS_eq : primeBelow K L ⁻¹' S = ⋃ v ∈ S, {w | primeBelow K L w = v} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨primeBelow K L w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => hvw ▸ hv⟩
    rw [hS_eq]
    apply ha.biUnion
    intro v _


    have hinj : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)) :=
      fun a b h => HeightOneSpectrum.ext_iff.mpr h
    apply Set.Finite.subset ((primesOver_finite v.asIdeal (𝓞 L)).preimage hinj.injOn)
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
    refine ⟨w.isPrime, ⟨?_⟩⟩
    show v.asIdeal = Ideal.under (𝓞 K) w.asIdeal
    rw [Ideal.under, ← hw]
    rfl

  ·
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def] at hw ⊢


    intro hmem
    exact hw (baseChangeAtPrime_mem_integers K L w _ hmem)

lemma baseChange_commutes (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (k : K) :
    (RestrictedProduct.mk
      (fun w => (baseChangeAtPrime K L w)
        ((algebraMap K (FiniteAdeleRing (𝓞 K) K) k) (primeBelow K L w)))
      (baseChange_restricted_condition K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) k))) =
    algebraMap K (FiniteAdeleRing (𝓞 L) L) k := by
  apply RestrictedProduct.ext; intro w
  simp only [RestrictedProduct.mk_apply]

  have hLHS : ((algebraMap K (FiniteAdeleRing (𝓞 K) K)) k) (primeBelow K L w) =
    (algebraMap K ((primeBelow K L w).adicCompletion K) k) := rfl
  rw [hLHS]

  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp]

  simp only [baseChangeAtPrime, UniformSpace.Completion.extensionHom_coe]

  simp only [localBaseChangeMap, RingHom.comp_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

noncomputable def finAdeleRing_baseChangeHom (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] FiniteAdeleRing (𝓞 L) L where
  toFun a := RestrictedProduct.mk
    (fun w => (baseChangeAtPrime K L w) (a (primeBelow K L w)))
    (baseChange_restricted_condition K L a)
  map_one' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (1 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 1 from rfl, map_one]
    rfl
  map_mul' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a * b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) * b (primeBelow K L w) from rfl, map_mul]
    rfl
  map_zero' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (0 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 0 from rfl, map_zero]
    rfl
  map_add' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a + b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) + b (primeBelow K L w) from rfl, map_add]
    rfl
  commutes' := fun k => baseChange_commutes K L k

def finAdeleRing_includeExt (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    L →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  (Algebra.ofId L (FiniteAdeleRing (𝓞 L) L)).restrictScalars K

def finAdeleRing_tensor_forward (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L) →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (finAdeleRing_baseChangeHom K L)
    (finAdeleRing_includeExt K L) (fun _ _ => Commute.all _ _)













instance adeleRing_algebra_base (L : Type*) [Field L] [NumberField L]
    [Algebra K L] :
    Algebra K (AdeleRing (𝓞 L) L) :=
  Algebra.compHom (AdeleRing (𝓞 L) L) (algebraMap K L)

omit [NumberField K] in
theorem adeleRing_algebra_base_algebraMap (L : Type*) [Field L] [NumberField L]
    [Algebra K L] :
    algebraMap K (AdeleRing (𝓞 L) L) =
      (algebraMap L (AdeleRing (𝓞 L) L)).comp (algebraMap K L) :=
  rfl





def adelicBox (a : adeleRing (K := K)) : Set (adeleRing (K := K)) :=
  { t | (∀ v : HeightOneSpectrum (𝓞 K), ‖t.2 v‖ ≤ ‖a.2 v‖) ∧
        (∀ w : InfinitePlace K, ‖t.1 w‖ ≤ ‖a.1 w‖ / 4) }











instance instNormOneClass_Completion (w : InfinitePlace K) : NormOneClass w.Completion where
  norm_one := by
    have : (1 : w.Completion) = algebraMap K w.Completion 1 := (map_one _).symm
    rw [this, show algebraMap K w.Completion 1 =
      (↑((WithAbs.equiv w.1).symm 1) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]; simp

instance instNontrivNormedField_InfCompl (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion := by
  refine { InfinitePlace.Completion.instNormedField w with non_trivial := ?_ }
  use algebraMap K w.Completion 2
  rw [show algebraMap K w.Completion 2 =
    (↑((WithAbs.equiv w.1).symm 2) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]
  show 1 < w 2
  rw [(w.norm_embedding_eq 2).symm]; simp only [map_ofNat]; norm_num

lemma mem_adicCompletionIntegers_iff_norm_le_one (vi : HeightOneSpectrum (𝓞 K))
    (x : vi.adicCompletion K) :
    x ∈ vi.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff (L := vi.adicCompletion K)
    (Γ₀ := WithZero (Multiplicative ℤ))).symm

theorem exists_strategic_adele
    (B : ℝ) (hB : 0 < B)
    (S : Finset (Place K)) (w : Place K) (hw : w ∉ S)
    (ε : (v : Place K) → v ∈ S → ℝ) (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
    ∃ (z : adeleRing (K := K)),
      adelicAbsVal z > B ∧
      (∀ v (hv : v ∈ S), placeNormAdele v z ≤ ε v hv) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNormAdele v z ≤ 1) ∧
      (Function.mulSupport
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => ‖z.2 v‖)).Finite := by
  classical
  rcases w with ⟨vi_w⟩ | ⟨w_inf⟩
  ·


    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1

    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let s_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1


    let P_inf : ℝ := ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult
    have hP_inf_pos : 0 < P_inf := by
      apply Finset.prod_pos
      intro w' _
      apply pow_pos
      simp only [inf_fn]
      split_ifs with hS
      · exact (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]

    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖s_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos
      intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [s_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
        (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec
        (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_pos hP_fin_pos

    letI := Valued.toNontriviallyNormedField (vi_w.adicCompletion K)
      (WithZero (Multiplicative ℤ))
    let vi_w_elem := Classical.choose
      (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))
    have hw_spec : (B + 1) / P < ‖vi_w_elem‖ :=
      Classical.choose_spec
        (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))

    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then s_fn vi
      else if h : vi = vi_w then h ▸ vi_w_elem
      else 1


    have fin_mem : ∀ᶠ vi in Filter.cofinite,
        fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S_fin.finite_toSet).union (Set.finite_singleton vi_w)
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Set.mem_union, Finset.mem_coe, S_fin, Finset.mem_preimage,
          Set.mem_singleton_iff] at h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [fin_fn, dif_neg h1, dif_neg h2] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩

    ·


      unfold adelicAbsVal
      simp only [z]

      have hinf_eq : ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult = P_inf := rfl


      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖

      have hsupp : Function.mulSupport g ⊆ ↑(S_fin ∪ {vi_w}) := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
          S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
        by_contra h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [g, fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
        exact hvi rfl

      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin ∪ {vi_w}, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp

      have hvi_w_notin : vi_w ∉ S_fin := by
        simp only [S_fin, Finset.mem_preimage]
        exact hw

      have hsplit : ∏ vi ∈ S_fin ∪ {vi_w}, g vi =
          (∏ vi ∈ S_fin, g vi) * (∏ vi ∈ ({vi_w} : Finset _), g vi) :=
        Finset.prod_union (Finset.disjoint_singleton_right.mpr hvi_w_notin)

      have hsingleton : ∏ vi ∈ ({vi_w} : Finset _), g vi = ‖vi_w_elem‖ := by
        simp only [Finset.prod_singleton, g, fin_fn, dif_neg hw, dite_true]

      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl
        intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]


      have hfinprod_val : ∏ᶠ vi, g vi = P_fin * ‖vi_w_elem‖ := by
        rw [hfin_eq, hsplit, hS_prod, hsingleton]

      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]

      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin * ‖vi_w_elem‖ := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val

      have hbound : P_inf * (P_fin * ‖vi_w_elem‖) > B := by
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ‖vi_w_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖vi_w_elem‖ * (P_inf * P_fin) := rfl
          _ = P_inf * (P_fin * ‖vi_w_elem‖) := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
            ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
          P_inf * (P_fin * ‖vi_w_elem‖) := by
        rw [hinf_eq]; congr 1
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, s_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, _ =>
        show ‖inf_fn w'‖ ≤ 1
        simp only [inf_fn, dif_neg hvS, norm_one, le_refl]
      | .finite vi, hvS, hne =>
        show ‖fin_fn vi‖ ≤ 1
        have hnotW : vi ≠ vi_w := fun h => hne (congrArg Place.finite h)
        simp only [fin_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
    ·
      apply Set.Finite.subset ((S_fin ∪ {vi_w}).finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
        S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
      by_contra h_not
      push Not at h_not
      have h1 : ¬ Place.finite vi ∈ S := h_not.1
      have h2 : ¬ vi = vi_w := h_not.2
      simp only [fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
      exact hvi rfl

  ·

    let inf_S_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1
    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1

    let P_inf_other : ℝ := ∏ w' : InfinitePlace K, ‖inf_S_fn w'‖ ^ w'.mult
    have hP_inf_other_pos : 0 < P_inf_other := by
      apply Finset.prod_pos; intro w' _; apply pow_pos
      simp only [inf_S_fn]; split_ifs with hS
      · exact (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]
    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖fin_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos; intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [fin_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec (NormedField.exists_norm_lt (vi.adicCompletion K)
        (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf_other * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_other_pos hP_fin_pos

    let w_inf_elem := Classical.choose
      (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_spec : (B + 1) / P + 1 < ‖w_inf_elem‖ :=
      Classical.choose_spec (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_gt_one : 1 < ‖w_inf_elem‖ := by
      calc 1 ≤ (B + 1) / P + 1 := le_add_of_nonneg_left (div_nonneg (by linarith) (le_of_lt hP_pos))
        _ < ‖w_inf_elem‖ := hw_spec
    have hw_norm_pos : 0 < ‖w_inf_elem‖ := by linarith

    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        inf_S_fn w'
      else if h : w' = w_inf then h ▸ w_inf_elem
      else 1

    have fin_mem : ∀ᶠ vi in Filter.cofinite,
        fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S.preimage Place.finite
            (fun a _ b _ h => Place.finite.inj h)).finite_toSet
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Finset.mem_coe, Finset.mem_preimage] at h_not
        simp only [fin_fn, dif_neg h_not] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩

    ·
      unfold adelicAbsVal
      simp only [z]


      have hinf_S : ∀ w' : InfinitePlace K, w' ≠ w_inf →
          ‖inf_fn w'‖ = ‖inf_S_fn w'‖ := by
        intro w' hw'
        simp only [inf_fn]
        rw [dite_eq_ite]
        split_ifs with hS
        · simp only [inf_S_fn, dif_pos hS]
        · simp only [inf_S_fn, dif_neg (show ¬ Place.infinite w' ∈ S from by
            intro hc; exact hS hc), norm_one]
      have hinf_w : ‖inf_fn w_inf‖ = ‖w_inf_elem‖ := by
        simp only [inf_fn, dif_neg hw, dite_true]

      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖
      have hsupp : Function.mulSupport g ⊆ ↑S_fin := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
        by_contra h_not
        simp only [g, fin_fn, dif_neg h_not, norm_one] at hvi
        exact hvi rfl
      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp
      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl; intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]
      have hfinprod_val : ∏ᶠ vi, g vi = P_fin := by
        rw [hfin_eq, hS_prod]
      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]
      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val


      have hinf_S_at_w : ‖inf_S_fn w_inf‖ = 1 := by
        simp only [inf_S_fn, dif_neg hw, norm_one]
      have hinf_prod_eq : (∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult) =
          P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult := by

        have hmem : w_inf ∈ Finset.univ := Finset.mem_univ w_inf

        rw [← Finset.mul_prod_erase _ _ hmem]

        rw [hinf_w]

        have hlhs : ∏ x ∈ Finset.univ.erase w_inf, ‖inf_fn x‖ ^ x.mult =
            ∏ x ∈ Finset.univ.erase w_inf, ‖inf_S_fn x‖ ^ x.mult := by
          apply Finset.prod_congr rfl
          intro w' hw'
          rw [Finset.mem_erase] at hw'
          rw [hinf_S w' hw'.1]
        rw [hlhs]


        have hP_factor : P_inf_other =
            (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) w_inf *
            ∏ x ∈ Finset.univ.erase w_inf, (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) x :=
          (Finset.mul_prod_erase _ _ hmem).symm
        simp only at hP_factor
        rw [hP_factor, hinf_S_at_w, one_pow, one_mul]
        ring
      have hbound : P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin > B := by
        have h_mult_pos : 0 < w_inf.mult := w_inf.mult_pos
        have hpow_ge : ‖w_inf_elem‖ ^ w_inf.mult ≥ ‖w_inf_elem‖ :=
          le_self_pow₀ (le_of_lt hw_gt_one) h_mult_pos.ne'
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ((B + 1) / P + 1) * P := by nlinarith
          _ < ‖w_inf_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖w_inf_elem‖ * (P_inf_other * P_fin) := rfl
          _ ≤ ‖w_inf_elem‖ ^ w_inf.mult * (P_inf_other * P_fin) := by
              exact mul_le_mul_of_nonneg_right hpow_ge (le_of_lt hP_pos)
          _ = P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
            ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
          P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by
        rw [hinf_prod_eq]; ring_nf; rw [hfp_eq]
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, inf_S_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, hne =>
        show ‖inf_fn w'‖ ≤ 1
        have hnotW : w' ≠ w_inf := fun h => hne (congrArg Place.infinite h)
        simp only [inf_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
      | .finite vi, hvS, _ =>
        show ‖fin_fn vi‖ ≤ 1
        simp only [fin_fn, dif_neg hvS, norm_one, le_refl]
    ·
      apply Set.Finite.subset (S_fin.finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
      by_contra h_not
      simp only [fin_fn, dif_neg h_not, norm_one] at hvi
      exact hvi rfl


lemma adicAbv_le_one_of_mem_integers_algebraMap (vi : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : algebraMap K (vi.adicCompletion K) x ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))) :
    NumberField.HeightOneSpectrum.adicAbv K vi x ≤ 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def]
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K)] at hx
  have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
  rw [this] at hx
  rw [vi.valuedAdicCompletion_eq_valuation' x] at hx
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal vi)).mpr hx

omit [NumberField K] in
lemma placeNorm_infinite_eq_norm_algebraMap (w : InfinitePlace K) (x : K) :
    w x = ‖algebraMap K w.Completion x‖ := by
  rw [show algebraMap K w.Completion x =
    (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]; simp


theorem global_field_dense_in_infiniteAdeleRing :
    Dense (Set.range (algebraMap K (InfiniteAdeleRing K))) :=
  InfiniteAdeleRing.denseRange_algebraMap K


@[reducible]
def placeCompletion : Place K → Type _
  | .finite vi => vi.adicCompletion K
  | .infinite w => w.Completion

instance instTopologicalSpacePlaceCompletion (v : Place K) :
    TopologicalSpace (placeCompletion v) := by
  cases v with
  | finite vi => exact inferInstance
  | infinite w => exact inferInstance

def placeIntegerSet : (v : Place K) → Set (placeCompletion v)
  | .finite vi => (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
  | .infinite _ => Set.univ

abbrev restrictedProductAwayFrom (w : Place K) : Type _ :=
  RestrictedProduct
    (fun (v : {v : Place K // v ≠ w}) => placeCompletion v.val)
    (fun (v : {v : Place K // v ≠ w}) => placeIntegerSet v.val)
    Filter.cofinite

@[reducible]
def embedAtPlace : (v : Place K) → K → placeCompletion v
  | .finite vi => algebraMap K (vi.adicCompletion K)
  | .infinite w => algebraMap K w.Completion

def diagonalAwayFrom (w : Place K) (x : K) : restrictedProductAwayFrom w :=
  RestrictedProduct.mk
    (fun (v : {v : Place K // v ≠ w}) => embedAtPlace v.val x)
    (by


     rw [Filter.eventually_cofinite]

     set f : {v : Place K // v ≠ w} → Option (HeightOneSpectrum (𝓞 K)) :=
       fun i => match i.val with
         | .finite vi => some vi
         | .infinite _ => none
     apply Set.Finite.of_injOn (f := f)
       (t := Option.some '' HeightOneSpectrum.Support (𝓞 K) x)
     ·
       intro ⟨v, hv⟩ hmem
       simp only [Set.mem_setOf_eq] at hmem
       cases v with
       | infinite _ => simp [placeIntegerSet] at hmem
       | finite vi =>
         simp only [f, Set.mem_image]
         refine ⟨vi, ?_, rfl⟩
         rw [HeightOneSpectrum.Support, Set.mem_setOf_eq]
         simp only [placeIntegerSet, SetLike.mem_coe, embedAtPlace] at hmem
         rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hmem
         have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
         rw [this] at hmem
         rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hmem
     ·
       intro ⟨v₁, hv₁⟩ hmem₁ ⟨v₂, hv₂⟩ hmem₂ hfeq
       simp only [Set.mem_setOf_eq] at hmem₁ hmem₂
       cases v₁ with
       | infinite _ => simp [placeIntegerSet] at hmem₁
       | finite vi₁ =>
         cases v₂ with
         | infinite _ => simp [placeIntegerSet] at hmem₂
         | finite vi₂ =>
           simp only [f] at hfeq
           have : vi₁ = vi₂ := Option.some_injective _ hfeq
           subst this; rfl
     ·
       exact (HeightOneSpectrum.Support.finite (𝓞 K) x).image _)

lemma isOpen_placeIntegerSet (v : Place K) : IsOpen (placeIntegerSet v) := by
  cases v with
  | finite vi => exact Valued.isOpen_valuationSubring _
  | infinite _ => exact isOpen_univ

lemma placeNorm_le_one_imp_mem_placeIntegerSet (v : Place K) (x : K)
    (hx : placeNorm v x ≤ 1) : embedAtPlace v x ∈ placeIntegerSet v := by
  cases v with
  | finite vi =>
    show algebraMap K (vi.adicCompletion K) x ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl,
        FinitePlace.norm_embedding]
    exact hx
  | infinite _ => exact Set.mem_univ _

omit [NumberField K] in
lemma infPlace_norm_algebraMap (wi : InfinitePlace K) (x : K) :
    ‖algebraMap K wi.Completion x‖ = wi.1 x := by
  change ‖(↑((WithAbs.equiv wi.1).symm x) :
    UniformSpace.Completion (WithAbs wi.1))‖ = _
  rw [UniformSpace.Completion.norm_coe]; rfl

omit [NumberField K] in
lemma infPlace_denseRange_algebraMap (wi : InfinitePlace K) :
    DenseRange (algebraMap K wi.Completion) := by
  suffices h : DenseRange (UniformSpace.Completion.coe' ∘
      (WithAbs.equiv wi.1).symm : K → UniformSpace.Completion (WithAbs wi.1)) from h
  exact DenseRange.comp
    (@UniformSpace.Completion.denseRange_coe (WithAbs wi.1) _)
    ((WithAbs.equiv wi.1).symm.surjective.denseRange)
    (UniformSpace.Completion.continuous_coe _)


end NumberField.Adeles
