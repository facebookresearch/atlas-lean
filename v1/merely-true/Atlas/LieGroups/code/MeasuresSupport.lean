/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Atlas.LieGroups.code.CompactMeasures
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

noncomputable section

open Filter Topology

namespace Meas

def embedMap (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] : (X →₀ ℂ) →ₗ[ℂ] MX :=
  Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))

def atomicIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (K : Set X) : Set MX :=
  (embedMap X MX) '' { f : X →₀ ℂ | ↑f.support ⊆ K }

def IsSupportedIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) (K : Set X) : Prop :=
  μ ∈ closure (atomicIn K)

end Meas


namespace Meas

def functionalSupp (X : Type*) [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) : Set X :=
  ⋂₀ { K : Set X | IsClosed K ∧ IsSupportedIn (X := X) μ K }

end Meas

noncomputable instance ContinuousMap.instIsUniformAddGroupComplex
    {X : Type*} [TopologicalSpace X] :
    IsUniformAddGroup C(X, ℂ) :=
  IsUniformInducing.isUniformAddGroup
    ({ toFun := ContinuousMap.toUniformOnFunIsCompact
       map_zero' := rfl
       map_add' := fun _ _ => rfl } : C(X, ℂ) →+ UniformOnFun X ℂ {K | IsCompact K})
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing

namespace ConcreteMeasSupp

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

def IsSupportedIn (μ : C(X, ℂ) →L[ℂ] ℂ) (K : Set X) : Prop :=
  ∀ f : C(X, ℂ), (∀ x ∈ K, f x = 0) → μ f = 0

def IsWeakStarCauchy (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) : Prop :=
  ∀ f : C(X, ℂ), CauchySeq (fun n => μ n f)

def TendstoWeakStar (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (μ₀ : C(X, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (μ₀ f))

theorem cauchySeq_supportedIn_compact
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (hcauchy : IsWeakStarCauchy μ) :
    ∃ K : Set X, IsCompact K ∧ ∀ n, IsSupportedIn (μ n) K := by

  rcases isEmpty_or_nonempty X with hempty | hne
  · exact ⟨∅, isCompact_empty, fun n f hf => by
      have : f = 0 := by ext x; exact IsEmpty.elim hempty x
      simp [this, map_zero]⟩

  haveI : BaireSpace C(X, ℂ) := inferInstance

  let A : ℕ → Set C(X, ℂ) := fun k => {f | ∀ n, ‖μ n f‖ ≤ ↑k}

  have A_closed : ∀ k, IsClosed (A k) := by
    intro k
    show IsClosed {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k}
    suffices h : {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k} =
        ⋂ n, (fun f => ‖μ n f‖) ⁻¹' Set.Iic ↑k by
      rw [h]
      exact isClosed_iInter fun n => IsClosed.preimage ((μ n).continuous.norm) isClosed_Iic
    ext f; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]

  have A_cover : ∀ f : C(X, ℂ), ∃ k, f ∈ A k := by
    intro f
    obtain ⟨R, _, hR⟩ := cauchySeq_bdd (hcauchy f)
    refine ⟨⌈‖μ 0 f‖ + R⌉₊, fun n => ?_⟩
    calc ‖μ n f‖ = ‖μ 0 f + (μ n f - μ 0 f)‖ := by ring_nf
      _ ≤ ‖μ 0 f‖ + ‖μ n f - μ 0 f‖ := norm_add_le _ _
      _ ≤ ‖μ 0 f‖ + dist (μ n f) (μ 0 f) := by rw [dist_eq_norm]
      _ ≤ ‖μ 0 f‖ + R := by linarith [hR n 0]
      _ ≤ ↑⌈‖μ 0 f‖ + R⌉₊ := Nat.le_ceil _
  have A_union : ⋃ k, A k = Set.univ := by
    ext f; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact A_cover f

  obtain ⟨k, hk_int⟩ : ∃ k, (interior (A k)).Nonempty :=
    nonempty_interior_of_iUnion_of_closed A_closed A_union
  obtain ⟨g, hg⟩ := hk_int
  have hg_nhds : A k ∈ nhds g :=
    mem_nhds_iff.mpr ⟨interior (A k), interior_subset, isOpen_interior, hg⟩

  rw [UniformSpace.mem_nhds_iff] at hg_nhds
  obtain ⟨E, hE_mem, hE_sub⟩ := hg_nhds
  rw [ContinuousMap.mem_compactConvergence_entourage_iff] at hE_mem
  obtain ⟨K, V, hK, hV, hKV⟩ := hE_mem

  refine ⟨K, hK, fun n f hfK => ?_⟩
  by_contra hne


  have hmem : ∀ c : ℂ, ∀ m, ‖μ m (g + c • f)‖ ≤ ↑k := by
    intro c
    suffices g + c • f ∈ A k from this
    apply hE_sub
    apply hKV
    intro x hx
    simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply]
    rw [hfK x hx, smul_zero, add_zero]
    exact refl_mem_uniformity hV

  have hbound : ∀ (c : ℂ), ‖(μ n) g + c * (μ n) f‖ ≤ ↑k := by
    intro c
    have h := hmem c n
    rw [map_add, map_smul, smul_eq_mul] at h
    exact h

  set a := (μ n) g
  set b := (μ n) f
  have hb_ne : b ≠ 0 := hne
  have hscale : ∀ (t : ℕ), ‖a + ↑t‖ ≤ ↑k := by
    intro t
    have h := hbound (↑t / b)
    rwa [div_mul_cancel₀ _ hb_ne] at h

  set t := k + ⌈‖a‖⌉₊ + 1
  have h1 := hscale t

  have h2 : (↑t : ℝ) - ‖a‖ ≤ ‖a + (↑t : ℂ)‖ := by
    have h : ‖(↑t : ℂ)‖ ≤ ‖a‖ + ‖a + (↑t : ℂ)‖ := by
      calc ‖(↑t : ℂ)‖ = ‖-a + (a + ↑t)‖ := by ring_nf
        _ ≤ ‖-a‖ + ‖a + ↑t‖ := norm_add_le _ _
        _ = ‖a‖ + ‖a + ↑t‖ := by rw [norm_neg]
    rw [Complex.norm_natCast] at h
    linarith

  have h3 : (k : ℝ) < ↑t - ‖a‖ := by
    have h_ceil : ‖a‖ ≤ ↑⌈‖a‖⌉₊ := Nat.le_ceil ‖a‖
    show (k : ℝ) < ↑(k + ⌈‖a‖⌉₊ + 1) - ‖a‖
    push_cast
    linarith
  linarith

end ConcreteMeasSupp

namespace Meas

end Meas

namespace ConcreteMeasSupp

variable {X : Type*} [TopologicalSpace X]

theorem pointwiseLimitOfCLM_continuous
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ))
    (g : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hlim : ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (g f))) :
    Continuous g := by

  have htendsto : Tendsto (fun n (f : C(X, ℂ)) => μ n f) atTop (nhds (fun f => g f)) := by
    rw [tendsto_pi_nhds]
    exact hlim


  exact (continuousLinearMapOfTendsto μ htendsto).cont

theorem weakStarCauchyLimit_exists
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ))
    (_hcauchy : IsWeakStarCauchy μ)
    (_hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c)) :
    ∃ (μ₀ : C(X, ℂ) →L[ℂ] ℂ), TendstoWeakStar μ μ₀ := by

  let limfun : C(X, ℂ) → ℂ := fun f => (_hlim f).choose
  have hlim_spec : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (limfun f)) :=
    fun f => (_hlim f).choose_spec

  have htendsto_pi : Tendsto (fun n => (fun f => μ n f)) atTop (𝓝 limfun) := by
    rw [tendsto_pi_nhds]
    exact hlim_spec

  let g : C(X, ℂ) →ₗ[ℂ] ℂ :=
    linearMapOfTendsto limfun (fun n => (μ n).toLinearMap) htendsto_pi

  have hg_eq : ∀ f, g f = limfun f := fun f => by
    simp [g, linearMapOfTendsto]

  have hg_lim : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (g f)) := by
    intro f; rw [hg_eq]; exact hlim_spec f
  have hcont : Continuous g := pointwiseLimitOfCLM_continuous μ g hg_lim

  let μ₀ : C(X, ℂ) →L[ℂ] ℂ := ⟨g, hcont⟩

  exact ⟨μ₀, fun f => by exact hg_lim f⟩

theorem seqComplete
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (hcauchy : IsWeakStarCauchy μ) :
    ∃ (K : Set X) (μ₀ : C(X, ℂ) →L[ℂ] ℂ), IsCompact K ∧
      IsSupportedIn μ₀ K ∧ TendstoWeakStar μ μ₀ := by

  obtain ⟨K, hK, hsupp⟩ := cauchySeq_supportedIn_compact μ hcauchy

  have hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c) := by
    intro f
    exact ⟨_, (hcauchy f).tendsto_limUnder⟩

  obtain ⟨μ₀, hμ₀_eq⟩ := weakStarCauchyLimit_exists μ hcauchy hlim

  refine ⟨K, μ₀, hK, ?_, ?_⟩

  · intro f hf
    have : ∀ n, μ n f = 0 := fun n => hsupp n f hf
    have htend : Tendsto (fun n => μ n f) atTop (nhds (μ₀ f)) := hμ₀_eq f
    have htend0 : Tendsto (fun n => μ n f) atTop (nhds 0) := by
      simp [this]
    exact tendsto_nhds_unique htend htend0

  · exact hμ₀_eq

def functionalSupport (μ : C(X, ℂ) →L[ℂ] ℂ) : Set X :=
  {x : X | ∀ U ∈ nhds x, ∃ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) ∧ μ g ≠ 0}

lemma isClosed_functionalSupport (μ : C(X, ℂ) →L[ℂ] ℂ) :
    IsClosed (functionalSupport μ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU_nhds, hU_prop⟩ := hx
  push Not at hU_prop


  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU_nhds
  apply mem_nhds_iff.mpr
  refine ⟨V, ?_, hVopen, hxV⟩
  intro y hyV
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall]
  exact ⟨U, mem_nhds_iff.mpr ⟨V, hVU, hVopen, hyV⟩,
    by push Not; exact hU_prop⟩

theorem not_in_support_local_vanishing
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (x : X) (hx : x ∉ functionalSupport μ) :
    ∃ U ∈ nhds x, ∀ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) → μ g = 0 := by
  simp only [functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU, hprop⟩ := hx
  push Not at hprop
  exact ⟨U, hU, hprop⟩


noncomputable def toComplexCM : C(ℝ, ℂ) := ⟨Complex.ofReal, Complex.continuous_ofReal⟩


theorem pou_kills_functional
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (f : C(X, ℂ))
    (g : ℕ → C(X, ℂ))
    (hlf : LocallyFinite (fun n => Function.support (⇑(g n))))
    (hpw : ∀ x, HasSum (fun n => g n x) (f x))
    (hzero : ∀ n, μ (g n) = 0) :
    μ f = 0 := by

  have hsum : HasSum g f := by
    rw [HasSum]
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    intro u hu x
    obtain ⟨t, ht_nhd, ht_fin⟩ := hlf x
    refine ⟨t, ht_nhd, ?_⟩
    simp only [SummationFilter.unconditional, Filter.eventually_atTop]
    use ht_fin.toFinset
    intro s hs y hy
    have hvan : ∀ n ∉ ht_fin.toFinset, (g n) y = 0 := by
      intro n hn
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
      have : y ∉ Function.support (⇑(g n)) := by
        intro hy_supp
        exact hn ⟨y, Set.mem_inter hy_supp hy⟩
      exact Function.notMem_support.mp this
    suffices h : (∑ n ∈ s, g n) y = f y by
      rw [h]; exact refl_mem_uniformity hu
    simp only [ContinuousMap.sum_apply]
    have h1 : ∑ n ∈ s, (g n) y = ∑ n ∈ ht_fin.toFinset, (g n) y :=
      (Finset.sum_subset hs (fun n _ hn' => hvan n hn')).symm
    rw [h1]
    exact (hasSum_sum_of_ne_finset_zero (fun n hn => hvan n hn)).unique (hpw y)

  have hμsum : HasSum (fun n => μ (g n)) (μ f) := μ.hasSum hsum

  have hμzero : HasSum (fun _ : ℕ => (0 : ℂ)) (μ f) := by
    convert hμsum using 1; ext n; exact (hzero n).symm

  exact hμzero.unique hasSum_zero




end ConcreteMeasSupp

end
