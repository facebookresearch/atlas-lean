/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

noncomputable section

open scoped TensorProduct
open Filter Topology Classical

class CompactlySupportedMeasureSpace
    (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX] where
  dirac : X → MX
  evalPairing : MX →ₗ[ℂ] C(X, ℂ) →ₗ[ℂ] ℂ
  evalPairing_dirac : ∀ (x : X) (f : C(X, ℂ)), evalPairing (dirac x) f = f x
  evalPairing_continuous : ∀ (f : C(X, ℂ)), Continuous (fun μ : MX => evalPairing μ f)
  hasCompactSupport : ∀ (μ : MX), ∃ (K : Set X), IsCompact K ∧
    ∀ (f : C(X, ℂ)), (∀ x ∈ K, f x = 0) → evalPairing μ f = 0
  topology_eq_initial : ∀ (μ : MX), 𝓝 μ = ⨅ (f : C(X, ℂ)),
    Filter.comap (fun ν => evalPairing ν f) (𝓝 (evalPairing μ f))

lemma linear_func_decomp_pi_abstract {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : (ι → ℂ) →ₗ[ℂ] ℂ) (w : ι → ℂ) :
    l w = ∑ i : ι, l (Function.update 0 i 1) * w i := by
  conv_lhs => rw [show w = ∑ i : ι, w i • Function.update (0 : ι → ℂ) i 1 from by
    ext j; simp [Finset.sum_apply, Function.update, Finset.mem_univ]]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

lemma evalPairing_linearCombination_dirac
    {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [inst : CompactlySupportedMeasureSpace X MX]
    (c : X →₀ ℂ) (f : C(X, ℂ)) :
    inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f =
      c.sum (fun x a => a * f x) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, inst.evalPairing_dirac]

lemma abstract_match_on_finset_restricted
    {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [inst : CompactlySupportedMeasureSpace X MX]
    (μ : MX) (K : Set X)
    (hK : ∀ (f : C(X, ℂ)), (∀ x ∈ K, f x = 0) → inst.evalPairing μ f = 0)
    (I : Finset (C(X, ℂ))) :
    ∃ c : X →₀ ℂ, (c.support : Set X) ⊆ K ∧
      ∀ f ∈ I, inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f =
                inst.evalPairing μ f := by
  let ι := (I : Set (C(X, ℂ))).Elem
  let φ : K → (ι → ℂ) := fun x i => (i : C(X, ℂ)) x.1
  let v : ι → ℂ := fun i => inst.evalPairing μ (i : C(X, ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : K, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))
    have key_zero : ∀ x' ∈ K,
        ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : C(X, ℂ)) x') = 0 := by
      intro x' hx'
      rw [← linear_func_decomp_pi_abstract l (φ ⟨x', hx'⟩)]
      exact hl_φ ⟨x', hx'⟩
    have g_zero_on_K : ∀ x' ∈ K,
        (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) x' = 0 := by
      intro x' hx'
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact key_zero x' hx'
    apply hl_v; rw [linear_func_decomp_pi_abstract l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * inst.evalPairing μ (↑i : C(X, ℂ)) =
           inst.evalPairing μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    exact hK _ g_zero_on_K
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c_sub, hc_sub⟩ := h_span
  let c : X →₀ ℂ := c_sub.mapDomain Subtype.val
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    have h1 := Finsupp.mapDomain_support (f := Subtype.val) (s := c_sub)
    have h2 : x ∈ Finset.image Subtype.val c_sub.support := h1 hx
    rw [Finset.mem_image] at h2
    obtain ⟨k, _, rfl⟩ := h2
    exact k.2
  · intro f hf
    rw [evalPairing_linearCombination_dirac]
    have hci : (c_sub.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc_sub]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsum : (Finsupp.mapDomain Subtype.val c_sub).sum (fun x a => a * f x) =
        c_sub.sum (fun k a => a * f k.1) :=
      Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)
    simp only [Finsupp.sum] at hsum ⊢
    rw [hsum]
    exact hci

theorem CompactlySupportedMeasureSpace.supported_in_compact
    {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [inst : CompactlySupportedMeasureSpace X MX]
    (μ : MX) : ∃ K : Set X, IsCompact K ∧
    μ ∈ closure ((Finsupp.linearCombination ℂ
      (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))) ''
      { f : X →₀ ℂ | (f.support : Set X) ⊆ K }) := by
  obtain ⟨K, hKc, hK⟩ := inst.hasCompactSupport μ
  refine ⟨K, hKc, ?_⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [inst.topology_eq_initial] at hU
  rw [Filter.mem_iInf] at hU
  obtain ⟨J_set, hJ_finite, V, hV_mem, hV_eq⟩ := hU
  let J : Finset (C(X, ℂ)) := hJ_finite.toFinset
  obtain ⟨c, hc_supp, hc_match⟩ := abstract_match_on_finset_restricted μ K hK J
  refine ⟨Finsupp.linearCombination ℂ inst.dirac c, ?_, ⟨c, hc_supp, rfl⟩⟩
  rw [hV_eq]
  simp only [Set.mem_iInter]
  intro ⟨f, hf⟩
  have hVf := hV_mem ⟨f, hf⟩
  rw [Filter.mem_comap] at hVf
  obtain ⟨W, hW_nhds, hW_sub⟩ := hVf
  apply hW_sub
  show inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f ∈ W
  have heq : inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f =
             inst.evalPairing μ f :=
    hc_match f (hJ_finite.mem_toFinset.mpr hf)
  rw [heq]
  exact mem_of_mem_nhds hW_nhds


def CompactlySupportedMeasureSpace.embed (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] :
    (X →₀ ℂ) →ₗ[ℂ] MX :=
  Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))

def concreteDirac (X : Type*) [TopologicalSpace X] (x : X) : WeakDual ℂ C(X, ℂ) :=
  ContinuousMap.evalCLM ℂ x

def concreteDiracEmbed (X : Type*) [TopologicalSpace X] :
    (X →₀ ℂ) →ₗ[ℂ] WeakDual ℂ C(X, ℂ) :=
  Finsupp.linearCombination ℂ (concreteDirac X)


lemma linear_func_decomp_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : (ι → ℂ) →ₗ[ℂ] ℂ) (w : ι → ℂ) :
    l w = ∑ i : ι, l (Function.update 0 i 1) * w i := by
  conv_lhs => rw [show w = ∑ i : ι, w i • Function.update (0 : ι → ℂ) i 1 from by
    ext j; simp [Finset.sum_apply, Function.update, Finset.mem_univ]]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

lemma concreteDiracEmbed_apply_sum
    (X : Type*) [TopologicalSpace X] (c : X →₀ ℂ) (f : C(X, ℂ)) :
    (concreteDiracEmbed X c) f = ∑ x ∈ c.support, c x * f x := by
  simp only [concreteDiracEmbed, Finsupp.linearCombination_apply, Finsupp.sum]
  show (∑ x ∈ c.support, c x • concreteDirac X x : C(X, ℂ) →L[ℂ] ℂ) f = _
  rw [ContinuousLinearMap.sum_apply]; congr 1

lemma concreteDiracEmbed_match_on_finset
    (X : Type*) [TopologicalSpace X]
    (μ : WeakDual ℂ C(X, ℂ)) (I : Finset (C(X, ℂ))) :
    ∃ c : X →₀ ℂ, ∀ f ∈ I, (concreteDiracEmbed X c) f = μ f := by
  let ι := (I : Set (C(X, ℂ))).Elem
  let φ : X → (ι → ℂ) := fun x i => (i : C(X, ℂ)) x
  let v : ι → ℂ := fun i => μ (i : C(X, ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : X, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))
    have key_zero : ∀ x' : X,
        ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : C(X, ℂ)) x') = 0 := by
      intro x'; rw [← linear_func_decomp_pi l (φ x')]; exact hl_φ x'
    have g_zero : (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) = 0 := by
      ext x'; simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, ContinuousMap.zero_apply]; exact key_zero x'
    apply hl_v; rw [linear_func_decomp_pi l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * μ (↑i : C(X, ℂ)) =
           μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this, g_zero, map_zero]
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c, hc⟩ := h_span; use c; intro f hf
  have hci : (c.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci
  rw [concreteDiracEmbed_apply_sum]; exact hci

lemma concreteDiracEmbed_match_on_finset_restricted
    (X : Type*) [TopologicalSpace X]
    (μ : WeakDual ℂ C(X, ℂ)) (K : Set X)
    (hK : ∀ (f : C(X, ℂ)), (∀ x ∈ K, f x = 0) → μ f = 0)
    (I : Finset (C(X, ℂ))) :
    ∃ c : X →₀ ℂ, (c.support : Set X) ⊆ K ∧
      ∀ f ∈ I, (concreteDiracEmbed X c) f = μ f := by
  let ι := (I : Set (C(X, ℂ))).Elem
  let φ : K → (ι → ℂ) := fun x i => (i : C(X, ℂ)) x.1
  let v : ι → ℂ := fun i => μ (i : C(X, ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : K, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))

    have key_zero : ∀ x' ∈ K,
        ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : C(X, ℂ)) x') = 0 := by
      intro x' hx'
      rw [← linear_func_decomp_pi l (φ ⟨x', hx'⟩)]
      exact hl_φ ⟨x', hx'⟩
    have g_zero_on_K : ∀ x' ∈ K,
        (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) x' = 0 := by
      intro x' hx'
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact key_zero x' hx'
    apply hl_v; rw [linear_func_decomp_pi l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * μ (↑i : C(X, ℂ)) =
           μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : C(X, ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    exact hK _ g_zero_on_K
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c_sub, hc_sub⟩ := h_span

  let c : X →₀ ℂ := c_sub.mapDomain Subtype.val
  refine ⟨c, ?_, ?_⟩
  ·
    intro x hx
    have h1 := Finsupp.mapDomain_support (f := Subtype.val) (s := c_sub)
    have h2 : x ∈ Finset.image Subtype.val c_sub.support := h1 hx
    rw [Finset.mem_image] at h2
    obtain ⟨k, _, rfl⟩ := h2
    exact k.2
  ·
    intro f hf
    rw [concreteDiracEmbed_apply_sum]
    have hci : (c_sub.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc_sub]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci


    have hsum : (Finsupp.mapDomain Subtype.val c_sub).sum (fun x a => a * f x) =
        c_sub.sum (fun k a => a * f k.1) :=
      Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)
    simp only [Finsupp.sum] at hsum ⊢
    rw [hsum]
    exact hci

theorem concreteDiracEmbed_range_dense_ax
    (X : Type*) [TopologicalSpace X]
    (μ : WeakDual ℂ C(X, ℂ)) :
    μ ∈ closure (Set.range (concreteDiracEmbed X)) := by
  rw [mem_closure_iff_nhds]
  intro U hU

  have hnhds : @nhds (WeakDual ℂ C(X, ℂ)) _ μ =
      Filter.comap (fun (ν : WeakDual ℂ C(X, ℂ)) (f : C(X, ℂ)) =>
        (topDualPairing ℂ C(X, ℂ)) ν f)
        (nhds (fun f => (topDualPairing ℂ C(X, ℂ)) μ f)) :=
    nhds_induced _ μ
  rw [hnhds] at hU
  rw [Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU

  rw [nhds_pi] at hV
  rw [Filter.mem_pi'] at hV
  obtain ⟨J, t, ht, htV⟩ := hV

  obtain ⟨c, hc⟩ := concreteDiracEmbed_match_on_finset X μ J
  refine ⟨concreteDiracEmbed X c, ?_, ⟨c, rfl⟩⟩
  apply hVU; apply htV
  intro f hf
  dsimp only; simp only [topDualPairing_apply]
  have eq1 : (concreteDiracEmbed X c) f = μ f := hc f hf
  have htf : μ f ∈ t f := by
    have := ht f; simp only [topDualPairing_apply] at this; exact mem_of_mem_nhds this
  exact eq1 ▸ htf

theorem finitelySupportedMeasures_dense
    (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] :
    Dense (Set.range (concreteDiracEmbed X)) := by
  rw [dense_iff_closure_eq]
  ext x
  simp only [Set.mem_univ, iff_true]
  exact concreteDiracEmbed_range_dense_ax X x

theorem lemma_3_4_dense_concrete
    (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] :
    Dense (Set.range (concreteDiracEmbed X)) :=
  finitelySupportedMeasures_dense X




def boxtimesAtomic (X Y : Type*) :
    (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ) →ₗ[ℂ] (X × Y →₀ ℂ) :=
  (TensorProduct.mk ℂ (X →₀ ℂ) (Y →₀ ℂ)).compr₂
    (finsuppTensorFinsupp' ℂ X Y).toLinearMap

theorem boxtimesAtomic_single_single (X Y : Type*) (x : X) (y : Y) (a b : ℂ) :
    boxtimesAtomic X Y (Finsupp.single x a) (Finsupp.single y b) =
    Finsupp.single (x, y) (a * b) := by
  simp [boxtimesAtomic, LinearMap.compr₂, finsuppTensorFinsupp']

section Cor35

variable (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X]
variable (Y : Type*) [TopologicalSpace Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [T2Space Y]

def boxtimesAtomicToMeas :
    (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ) →ₗ[ℂ] WeakDual ℂ C(X × Y, ℂ) :=
  (boxtimesAtomic X Y).compr₂ (concreteDiracEmbed (X × Y))

section BLTExtension

variable {D₁ : Type*} [AddCommGroup D₁] [Module ℂ D₁]
variable {D₂ : Type*} [AddCommGroup D₂] [Module ℂ D₂]
variable {M₁ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [TopologicalSpace M₁]
variable {M₂ : Type*} [AddCommGroup M₂] [Module ℂ M₂] [TopologicalSpace M₂]
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]






end BLTExtension


theorem boxtimes_extension_unique
    (bt₁ bt₂ : WeakDual ℂ C(X, ℂ) →ₗ[ℂ] WeakDual ℂ C(Y, ℂ) →ₗ[ℂ] WeakDual ℂ C(X × Y, ℂ))
    (hext₁ : ∀ (μ : X →₀ ℂ) (ν : Y →₀ ℂ),
      bt₁ (concreteDiracEmbed X μ) (concreteDiracEmbed Y ν) =
      concreteDiracEmbed (X × Y) (boxtimesAtomic X Y μ ν))
    (hext₂ : ∀ (μ : X →₀ ℂ) (ν : Y →₀ ℂ),
      bt₂ (concreteDiracEmbed X μ) (concreteDiracEmbed Y ν) =
      concreteDiracEmbed (X × Y) (boxtimesAtomic X Y μ ν))
    (hcont₁_l : ∀ (ν : WeakDual ℂ C(Y, ℂ)), Continuous (fun μ => bt₁ μ ν))
    (hcont₁_r : ∀ (μ : WeakDual ℂ C(X, ℂ)), Continuous (fun ν => bt₁ μ ν))
    (hcont₂_l : ∀ (ν : WeakDual ℂ C(Y, ℂ)), Continuous (fun μ => bt₂ μ ν))
    (hcont₂_r : ∀ (μ : WeakDual ℂ C(X, ℂ)), Continuous (fun ν => bt₂ μ ν)) :
    bt₁ = bt₂ := by
  ext μ ν
  have step1 : ∀ (ν₀ : Y →₀ ℂ) (μ : WeakDual ℂ C(X, ℂ)),
      bt₁ μ (concreteDiracEmbed Y ν₀) = bt₂ μ (concreteDiracEmbed Y ν₀) := by
    intro ν₀
    have heq : Set.EqOn
        (fun μ => bt₁ μ (concreteDiracEmbed Y ν₀))
        (fun μ => bt₂ μ (concreteDiracEmbed Y ν₀))
        (Set.range (concreteDiracEmbed X)) := by
      rintro _ ⟨μ₀, rfl⟩
      dsimp only
      rw [hext₁ μ₀ ν₀, hext₂ μ₀ ν₀]
    exact fun μ => congr_fun (Continuous.ext_on
      (lemma_3_4_dense_concrete X)
      (hcont₁_l _) (hcont₂_l _) heq) μ
  have heq : Set.EqOn
      (fun ν => bt₁ μ ν)
      (fun ν => bt₂ μ ν)
      (Set.range (concreteDiracEmbed Y)) := by
    rintro _ ⟨ν₀, rfl⟩
    dsimp only
    exact step1 ν₀ μ
  exact congr_fun (Continuous.ext_on
    (lemma_3_4_dense_concrete Y)
    (hcont₁_r μ) (hcont₂_r μ) heq) ν


end Cor35
