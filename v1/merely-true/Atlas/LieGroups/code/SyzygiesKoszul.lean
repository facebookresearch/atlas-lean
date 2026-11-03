/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

def IsRegularSequence {A : Type*} [CommRing A] {m : ℕ} (f : Fin m → A) : Prop :=
  (∀ (j : Fin m),
    ∀ (r : A ⧸ Ideal.span (Set.image f {i | (i : ℕ) < j})),
      r ≠ 0 →
        (Ideal.Quotient.mk (Ideal.span (Set.image f {i | (i : ℕ) < j})) (f j)) • r ≠ 0) ∧
  Nontrivial (A ⧸ Ideal.span (Set.range f))

structure IsGradedSModule {k S M : Type*} [CommRing k] [Ring S] [Algebra k S]
    [AddCommGroup M] [Module S M] [Module k M] [IsScalarTower k S M]
    (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k M) : Prop where
  internal : DirectSum.IsInternal ℳ
  smul_mem : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j)

def IsConnectedGrading (k : Type*) (S : Type*) [CommRing k] [Ring S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Prop :=
  𝒮 0 = (Algebra.linearMap k S).range

def augmentationIdealGraded {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Ideal S :=
  Ideal.span (⋃ (i : ℕ) (_ : 0 < i), ↑(𝒮 i))

lemma isHomogeneous_augmentationIdealGraded {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] :
    Ideal.IsHomogeneous 𝒮 (augmentationIdealGraded 𝒮) := by
  unfold augmentationIdealGraded
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, _, hxi⟩ := hx
  exact ⟨i, hxi⟩

lemma augmentationIdealGraded_component_mem {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮]
    (r : S) (hr : r ∈ augmentationIdealGraded 𝒮) (j : ℕ) :
    ((DirectSum.decompose 𝒮 r) j : S) ∈ augmentationIdealGraded 𝒮 :=
  ((isHomogeneous_augmentationIdealGraded 𝒮).mem_iff.mp hr) j

def hilbertSeries {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (ℳ : ℕ → Submodule k M) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => (Module.finrank k (ℳ i) : ℤ))

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

def augmentation_ideal_poly : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))

lemma homog_in_aug_smul
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (d : ℕ) (x : M) (hxd : x ∈ ℳ d)
    (hxP : x ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) :
    x ∈ Submodule.span k'
      (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
        Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M)) := by
  classical
  haveI : DirectSum.Decomposition ℳ := hgr.internal.chooseDecomposition
  set target := Submodule.span k'
    (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
      Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M)) with htarget_def

  have hx_eq : (↑((DirectSum.decompose ℳ x) d) : M) = x :=
    DirectSum.decompose_of_mem_same ℳ hxd
  rw [← hx_eq]

  clear hxd hx_eq

  refine Submodule.smul_induction_on hxP ?_ ?_
  ·
    intro r hr n _

    suffices key : ∀ (r : S), r ∈ augmentationIdealGraded 𝒮 → ∀ (n : M),
        (↑((DirectSum.decompose ℳ (r • n)) d) : M) ∈ target from key r hr n
    intro r hr
    induction hr using Submodule.span_induction with
    | mem s hs =>

      intro n
      simp only [Set.mem_iUnion] at hs
      obtain ⟨j, hj, hs_j⟩ := hs

      rw [(DirectSum.sum_support_decompose ℳ n).symm, Finset.smul_sum,
        DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finset_sum]
      apply Submodule.sum_mem; intro i _

      have hni_mem := SetLike.coe_mem ((DirectSum.decompose ℳ n) i)
      have hsmul : s • (↑((DirectSum.decompose ℳ n) i) : M) ∈ ℳ (i + j) :=
        hgr.smul_mem i j s _ hs_j hni_mem

      by_cases he : d = i + j
      ·
        subst he; rw [DirectSum.decompose_of_mem_same ℳ hsmul]
        apply Submodule.subset_span

        simp only [Set.mem_iUnion]
        exact ⟨j, hj, i, rfl, Set.mem_image2_of_mem hs_j (SetLike.coe_mem _)⟩
      ·
        rw [DirectSum.decompose_of_mem_ne ℳ hsmul (Ne.symm he)]; exact target.zero_mem
    | zero =>
      intro n
      simp only [zero_smul, DirectSum.decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero]
      exact target.zero_mem
    | add _ _ _ _ ih₁ ih₂ =>
      intro n
      rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      exact target.add_mem (ih₁ n) (ih₂ n)
    | smul a _ _ ih =>
      intro n
      change (↑((DirectSum.decompose ℳ ((a * _) • n)) d) : M) ∈ target
      rw [mul_comm, mul_smul]; exact ih (a • n)

  ·
    intro x y hx hy
    rw [DirectSum.decompose_add]
    simp only [DirectSum.add_apply, AddMemClass.coe_add]
    exact target.add_mem hx hy

lemma exists_homogeneous_span_quotient
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfin : FiniteDimensional k' (M ⧸ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M))) :
    ∃ (T : Finset M),
      (∀ t ∈ T, ∃ d, t ∈ ℳ d) ∧
      Submodule.span k' (((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤ := by
  classical
  set P := (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)
  set H : Set M := ⋃ d, ↑(ℳ d)
  have hH_span : Submodule.span k' H = ⊤ := by
    rw [show H = ⋃ d, ↑(ℳ d) from rfl, ← Submodule.iSup_eq_span]
    exact hgr.internal.submodule_iSup_eq_top
  set f := P.mkQ.restrictScalars k'
  have hf_surj : Function.Surjective f := Submodule.mkQ_surjective P
  obtain ⟨S₀, hS₀⟩ := (Module.finite_def.mp (inferInstance) : (⊤ : Submodule k' (M ⧸ P)).FG)
  have hS₀_lift : ∀ q ∈ S₀, ∃ (Tq : Finset M), ↑Tq ⊆ H ∧ q ∈ Submodule.span k' (f '' ↑Tq) := by
    intro q _
    obtain ⟨m, hm⟩ := hf_surj q
    have hm_in : m ∈ Submodule.span k' H := hH_span ▸ Submodule.mem_top
    obtain ⟨Tm, hTm_sub, hm_mem⟩ := Submodule.mem_span_finite_of_mem_span hm_in
    exact ⟨Tm, hTm_sub, by rw [← hm, Submodule.span_image]; exact Submodule.mem_map_of_mem hm_mem⟩
  choose Tq hTq_sub hTq_mem using hS₀_lift
  set T := S₀.attach.biUnion (fun ⟨q, hq⟩ => Tq q hq)
  refine ⟨T, ?_, ?_⟩
  ·
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨⟨q, hq⟩, _, ht'⟩ := ht
    have : (t : M) ∈ H := hTq_sub q hq (Finset.mem_coe.mpr ht')
    rw [Set.mem_iUnion] at this
    exact this
  ·
    rw [eq_top_iff, ← hS₀]
    apply Submodule.span_le.mpr
    intro q hq
    have hq' : q ∈ S₀ := hq
    have hTq_sub_T : (Tq q hq' : Set M) ⊆ (T : Set M) := by
      intro m hm
      show m ∈ T
      rw [Finset.mem_biUnion]
      exact ⟨⟨q, hq'⟩, Finset.mem_attach _ _, hm⟩
    have himg_sub : f '' ↑(Tq q hq') ⊆ (P.mkQ : M →ₗ[S] M ⧸ P) '' ↑T := by
      intro x ⟨m, hm, hmx⟩
      exact ⟨m, hTq_sub_T hm, hmx⟩
    exact Submodule.span_mono himg_sub (hTq_mem q hq')


lemma homog_smul_component_mem_aug
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    [DirectSum.Decomposition ℳ]
    (d j : ℕ) (rj : S) (hrj_homog : rj ∈ 𝒮 j)
    (hrj_aug : rj ∈ augmentationIdealGraded 𝒮) (n : M) :
    ((DirectSum.decompose ℳ (rj • n)) d : M) ∈
      (augmentationIdealGraded 𝒮 : Ideal S) • (⊤ : Submodule S M) := by
  classical
  have h_eq : ((DirectSum.decompose ℳ (rj • n)) d : M) =
      ∑ i ∈ (DirectSum.decompose ℳ n).support,
        ((DirectSum.decompose ℳ (rj • ((DirectSum.decompose ℳ n) i : M))) d : M) := by
    conv_lhs => rw [show rj • n = ∑ i ∈ (DirectSum.decompose ℳ n).support,
        rj • ((DirectSum.decompose ℳ n) i : M) from by
      conv_lhs => rw [← DirectSum.sum_support_decompose ℳ n]; rw [Finset.smul_sum]]
    rw [DirectSum.decompose_sum]; simp
  rw [h_eq]
  apply Submodule.sum_mem
  intro i _
  have h_mem_grade := hgr.smul_mem i j rj _ hrj_homog ((DirectSum.decompose ℳ n) i).2
  by_cases h : i + j = d
  · rw [← h, DirectSum.decompose_of_mem_same ℳ h_mem_grade]
    exact Submodule.smul_mem_smul hrj_aug Submodule.mem_top
  · rw [DirectSum.decompose_of_mem_ne ℳ h_mem_grade h]; exact Submodule.zero_mem _

lemma aug_smul_graded_component
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    [DirectSum.Decomposition ℳ]
    (d : ℕ) (z : M) (hz : z ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) :
    (↑((DirectSum.decompose ℳ z) d) : M) ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) := by
  classical
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr n _hn
    have h_eq_r : ((DirectSum.decompose ℳ (r • n)) d : M) =
        ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
          ((DirectSum.decompose ℳ (((DirectSum.decompose 𝒮 r) j : S) • n)) d : M) := by
      conv_lhs => rw [show r • n = ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
          ((DirectSum.decompose 𝒮 r) j : S) • n from by
        conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 r]; rw [Finset.sum_smul]]
      rw [DirectSum.decompose_sum]; simp
    rw [h_eq_r]
    apply Submodule.sum_mem
    intro j _
    have hrj_aug : ((DirectSum.decompose 𝒮 r) j : S) ∈ augmentationIdealGraded 𝒮 :=
      augmentationIdealGraded_component_mem 𝒮 r hr j

    exact homog_smul_component_mem_aug 𝒮 ℳ hgr d j _
      ((DirectSum.decompose 𝒮 r) j).2 hrj_aug n

  · intro x y hx hy
    have h_add : (↑((DirectSum.decompose ℳ (x + y)) d) : M) =
        (↑((DirectSum.decompose ℳ x) d) : M) + (↑((DirectSum.decompose ℳ y) d) : M) := by
      simp [DirectSum.decompose_add]
    rw [h_add]
    exact Submodule.add_mem _ hx hy

lemma decompose_mod_P
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (T : Finset M) (hThom : ∀ t ∈ T, ∃ d, t ∈ ℳ d)
    (hTspan : Submodule.span k' (((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤)
    (d : ℕ) (m : M) (hm : m ∈ ℳ d) :
    ∃ (v : M), v ∈ Submodule.span k' (↑T ∩ (ℳ d : Set M)) ∧
      (m - v) ∈ ℳ d ∧
      (m - v) ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) := by
  classical
  set P := (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) with hP_def
  haveI : DirectSum.Decomposition ℳ := hgr.internal.chooseDecomposition

  have hm_quot : P.mkQ m ∈ Submodule.span k' ((P.mkQ.restrictScalars k') '' ↑T) := by
    change P.mkQ m ∈ Submodule.span k' (P.mkQ '' ↑T)
    rw [hTspan]; exact Submodule.mem_top
  rw [Submodule.span_image, Submodule.mem_map] at hm_quot
  obtain ⟨y, hy, hym⟩ := hm_quot
  rw [Submodule.mem_span_finset] at hy
  obtain ⟨c, _, hc⟩ := hy

  have hsum_in_P : m - ∑ t ∈ T, c t • t ∈ P := by
    have key : P.mkQ (m - ∑ t ∈ T, c t • t) = 0 := by
      simp only [map_sub, map_sum]
      rw [show P.mkQ m = (P.mkQ.restrictScalars k') y from hym.symm, ← hc, map_sum, sub_eq_zero]
      apply Finset.sum_congr rfl
      intro t _; exact ((P.mkQ.restrictScalars k').map_smul (c t) t).symm
    rwa [P.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key

  set v := ∑ t ∈ T.filter (fun t => t ∈ ℳ d), c t • t with hv_def
  refine ⟨v, ?_, ?_, ?_⟩
  ·
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Finset.mem_coe.mpr ht.1, ht.2⟩)
  ·
    apply (ℳ d).sub_mem hm
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact (ℳ d).smul_mem _ ht.2
  ·


    set z := m - ∑ t ∈ T, c t • t with hz_def
    have hmv_d : m - v ∈ ℳ d := (ℳ d).sub_mem hm (by
      apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
      exact (ℳ d).smul_mem _ ht.2)

    suffices h_decomp : (↑((DirectSum.decompose ℳ z) d) : M) = m - v by
      rw [← h_decomp]
      exact aug_smul_graded_component 𝒮 ℳ hgr d z hsum_in_P

    set w := ∑ t ∈ T.filter (fun t => t ∉ ℳ d), c t • t with hw_def
    have hz_split : z = (m - v) - w := by
      simp only [z, v, w, sub_sub]

      congr 1
      rw [← Finset.sum_union (s₁ := T.filter (· ∈ ℳ d)) (s₂ := T.filter (· ∉ ℳ d))]
      · congr 1; ext x; simp [Finset.mem_filter, Finset.mem_union]; tauto
      · exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => h2 h1)

    conv_lhs => rw [hz_split]
    rw [show DirectSum.decompose ℳ ((m - v) - w) =
        DirectSum.decompose ℳ (m - v) - DirectSum.decompose ℳ w from
      map_sub (DirectSum.decomposeAddEquiv ℳ) _ _]
    simp only [DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_same ℳ hmv_d]

    suffices hw0 : (↑((DirectSum.decompose ℳ w) d) : M) = 0 by rw [hw0, sub_zero]

    change (↑((DirectSum.decomposeAddEquiv ℳ w) d) : M) = 0
    rw [hw_def, map_sum (DirectSum.decomposeAddEquiv ℳ)]
    have key2 : (↑((∑ x ∈ T.filter (fun t => t ∉ ℳ d),
        (DirectSum.decomposeAddEquiv ℳ) (c x • x)) d) : M) =
        ↑(∑ x ∈ T.filter (fun t => t ∉ ℳ d),
          ((DirectSum.decomposeAddEquiv ℳ) (c x • x)) d : ↥(ℳ d)) := by
      congr 1; exact DFinsupp.finset_sum_apply _ _ _
    rw [key2, AddSubmonoidClass.coe_finset_sum]

    apply Finset.sum_eq_zero
    intro t ht; rw [Finset.mem_filter] at ht
    obtain ⟨hT, hnd⟩ := ht
    obtain ⟨e, he⟩ := hThom t hT
    have hne : e ≠ d := fun heq => hnd (heq ▸ he)
    show (↑((DirectSum.decomposeAddEquiv ℳ (c t • t)) d) : M) = 0
    change (↑((DirectSum.decompose ℳ (c t • t)) d) : M) = 0
    exact DirectSum.decompose_of_mem_ne ℳ ((ℳ e).smul_mem _ he) hne

theorem lemma_12_3_i_generators

    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfin : FiniteDimensional k' (M ⧸ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M))) :
    Module.Finite S M := by
  set P := ((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) with hP_def

  obtain ⟨T, hThom, hTspan⟩ := exists_homogeneous_span_quotient 𝒮 ℳ hgr hfin

  let N := Submodule.span S (T : Set M)

  suffices hN : N = ⊤ by
    rw [Module.finite_def]; exact ⟨T, hN⟩
  rw [eq_top_iff]


  suffices hall : ∀ d, ℳ d ≤ N.restrictScalars k' by
    intro m _
    have hint := hgr.internal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
    have hle : (⨆ d, ℳ d) ≤ N.restrictScalars k' := iSup_le hall
    rw [hint.2] at hle
    exact hle Submodule.mem_top

  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro m hm
    show m ∈ N

    obtain ⟨v, hv_span, hm_v_d, hm_v_P⟩ := decompose_mod_P 𝒮 ℳ hgr T hThom hTspan d m hm

    have hv_N : v ∈ N := by
      have h1 : Submodule.span k' (↑T ∩ (ℳ d : Set M)) ≤ Submodule.span k' (↑T : Set M) :=
        Submodule.span_mono Set.inter_subset_left
      have h2 : Submodule.span k' (↑T : Set M) ≤ N.restrictScalars k' :=
        Submodule.span_le_restrictScalars k' S (↑T : Set M)
      exact h2 (h1 hv_span)


    have hm_v_N : m - v ∈ N := by
      have hmem := homog_in_aug_smul 𝒮 ℳ hgr d (m - v) hm_v_d hm_v_P
      suffices m - v ∈ N.restrictScalars k' from this
      apply Submodule.span_le.mpr _ hmem
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_image2, SetLike.mem_coe] at hy
      obtain ⟨j, hj, i, hij, s, hs, m', hm', rfl⟩ := hy
      change s • m' ∈ N
      exact N.smul_mem s (ih i (by omega) hm')

    have : m = v + (m - v) := by abel
    rw [this]
    exact N.add_mem hv_N hm_v_N

theorem graded_nakayama
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (_hconn : IsConnectedGrading k' S 𝒮)
    {N : Type*} [AddCommGroup N] [Module S N] [Module k' N] [IsScalarTower k' S N]
    (𝒩 : ℕ → Submodule k' N) (hgr : IsGradedSModule 𝒮 𝒩)
    (hdeg0 : 𝒩 0 = ⊥)
    (hSN : ∀ (d : ℕ) (n : N), n ∈ 𝒩 d →
      n ∈ Submodule.span k'
        (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
          Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N))) :
    ∀ n : N, n = 0 := by

  have hall : ∀ d, 𝒩 d = ⊥ := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      cases d with
      | zero => exact hdeg0
      | succ d =>
        rw [Submodule.eq_bot_iff]
        intro n hn
        have hmem := hSN (d + 1) n hn

        have hset_zero : (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
            Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) ⊆ {(0 : N)} := by
          intro x hx
          simp only [Set.mem_iUnion, Set.mem_image2] at hx
          obtain ⟨j, hj, i, hij, s, hs, m, hm, rfl⟩ := hx
          have hi : i < d + 1 := by omega
          rw [ih i hi] at hm
          simp at hm
          simp [hm]

        have hspan_bot : Submodule.span k'
            (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
              Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) = ⊥ := by
          have : Submodule.span k' ({(0 : N)} : Set N) = ⊥ :=
            Submodule.span_singleton_eq_bot.mpr rfl
          exact le_antisymm (this ▸ Submodule.span_mono hset_zero) bot_le
        rw [hspan_bot] at hmem
        exact (Submodule.mem_bot k').mp hmem

  intro n
  have hint := hgr.internal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
  have htop := hint.2
  have hbot : ⨆ i, 𝒩 i = ⊥ := by simp [hall]
  rw [hbot] at htop
  exact (Submodule.mem_bot k').mp (htop ▸ Submodule.mem_top)




def quotientGrading {k' S : Type*} [CommRing k'] [CommRing S] [Algebra k' S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k' M) (i : ℕ) :
    Submodule k' (M ⧸ (augmentationIdealGraded 𝒮 • (⊤ : Submodule S M))) :=
  (ℳ i).map ((augmentationIdealGraded 𝒮 • (⊤ : Submodule S M)).mkQ.restrictScalars k')





attribute [local instance] MvPolynomial.gradedAlgebra

theorem mvpoly_connected_grading :
    @IsConnectedGrading k R _ _ _
      (homogeneousSubmodule (Fin n) k) MvPolynomial.gradedAlgebra := by
  show homogeneousSubmodule (Fin n) k 0 = (Algebra.linearMap k R).range
  ext p
  simp only [mem_homogeneousSubmodule, LinearMap.mem_range]
  constructor
  · intro hp
    refine ⟨coeff 0 p, ?_⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    ext d
    simp only [coeff_C]
    split_ifs with hd
    · exact hd ▸ rfl
    · symm
      exact hp.coeff_eq_zero (by
        intro h
        apply hd
        ext i
        have : Finsupp.degree d = 0 := h
        simp only [Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
        have hsum := Finset.sum_eq_zero_iff.mp this
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        by_cases hi : i ∈ d.support
        · exact (hsum i hi).symm
        · rw [Finsupp.mem_support_iff, not_not] at hi; exact hi.symm)
  · rintro ⟨c, rfl⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    exact isHomogeneous_C (Fin n) c

structure KoszulComplex (k : Type*) [Field k] (n : ℕ) where
  rank : (p : ℕ) → (hp : p ≤ n) → ℕ
  rank_eq : ∀ (p : ℕ) (hp : p ≤ n), rank p hp = Nat.choose n p
  differential : ∀ (p : ℕ) (hp : 0 < p) (hp' : p ≤ n),
    ((Fin (rank p hp') → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
     (Fin (rank (p - 1) (by omega)) → MvPolynomial (Fin n) k))
  d_squared_zero : ∀ (p : ℕ) (hp : 1 < p) (hp' : p ≤ n),
    (differential (p - 1) (by omega) (by omega)).comp
      (differential p (by omega) hp') = 0





attribute [local instance] MvPolynomial.gradedAlgebra

def freeModuleGrading (d : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ i, f i ∈ homogeneousSubmodule (Fin n) k d}
  zero_mem' i := (homogeneousSubmodule (Fin n) k d).zero_mem
  add_mem' ha hb i := (homogeneousSubmodule (Fin n) k d).add_mem (ha i) (hb i)
  smul_mem' c _ ha i := (homogeneousSubmodule (Fin n) k d).smul_mem c (ha i)

def twistedFreeModuleGrading {m : ℕ} (degrees : Fin m → ℕ) (p : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ j, f j ∈ homogeneousSubmodule (Fin n) k (p - degrees j)}
  zero_mem' j := (homogeneousSubmodule (Fin n) k (p - degrees j)).zero_mem
  add_mem' ha hb j := (homogeneousSubmodule (Fin n) k (p - degrees j)).add_mem (ha j) (hb j)
  smul_mem' c _ ha j := (homogeneousSubmodule (Fin n) k (p - degrees j)).smul_mem c (ha j)


lemma mem_finsuppAntidiag_iff_degree (d : ℕ) (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree f = d := by
  rw [Finset.mem_finsuppAntidiag]
  simp only [Finset.subset_univ, and_true]
  have key : (Finset.univ : Finset (Fin n)).sum f = Finsupp.degree f := by
    simp [Finsupp.degree]
    exact (Finsupp.sum_fintype f (fun _ => id) (fun _ => rfl)).symm
  rw [key]


noncomputable instance fintypeFinsuppDegreeEq (d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | Finsupp.degree s = d} :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin n)).finsuppAntidiag d)
    (fun f => mem_finsuppAntidiag_iff_degree n d f)


instance instModuleFiniteHomogSub (d : ℕ) :
    Module.Finite k (homogeneousSubmodule (Fin n) k d) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm


noncomputable def freeModuleGradingEquiv (m d : ℕ) :
    freeModuleGrading k n (m := m) d ≃ₗ[k]
    (Fin m → ↥(homogeneousSubmodule (Fin n) k d)) where
  toFun f i := ⟨f.val i, f.property i⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun g := ⟨fun i => (g i).val, fun i => (g i).property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl


lemma finrank_homogeneousSubmodule_eq (d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) = n.multichoose d := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have e : ↥(Finsupp.supported k k {s : Fin n →₀ ℕ | Finsupp.degree s = d}) ≃ₗ[k]
      ↥{s : Fin n →₀ ℕ | Finsupp.degree s = d} →₀ k :=
    Finsupp.supportedEquivFinsupp _
  calc Module.finrank k ↥(Finsupp.supported k k {d_1 | Finsupp.degree d_1 = d})
      = Module.finrank k (↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} →₀ k) := e.finrank_eq
    _ = Fintype.card ↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} :=
        Module.finrank_finsupp_self k
    _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag d).card := Fintype.card_ofFinset ..
    _ = n.multichoose d := by
        rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]; simp [Fintype.card_fin]


lemma hilbertSeries_homogeneousSubmodule :
    hilbertSeries (homogeneousSubmodule (Fin n) k) = (PowerSeries.mk (1 : ℕ → ℤ)) ^ n := by
  cases n with
  | zero =>
    ext d; simp only [hilbertSeries, PowerSeries.coeff_mk, pow_zero, PowerSeries.coeff_one]
    rw [finrank_homogeneousSubmodule_eq]
    cases d <;> simp
  | succ n =>
    ext d
    rw [show PowerSeries.mk (1 : ℕ → ℤ) = PowerSeries.mk 1 from rfl]
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    simp only [hilbertSeries, PowerSeries.coeff_mk]

    rw [finrank_homogeneousSubmodule_eq]
    congr 1
    rw [Nat.multichoose_eq]
    rw [show n + 1 + d - 1 = n + d from by omega]
    exact Nat.choose_symm_of_eq_add (by omega)




lemma alternating_sum_general' (nn : ℕ) (b : ℕ → ℤ) :
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) =
    b 0 + (-1 : ℤ) ^ nn * b (nn + 1) := by
  induction nn with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]; ring

lemma alternating_sum_eq' (nn : ℕ) (a : Fin (nn + 1) → ℤ) (target : ℤ)
    (b : ℕ → ℤ) (hb0 : b 0 = target) (hbn : b (nn + 1) = 0)
    (hab : ∀ j : Fin (nn + 1), a j = b j.val + b (j.val + 1)) :
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j = target := by
  have : ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j =
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) := by
    congr 1; ext j; rw [hab j]
  rw [this, alternating_sum_general', hbn, mul_zero, add_zero, hb0]





theorem lemma_12_6_krull_dim_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {f}) + 1 := by
  have h : ({f} : Set A) ⊆ ↑(Ring.jacobson A) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Set.singleton_subset_iff.mpr hf
  have := ringKrullDim_le_ringKrullDim_quotient_add_encard {f} h
  simp [Set.encard_singleton] at this
  exact this






lemma image_castSucc_eq_image {A : Type*} {k : ℕ} (f : Fin (k + 1) → A) (j : Fin k) :
    Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)} =
    Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Function.comp]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.castSucc i, by simp [Fin.castSucc, hi], rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hik : (i : ℕ) < k := by
      have := j.isLt; simp [Fin.castSucc] at hi; omega
    exact ⟨⟨i, hik⟩, by simp [Fin.castSucc] at hi ⊢; exact hi, by simp [Fin.castSucc]⟩

lemma isRegularSequence_init {A : Type*} [CommRing A] {k : ℕ}
    {f : Fin (k + 1) → A} (hreg : IsRegularSequence f) :
    IsRegularSequence (f ∘ Fin.castSucc) := by
  obtain ⟨hnzd, hnt⟩ := hreg
  constructor
  · intro j r hr
    suffices h : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h _ rfl r hr
    intro I hI r' hr'
    subst hI
    have hImgEq := image_castSucc_eq_image f j
    suffices h2 : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h2 _ (by rw [← hImgEq]) r' hr'
    intro I' hI' r'' hr''
    subst hI'
    exact hnzd (Fin.castSucc j) r'' hr''
  · have hsub : Ideal.span (Set.range (f ∘ Fin.castSucc)) ≤ Ideal.span (Set.range f) := by
      apply Ideal.span_mono; intro x ⟨i, hi⟩; exact ⟨Fin.castSucc i, hi⟩
    rw [Ideal.Quotient.nontrivial_iff] at hnt ⊢
    exact ne_top_of_le_ne_top hnt hsub

section KoszulHelpers

variable {A : Type*} [CommRing A]

def koszulProjL (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.castAdd c i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulProjR (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin c → A) where
  toFun v i := v (Fin.natAdd b i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulReindex {a b : ℕ} (h : a = b) : (Fin a → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.cast h.symm i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulSmulLM (a_val : A) (k : ℕ) : (Fin k → A) →ₗ[A] (Fin k → A) where
  toFun v i := a_val * v i
  map_add' v w := by ext; simp [mul_add]
  map_smul' r v := by ext; simp [smul_eq_mul, mul_left_comm]

def koszulInjectL (b c : ℕ) : (Fin b → A) →ₗ[A] (Fin (b + c) → A) where
  toFun u := Fin.addCases u (fun _ => 0)
  map_add' u₁ u₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r u := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

def koszulInjectR (b c : ℕ) : (Fin c → A) →ₗ[A] (Fin (b + c) → A) where
  toFun w := Fin.addCases (fun _ => 0) w
  map_add' w₁ w₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r w := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

noncomputable def koszulDSafe (n : ℕ)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (p : ℕ) : (Fin (n.choose (p+1)) → A) →ₗ[A] (Fin (n.choose p) → A) :=
  if h : p < n then d' p h else 0

end KoszulHelpers

section KoszulConeDiff

variable {A : Type*} [CommRing A]

noncomputable def koszulConeDiff0 (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose 1) → A) →ₗ[A] (Fin ((n+1).choose 0) → A) :=
  let h_s := Nat.choose_succ_succ n 0
  have h_t : n.choose 0 = (n+1).choose 0 := by simp [Nat.choose_zero_right]
  (koszulReindex h_t).comp (
    (-(koszulSmulLM a (n.choose 0))).comp ((koszulProjL (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)) +
    (d' 0 hn).comp ((koszulProjR (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)))

noncomputable def koszulConeDiffSucc (n p' : ℕ) (hp' : p' < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose (p'+2)) → A) →ₗ[A] (Fin ((n+1).choose (p'+1)) → A) :=
  (koszulReindex (Nat.choose_succ_succ n p').symm).comp (
    (koszulInjectL (n.choose p') (n.choose (p'+1))).comp
      ((d' p' hp').comp ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
        (koszulReindex (Nat.choose_succ_succ n (p'+1))))) +
    (koszulInjectR (n.choose p') (n.choose (p'+1))).comp (
      (koszulSmulLM ((-1 : A) ^ (p' + 2) * a) (n.choose (p'+1))).comp
        ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1)))) +
      (koszulDSafe n d' (p'+1)).comp
        ((koszulProjR (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1))))))

noncomputable def koszulConeDiff (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (p : ℕ) → (hp : p < n + 1) →
    (Fin ((n+1).choose (p+1)) → A) →ₗ[A] (Fin ((n+1).choose p) → A)
  | 0, _ => koszulConeDiff0 n hn d' a
  | p + 1, hp => koszulConeDiffSucc n p (Nat.lt_of_succ_lt_succ hp) d' a

end KoszulConeDiff

section KoszulBlockLemmas

variable {A : Type*} [CommRing A]

end KoszulBlockLemmas

section KoszulConeExactness
omit k n


end KoszulConeExactness


lemma X_nonzerodiv_mod_lower (k : Type*) [Field k] (n : ℕ) (j : Fin n)
    (p : MvPolynomial (Fin n) k)
    (hp : MvPolynomial.X j * p ∈ Ideal.span (MvPolynomial.X '' {i : Fin n | (i : ℕ) < (j : ℕ)})) :
    p ∈ Ideal.span (MvPolynomial.X '' {i : Fin n | (i : ℕ) < (j : ℕ)}) := by
  rw [MvPolynomial.mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff : MvPolynomial.coeff m p ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hcoeff2 : MvPolynomial.coeff (Finsupp.single j 1 + m) (MvPolynomial.X j * p) ≠ 0 := by
    rw [MvPolynomial.coeff_X_mul]; exact hcoeff
  obtain ⟨i, hi_lt, hi_ne⟩ := hp _ (MvPolynomial.mem_support_iff.mpr hcoeff2)
  refine ⟨i, hi_lt, ?_⟩
  have hij : j ≠ i := by intro h; subst h; exact Nat.lt_irrefl _ hi_lt
  rwa [Finsupp.add_apply, Finsupp.single_apply, if_neg hij, zero_add] at hi_ne

set_option maxHeartbeats 400000 in

theorem variables_form_regular_sequence
    (k : Type*) [Field k] (n : ℕ) :
    IsRegularSequence (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)) := by
  refine ⟨fun j r hr h => ?_, ?_⟩
  ·
    apply hr
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r

    have hmul : (X j : MvPolynomial (Fin n) k) * p ∈
        Ideal.span ((fun i : Fin n => (X i : MvPolynomial (Fin n) k)) '' {i | (i : ℕ) < ↑j}) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      rwa [smul_eq_mul] at h
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact X_nonzerodiv_mod_lower k n j p hmul
  ·
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) k) ∈
        Ideal.span (Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k))) := by
      rw [htop]; trivial
    have hrange : Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k)) =
      (X : Fin n → MvPolynomial (Fin n) k) '' Set.univ := by ext x; simp [Set.mem_range]
    rw [hrange, mem_ideal_span_X_image] at h1
    have hmem : (0 : Fin n →₀ ℕ) ∈ (1 : MvPolynomial (Fin n) k).support := by
      rw [mem_support_iff, coeff_one, if_pos rfl]; exact one_ne_zero
    obtain ⟨i, _, hi⟩ := h1 0 hmem
    simp at hi


lemma eval_zero_of_homogeneous_pos_deg
    (f : MvPolynomial (Fin n) k) (d : ℕ) (hd : 0 < d)
    (hhom : ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m f ≠ 0 →
      (m.sum fun _ e => e) = d) :
    MvPolynomial.eval (0 : Fin n → k) f = 0 := by
  simp only [MvPolynomial.eval_zero]
  rw [MvPolynomial.constantCoeff_eq]

  by_contra h
  have := hhom 0 h
  simp [Finsupp.sum] at this
  omega




theorem reverse_catenary_polynomial_ring
    (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height ≤
      (n : WithBot ℕ∞) := by
  set Rp := MvPolynomial (Fin n) k with hRp_def
  let pp : PrimeSpectrum Rp := ⟨p, inferInstance⟩

  have h_quot_eq : ringKrullDim (Rp ⧸ p) = ↑(Order.coheight pp) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]; congr 1

  have h_ht_eq : p.height = Order.height pp := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]

  have hbdd : BddAbove (Set.range fun (a : PrimeSpectrum Rp) =>
      Order.height a + Order.coheight a) :=
    OrderTop.bddAbove _
  have h3 : Order.height pp + Order.coheight pp ≤
      ⨆ (a : PrimeSpectrum Rp), Order.height a + Order.coheight a :=
    le_ciSup hbdd pp
  have h4 : Order.krullDim (PrimeSpectrum Rp) =
      ↑(⨆ (a : PrimeSpectrum Rp), Order.height a + Order.coheight a) :=
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
  have h5 : ↑(Order.height pp + Order.coheight pp) ≤
      Order.krullDim (PrimeSpectrum Rp) := by
    rw [h4, WithBot.coe_le_coe]; exact h3

  have h6 : ringKrullDim Rp = (n : WithBot ℕ∞) := by
    show ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

  rw [h_quot_eq, h_ht_eq, ← WithBot.coe_add, add_comm]
  exact le_trans h5 (by rw [ringKrullDim] at h6; exact h6.le)


lemma height_bound_from_dim_bounds
    (dim : WithBot ℕ∞) (ht : ℕ∞) (n j1 : ℕ)
    (h_le : dim + ht ≤ (n : WithBot ℕ∞))
    (h_ge : (n : WithBot ℕ∞) ≤ dim + ht)
    (h_dim : dim + ((j1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)) :
    (j1 : ℕ∞) ≤ ht := by
  have h_eq : dim + (ht : WithBot ℕ∞) = (n : WithBot ℕ∞) := le_antisymm h_le h_ge
  by_cases hdim : dim = ⊥
  · rw [hdim, WithBot.bot_add] at h_eq; exact absurd h_eq.symm WithBot.coe_ne_bot
  obtain ⟨dim_val, hdim_eq⟩ := WithBot.ne_bot_iff_exists.mp hdim
  subst hdim_eq
  by_cases hht : ht = ⊤
  · subst hht; exact le_top
  by_cases hdv : dim_val = ⊤
  · exfalso; rw [hdv, ← WithBot.coe_add, top_add] at h_eq
    exact absurd (WithBot.coe_injective h_eq) (ENat.top_ne_coe n)
  obtain ⟨h_nat, hht_eq⟩ := WithTop.ne_top_iff_exists.mp hht
  obtain ⟨d_nat, hdim_eq⟩ := WithTop.ne_top_iff_exists.mp hdv
  subst hht_eq; subst hdim_eq
  change (j1 : ℕ∞) ≤ h_nat
  have h1 : (d_nat : ℕ∞) + (h_nat : ℕ∞) = (n : ℕ∞) := by
    rw [← WithBot.coe_add] at h_eq; exact WithBot.coe_injective h_eq
  rw [show ((j1 : ℕ) : WithBot ℕ∞) = ((j1 : ℕ∞) : WithBot ℕ∞) from by norm_cast] at h_dim
  have h2 : (d_nat : ℕ∞) + (j1 : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← WithBot.coe_add] at h_dim; exact WithBot.coe_le_coe.mp h_dim
  have : d_nat + h_nat = n := by exact_mod_cast h1
  have : d_nat + j1 ≤ n := by exact_mod_cast h2
  exact_mod_cast (show j1 ≤ h_nat by omega)






def quotientHomogeneousSubmodule
    (I : Ideal (MvPolynomial (Fin n) k)) (i : ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I) :=
  (homogeneousSubmodule (Fin n) k i).map (I.mkQ.restrictScalars k)

def qAnalog (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => if i < d then 1 else 0)

def invOneSubX : PowerSeries ℤ :=
  PowerSeries.mk (fun _ => 1)

section HilbertHelpers
variable {n}

lemma mem_finsuppAntidiag_univ_iff_degree' {d : ℕ} (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree f = d := by
  rw [Finset.mem_finsuppAntidiag]
  simp only [Finset.subset_univ, and_true]
  have key : (Finset.univ : Finset (Fin n)).sum f = Finsupp.degree f := by
    simp [Finsupp.degree]
    exact (Finsupp.sum_fintype f (fun _ => id) (fun _ => rfl)).symm
  rw [key]

noncomputable instance fintypeFinsuppDegreeEq' (d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | Finsupp.degree s = d} :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin n)).finsuppAntidiag d)
    (fun f => mem_finsuppAntidiag_univ_iff_degree' f)

lemma finrank_homogeneousSubmodule_eq' (d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) = n.multichoose d := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have e : ↥(Finsupp.supported k k {s : Fin n →₀ ℕ | Finsupp.degree s = d}) ≃ₗ[k]
      ↥{s : Fin n →₀ ℕ | Finsupp.degree s = d} →₀ k :=
    Finsupp.supportedEquivFinsupp _
  calc Module.finrank k ↥(Finsupp.supported k k {d_1 | Finsupp.degree d_1 = d})
      = Module.finrank k (↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} →₀ k) := e.finrank_eq
    _ = Fintype.card ↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} :=
        Module.finrank_finsupp_self k
    _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag d).card := Fintype.card_ofFinset ..
    _ = n.multichoose d := by
        rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]; simp [Fintype.card_fin]

end HilbertHelpers

theorem hilbert_series_polynomial_ring :
    hilbertSeries (homogeneousSubmodule (Fin n) k) = invOneSubX ^ n := by
  ext d
  simp only [hilbertSeries, invOneSubX, PowerSeries.coeff_mk, PowerSeries.coeff_pow,
    Finset.prod_const_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, finrank_homogeneousSubmodule_eq']
  norm_cast
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_range]


lemma one_sub_X_pow_mul_invOneSubX (d : ℕ) :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ d) * invOneSubX = qAnalog d := by
  ext m
  simp only [qAnalog, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub, invOneSubX]
  by_cases hm : m < d
  · simp only [hm, ite_true]
    suffices h : (PowerSeries.coeff m) ((PowerSeries.X : PowerSeries ℤ) ^ d *
        PowerSeries.mk (fun _ => (1 : ℤ))) = 0 by linarith
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal] at hab
    simp [PowerSeries.coeff_X_pow, show a ≠ d from by omega]
  · simp only [show ¬(m < d) from by omega, ite_false]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ m)
    rw [show d + j = j + d from by ring, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_mk]
    ring

lemma prod_one_sub_mul_invOneSubX_eq_prod_qAnalog {m : ℕ} (d : Fin m → ℕ) :
    (∏ i : Fin m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ d i)) * invOneSubX ^ m =
    ∏ i : Fin m, qAnalog (d i) := by
  have h1 : invOneSubX ^ m = ∏ _i : Fin m, (invOneSubX : PowerSeries ℤ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact one_sub_X_pow_mul_invOneSubX (d i)






end
