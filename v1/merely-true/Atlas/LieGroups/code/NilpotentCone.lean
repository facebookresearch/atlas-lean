/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section

open scoped LieAlgebra
open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]

def IsNilpotentElement (x : L) : Prop :=
  IsNilpotent (LieAlgebra.ad R L x)

def NilpotentCone : Set L :=
  {x : L | IsNilpotentElement R L x}

theorem NilpotentCone.zero_mem : (0 : L) ∈ NilpotentCone R L := by
  simp [NilpotentCone, IsNilpotentElement, map_zero]

theorem NilpotentCone.smul_mem {x : L} (hx : x ∈ NilpotentCone R L) (c : R) :
    c • x ∈ NilpotentCone R L := by
  simp only [NilpotentCone, Set.mem_setOf_eq, IsNilpotentElement] at *
  rw [map_smul]
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩

theorem NilpotentCone.mem_iff (x : L) :
    x ∈ NilpotentCone R L ↔ IsNilpotentElement R L x :=
  Iff.rfl

structure AdjointGroupAction where
  G : Type*
  instGroup : Group G
  Ad : G → L ≃ₗ⁅R⁆ L
  Ad_mul : ∀ g₁ g₂ : G,
    (Ad (@HMul.hMul G G G (@instHMul G instGroup.toMul) g₁ g₂) : L → L) =
    (Ad g₁ : L → L) ∘ (Ad g₂ : L → L)
  Ad_one : Ad (@One.one G instGroup.toOne) = LieEquiv.refl
  instTopologicalSpaceG : TopologicalSpace G
  instIrreducibleSpaceG : @IrreducibleSpace G instTopologicalSpaceG
  orbit_map_continuous : ∀ (ts : TopologicalSpace L) (x : L),
    @Continuous G L instTopologicalSpaceG ts (fun g => Ad g x)

variable {R L}

def AdjointOrbit (Gact : AdjointGroupAction R L) (x : L) : Set L :=
  { y : L | ∃ g : Gact.G, Gact.Ad g x = y }

def IsAdjointConjugate (Gact : AdjointGroupAction R L) (x y : L) : Prop :=
  ∃ g : Gact.G, Gact.Ad g x = y

theorem AdjointOrbit.self_mem (Gact : AdjointGroupAction R L) (x : L) :
    x ∈ AdjointOrbit Gact x :=
  ⟨@One.one Gact.G Gact.instGroup.toOne, by rw [Gact.Ad_one]; rfl⟩

theorem IsAdjointConjugate.refl (Gact : AdjointGroupAction R L) (x : L) :
    IsAdjointConjugate Gact x x :=
  AdjointOrbit.self_mem Gact x

theorem IsNilpotentElement.map_lieEquiv (φ : L ≃ₗ⁅R⁆ L) {x : L}
    (hx : IsNilpotentElement R L x) : IsNilpotentElement R L (φ x) := by
  unfold IsNilpotentElement at *
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩


  have key : LieAlgebra.ad R L (φ x) =
      φ.toLinearEquiv.conjRingEquiv (LieAlgebra.ad R L x) := by
    show _ = φ.toLinearEquiv.conj _
    rw [LieAlgebra.conj_ad_apply]
  rw [key, ← map_pow (φ.toLinearEquiv.conjRingEquiv), hn, map_zero]

theorem AdjointOrbit.subset_nilpotentCone (Gact : AdjointGroupAction R L) {x : L}
    (hx : IsNilpotentElement R L x) :
    AdjointOrbit Gact x ⊆ NilpotentCone R L := by
  intro y ⟨g, hg⟩
  rw [NilpotentCone.mem_iff, ← hg]
  exact hx.map_lieEquiv (Gact.Ad g)

variable (R L)

def lieCentralizer (x : L) : Submodule R L :=
  LinearMap.ker (LieAlgebra.ad R L x : L →ₗ[R] L)

variable [Module.Finite R L] [Module.Free R L]

def IsRegularElement (x : L) : Prop :=
  Module.finrank R (lieCentralizer R L x) = LieAlgebra.rank R L

def IsRegularNilpotent (x : L) : Prop :=
  IsNilpotentElement R L x ∧ IsRegularElement R L x

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

def IsAdInvariant (x : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  ∀ v ∈ V, (LieAlgebra.ad ℂ 𝔤 x) v ∈ V

def IsSl2SubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  IsAdInvariant h V ∧ IsAdInvariant e V ∧ IsAdInvariant f V

def IsSl2IrreducibleSubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  V ≠ ⊥ ∧ IsSl2SubmoduleOf h e f V ∧
  ∀ W : Submodule ℂ 𝔤, W ≤ V → IsSl2SubmoduleOf h e f W → W = ⊥ ∨ W = V

def IsSl2SubmoduleOf.toLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hV : IsSl2SubmoduleOf h e f V) :
    LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤 where
  __ := V
  lie_mem {x v} hv := by
    obtain ⟨c₁, c₂, c₃, hx⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.2
    have hv_h := hV.1 v hv
    have hv_e := hV.2.1 v hv
    have hv_f := hV.2.2 v hv

    have heq : ⁅(x : 𝔤), v⁆ = c₁ • ⁅e, v⁆ + c₂ • ⁅f, v⁆ + c₃ • ⁅h, v⁆ := by
      rw [hx, add_lie, add_lie, smul_lie, smul_lie, smul_lie, t.lie_e_f]
    show ⁅(x : 𝔤), v⁆ ∈ V
    rw [heq]
    exact V.add_mem (V.add_mem (V.smul_mem _ hv_e) (V.smul_mem _ hv_f)) (V.smul_mem _ hv_h)

omit [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
@[simp]
lemma IsSl2SubmoduleOf.toLieSubmodule_toSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hV : IsSl2SubmoduleOf h e f V) :
    (hV.toLieSubmodule t).toSubmodule = V := rfl

def IsSl2IrreducibleLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    (V : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤) : Prop :=
  V ≠ ⊥ ∧
  ∀ W : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤,
    W.toSubmodule ≤ V.toSubmodule → W = ⊥ ∨ W = V

omit [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
lemma lieSubmodule_isSl2SubmoduleOf {h e f : 𝔤} (t : IsSl2Triple h e f)
    (W : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤) :
    IsSl2SubmoduleOf h e f W.toSubmodule := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  ·
    have hmem : h ∈ t.toLieSubalgebra ℂ :=
      IsSl2Triple.mem_toLieSubalgebra_iff.mpr ⟨0, 0, 1, by simp [t.lie_e_f.symm]⟩
    exact W.lie_mem (x := ⟨h, hmem⟩) hv
  · have hmem : e ∈ t.toLieSubalgebra ℂ :=
      IsSl2Triple.mem_toLieSubalgebra_iff.mpr ⟨1, 0, 0, by simp⟩
    exact W.lie_mem (x := ⟨e, hmem⟩) hv
  · have hmem : f ∈ t.toLieSubalgebra ℂ :=
      IsSl2Triple.mem_toLieSubalgebra_iff.mpr ⟨0, 1, 0, by simp⟩
    exact W.lie_mem (x := ⟨f, hmem⟩) hv

omit [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem IsSl2IrreducibleSubmoduleOf.toIsSl2IrreducibleLieSubmodule
    {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V) :
    IsSl2IrreducibleLieSubmodule t (hirr.2.1.toLieSubmodule t) := by
  constructor
  ·
    intro habs
    apply hirr.1
    have : (hirr.2.1.toLieSubmodule t).toSubmodule =
        (⊥ : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤).toSubmodule := by
      rw [habs]
    simp [IsSl2SubmoduleOf.toLieSubmodule_toSubmodule] at this
    exact this
  ·
    intro W hW

    have hW_inv : IsSl2SubmoduleOf h e f W.toSubmodule := lieSubmodule_isSl2SubmoduleOf t W

    simp [IsSl2SubmoduleOf.toLieSubmodule_toSubmodule] at hW
    rcases hirr.2.2 W.toSubmodule hW hW_inv with h_bot | h_eq
    · left
      rwa [← LieSubmodule.toSubmodule_eq_bot]
    · right
      apply_fun LieSubmodule.toSubmodule using LieSubmodule.toSubmodule_injective
      simp [IsSl2SubmoduleOf.toLieSubmodule_toSubmodule, h_eq]

structure RootSystemData (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] where
  rankVal : ℕ
  rank_pos : 0 < rankVal
  rank_eq : rankVal = LieAlgebra.rank ℂ 𝔤
  simpleRootVector : Fin rankVal → 𝔤
  simpleCorootVector : Fin rankVal → 𝔤
  simpleCoroot : Fin rankVal → 𝔤
  halfSumPosCoroots : 𝔤
  lie_simpleRootVector_simpleCorootVector :
    ∀ i j : Fin rankVal,
      ⁅simpleRootVector i, simpleCorootVector j⁆ =
        if i = j then simpleCoroot i else 0
  simpleRootVector_ne_zero : ∀ i : Fin rankVal, simpleRootVector i ≠ 0
  simpleCorootVector_ne_zero : ∀ i : Fin rankVal, simpleCorootVector i ≠ 0
  halfSumPosCoroots_regular :
    Module.finrank ℂ (lieCentralizer ℂ 𝔤 halfSumPosCoroots) = LieAlgebra.rank ℂ 𝔤
  no_joint_centralizer :
    ∀ v : 𝔤, ⁅halfSumPosCoroots, v⁆ = 0 →
      ⁅∑ i, simpleRootVector i, v⁆ = 0 → v = 0
  halfSumPosCoroots_odd_dim_irreducibles :
    ∀ {h e f : 𝔤} (_hprinc_h : h = (2 : ℂ) • halfSumPosCoroots)
      (_hprinc_e : e = ∑ i, simpleRootVector i)
      {V : Submodule ℂ 𝔤} (_hirr : IsSl2IrreducibleSubmoduleOf h e f V),
      ¬ Even (Module.finrank ℂ V)

structure IsPrincipalSl2Triple (h e f : 𝔤) extends IsSl2Triple h e f where
  rootData : RootSystemData 𝔤
  e_eq_sum : e = ∑ i, rootData.simpleRootVector i
  h_eq_two_rho : h = (2 : ℂ) • rootData.halfSumPosCoroots
  e_nilpotent : IsNilpotentElement ℂ 𝔤 e


lemma nsmul_two_eq_zero_of_complex {M : Type*} [AddCommGroup M] [Module ℂ M] {x : M}
    (h : (2 : ℕ) • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℂ 2 x] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

omit [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
lemma sl2_acts_trivially_on_one_dim_subspace
    {h e f : 𝔤} (ht : IsSl2Triple h e f)
    {v : 𝔤} {c_e c_f : ℂ}
    (he_v : ⁅e, v⁆ = c_e • v) (hf_v : ⁅f, v⁆ = c_f • v) :
    ⁅e, v⁆ = 0 ∧ ⁅f, v⁆ = 0 ∧ ⁅h, v⁆ = 0 := by

  have hh_v : ⁅h, v⁆ = 0 := by
    rw [show h = ⁅e, f⁆ from ht.lie_e_f.symm]
    have key : ⁅⁅e, f⁆, v⁆ = ⁅e, ⁅f, v⁆⁆ - ⁅f, ⁅e, v⁆⁆ := by
      have h1 := (leibniz_lie e f v).symm
      exact add_right_cancel_iff.mp (show ⁅⁅e, f⁆, v⁆ + ⁅f, ⁅e, v⁆⁆ =
        (⁅e, ⁅f, v⁆⁆ - ⁅f, ⁅e, v⁆⁆) + ⁅f, ⁅e, v⁆⁆ from by rw [sub_add_cancel]; exact h1)
    rw [key, hf_v, he_v, lie_smul, lie_smul, he_v, hf_v, smul_smul, smul_smul,
        mul_comm c_f c_e, sub_self]

  have he_zero : ⁅e, v⁆ = 0 := by
    have leib := leibniz_lie h e v
    rw [ht.lie_h_e_nsmul, nsmul_lie, hh_v, lie_zero, add_zero] at leib
    have lhs : ⁅h, ⁅e, v⁆⁆ = 0 := by rw [he_v, lie_smul, hh_v, smul_zero]
    rw [lhs] at leib
    exact nsmul_two_eq_zero_of_complex leib.symm

  have hf_zero : ⁅f, v⁆ = 0 := by
    have leib := leibniz_lie h f v
    rw [ht.lie_h_f_nsmul, neg_lie, nsmul_lie, hh_v, lie_zero, add_zero] at leib
    have lhs : ⁅h, ⁅f, v⁆⁆ = 0 := by rw [hf_v, lie_smul, hh_v, smul_zero]
    rw [lhs] at leib
    exact nsmul_two_eq_zero_of_complex (neg_eq_zero.mp leib.symm)
  exact ⟨he_zero, hf_zero, hh_v⟩

omit [IsSemisimple ℂ 𝔤] in
lemma principal_sl2_no_centralizer
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {v : 𝔤} (hv : v ≠ 0)
    (hh : ⁅h, v⁆ = 0) (he : ⁅e, v⁆ = 0) (_hf : ⁅f, v⁆ = 0) : False := by

  have h_rho : ⁅hprinc.rootData.halfSumPosCoroots, v⁆ = 0 := by
    have := hprinc.h_eq_two_rho
    rw [this, smul_lie] at hh
    exact smul_eq_zero.mp hh |>.resolve_left (by norm_num : (2 : ℂ) ≠ 0)

  have h_sum : ⁅∑ i, hprinc.rootData.simpleRootVector i, v⁆ = 0 := by
    rwa [← hprinc.e_eq_sum]

  exact hv (hprinc.rootData.no_joint_centralizer v h_rho h_sum)


omit [IsSemisimple ℂ 𝔤] in
theorem sl2_irreducible_submodule_dim
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V) :
    ∃ n : ℕ, 1 ≤ n ∧ Module.finrank ℂ V = n + 1 := by

  have hne : V ≠ ⊥ := hirr.1

  have hge1 : 1 ≤ Module.finrank ℂ ↥V :=
    Submodule.one_le_finrank_iff.mpr hne

  have hne1 : Module.finrank ℂ ↥V ≠ 1 := by
    intro h1

    obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne

    have hspan : ∀ w ∈ V, ∃ c : ℂ, w = c • v := by
      intro w hw
      have hv_ne' : (⟨v, hv_mem⟩ : ↥V) ≠ 0 := by
        simp [Submodule.mk_eq_zero]; exact hv_ne
      have hspan_top : ℂ ∙ (⟨v, hv_mem⟩ : ↥V) = ⊤ :=
        (finrank_eq_one_iff_of_nonzero ⟨v, hv_mem⟩ hv_ne').mp h1
      have hw' : (⟨w, hw⟩ : ↥V) ∈ ℂ ∙ (⟨v, hv_mem⟩ : ↥V) := by
        rw [hspan_top]; exact Submodule.mem_top
      rw [Submodule.mem_span_singleton] at hw'
      obtain ⟨c, hc⟩ := hw'
      exact ⟨c, by have := congr_arg Subtype.val hc; simp at this; exact this.symm⟩


    have he_inv := hirr.2.1.2.1 v hv_mem
    have hf_inv := hirr.2.1.2.2 v hv_mem
    obtain ⟨c_e, hce⟩ := hspan _ he_inv
    obtain ⟨c_f, hcf⟩ := hspan _ hf_inv

    have ⟨he0, hf0, hh0⟩ := sl2_acts_trivially_on_one_dim_subspace
      hprinc.toIsSl2Triple hce hcf

    exact principal_sl2_no_centralizer hprinc hv_ne hh0 he0 hf0

  refine ⟨Module.finrank ℂ ↥V - 1, ?_, ?_⟩
  · omega
  · omega

theorem sl2_integration_minus_one_acts_trivially
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V) :
    ∀ n : ℕ, Module.finrank ℂ V = n + 1 → (-1 : ℤ) ^ n = 1 := by
  intro n hn

  have hodd := hprinc.rootData.halfSumPosCoroots_odd_dim_irreducibles
    hprinc.h_eq_two_rho hprinc.e_eq_sum hirr

  rw [hn] at hodd
  have hn_even : Even n := by
    by_contra h_not_even
    exact hodd (Nat.even_add_one.mpr h_not_even)

  exact Even.neg_one_pow hn_even

theorem principal_sl2_even_weights
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V)
    (n : ℕ) (hn : Module.finrank ℂ V = n + 1) : Even n := by

  have h_neg_one := sl2_integration_minus_one_acts_trivially hprinc hirr n hn

  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow hne
  linarith

omit [LieAlgebra.IsSemisimple ℂ 𝔤] in

theorem principal_sl2_highest_weight_even
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V) :
    ∀ n : ℕ, Module.finrank ℂ V = n + 1 → Even n := by
  intro n hn

  have h_neg_one := sl2_integration_minus_one_acts_trivially hprinc hirr n hn

  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow hne
  linarith

omit [IsSemisimple ℂ 𝔤] in
theorem h_eigenvalues_are_even
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V) :
    ∃ m : ℕ, 0 < m ∧ Module.finrank ℂ V = 2 * m + 1 := by

  obtain ⟨n, hn_pos, hn_dim⟩ := sl2_irreducible_submodule_dim hprinc hirr

  have hn_even := principal_sl2_highest_weight_even hprinc hirr n hn_dim

  obtain ⟨m, hm⟩ := hn_even
  exact ⟨m, by omega, by omega⟩

lemma lieCentralizer_smul_eq {K : Type*} [Field K] {L : Type*} [LieRing L] [LieAlgebra K L]
    {c : K} (hc : c ≠ 0) (x : L) :
    lieCentralizer K L (c • x) = lieCentralizer K L x := by
  ext y
  simp only [lieCentralizer, LinearMap.mem_ker]
  constructor
  · intro h
    have : (LieAlgebra.ad K L (c • x)) y = c • (LieAlgebra.ad K L x) y := by
      simp [LieAlgebra.ad_apply]
    rw [this] at h
    exact (smul_eq_zero.mp h).resolve_left hc
  · intro h
    have : (LieAlgebra.ad K L (c • x)) y = c • (LieAlgebra.ad K L x) y := by
      simp [LieAlgebra.ad_apply]
    rw [this, h, smul_zero]

omit [IsSemisimple ℂ 𝔤] in
theorem principal_sl2_h_is_regular
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f) :
    Module.finrank ℂ (lieCentralizer ℂ 𝔤 h) = LieAlgebra.rank ℂ 𝔤 := by

  rw [hprinc.h_eq_two_rho]

  rw [lieCentralizer_smul_eq (by norm_num : (2 : ℂ) ≠ 0)]

  exact hprinc.rootData.halfSumPosCoroots_regular

omit [IsSemisimple ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem finrank_ker_of_invariant_direct_sum
    {n : ℕ} {V : Fin n → Submodule ℂ 𝔤}
    (hint : DirectSum.IsInternal V)
    {φ : 𝔤 →ₗ[ℂ] 𝔤}
    (hinv : ∀ i v, v ∈ V i → φ v ∈ V i) :
    Module.finrank ℂ (LinearMap.ker φ) =
      ∑ i : Fin n, Module.finrank ℂ ↥(V i ⊓ LinearMap.ker φ) := by

  have sum_eq_zero_of_indep : ∀ {V' : Fin n → Submodule ℂ 𝔤},
      iSupIndep V' → ∀ {f : Fin n → 𝔤}, (∀ i, f i ∈ V' i) → ∑ i, f i = 0 →
      ∀ i, f i = 0 := by
    intro V' hindep f hf hsum i
    have heq : f i = -(∑ j ∈ Finset.univ.erase i, f j) :=
      eq_neg_of_add_eq_zero_left
        (by rwa [Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)])
    have h2 : f i ∈ ⨆ j, ⨆ (_ : j ≠ i), V' j := by
      rw [heq]; apply Submodule.neg_mem; apply Submodule.sum_mem
      intro j hj; rw [Finset.mem_erase] at hj
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj.1 (hf j))
    have hdisj := hindep i; rw [disjoint_iff] at hdisj
    exact (Submodule.mem_bot (R := ℂ)).mp (hdisj ▸ Submodule.mem_inf.mpr ⟨hf i, h2⟩)

  obtain ⟨hindep, hspan⟩ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).mp hint

  set W : Fin n → Submodule ℂ ↥(LinearMap.ker φ) :=
    fun i => (V i).comap (LinearMap.ker φ).subtype

  have hintW : DirectSum.IsInternal W := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ·
      rw [iSupIndep_def]; intro i; rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have hxi : ((LinearMap.ker φ).subtype x : 𝔤) ∈ V i := hx1
      have hxs : ((LinearMap.ker φ).subtype x : 𝔤) ∈ ⨆ j, ⨆ (_ : j ≠ i), V j := by
        have hmem : (LinearMap.ker φ).subtype x ∈ Submodule.map (LinearMap.ker φ).subtype
            (⨆ j, ⨆ (_ : j ≠ i), (V j).comap (LinearMap.ker φ).subtype) :=
          ⟨x, hx2, rfl⟩
        rw [Submodule.map_iSup] at hmem; simp only [Submodule.map_iSup] at hmem
        exact (iSup_mono fun j => iSup_mono fun hj =>
          Submodule.map_comap_le (LinearMap.ker φ).subtype (V j)) hmem
      rw [iSupIndep_def] at hindep; have hdisj := hindep i
      rw [Submodule.disjoint_def] at hdisj
      exact Subtype.val_injective (hdisj _ hxi hxs)
    ·
      rw [Submodule.eq_top_iff']; intro x
      have hx_top : (x : 𝔤) ∈ (⊤ : Submodule ℂ 𝔤) := Submodule.mem_top
      rw [← hspan] at hx_top
      rw [Submodule.mem_iSup_iff_exists_finsupp] at hx_top
      obtain ⟨f, hf_mem, hf_sum⟩ := hx_top
      have hf_sum' : ∑ i : Fin n, (f i : 𝔤) = (x : 𝔤) := by
        rw [← hf_sum, Finsupp.sum]
        exact (Finset.sum_subset f.support.subset_univ
          (fun i _ hi => Finsupp.notMem_support_iff.mp hi)).symm
      have hf_ker : ∀ i : Fin n, f i ∈ LinearMap.ker φ := by
        intro i; rw [LinearMap.mem_ker]
        exact sum_eq_zero_of_indep hindep
          (fun i => hinv i _ (hf_mem i))
          (by rw [← map_sum, hf_sum']; exact x.2) i
      have hx_eq : x = ∑ i : Fin n, (⟨f i, hf_ker i⟩ : ↥(LinearMap.ker φ)) := by
        ext; simp [hf_sum']
      rw [hx_eq]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.mem_iSup_of_mem i
        (show (⟨f i, hf_ker i⟩ : ↥(LinearMap.ker φ)) ∈ W i from hf_mem i)

  have hfr : Module.finrank ℂ ↥(LinearMap.ker φ) = ∑ i, Module.finrank ℂ ↥(W i) := by
    set b := fun i => Module.finBasis ℂ ↥(W i)
    rw [Module.finrank_eq_card_basis (hintW.collectedBasis b)]
    simp [Fintype.card_sigma]
  rw [hfr]

  congr 1; ext i
  change Module.finrank ℂ ↥(Submodule.comap (LinearMap.ker φ).subtype (V i)) = _
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker φ) _, Submodule.map_comap_subtype,
      inf_comm]







omit [IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem sl2_raising_kernel_nonempty
    {h e f : 𝔤}
    {V : Submodule ℂ 𝔤} (hirr : IsSl2IrreducibleSubmoduleOf h e f V)
    (he : IsNilpotentElement ℂ 𝔤 e) :
    V ⊓ LinearMap.ker (LieAlgebra.ad ℂ 𝔤 e) ≠ ⊥ := by

  have hV_ne_bot : V ≠ ⊥ := hirr.1
  have hV_inv : ∀ v ∈ V, (LieAlgebra.ad ℂ 𝔤 e) v ∈ V := hirr.2.1.2.1

  have hV_nt : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV_ne_bot

  have hnil : IsNilpotent ((LieAlgebra.ad ℂ 𝔤 e : 𝔤 →ₗ[ℂ] 𝔤).restrict hV_inv) := by
    obtain ⟨n, hn⟩ := he
    exact ⟨n, by rw [Module.End.pow_restrict]; ext ⟨v, hv⟩; simp [hn]⟩

  have hker : ((LieAlgebra.ad ℂ 𝔤 e : 𝔤 →ₗ[ℂ] 𝔤).restrict hV_inv).ker ≠ ⊥ := by
    intro habs
    rw [LinearMap.ker_eq_bot] at habs
    obtain ⟨n, hn⟩ := hnil
    have hinj : ∀ k, Function.Injective
        (⇑(((LieAlgebra.ad ℂ 𝔤 e : 𝔤 →ₗ[ℂ] 𝔤).restrict hV_inv) ^ k) : V → V) := by
      intro k; induction k with
      | zero => intro a b h; simpa using h
      | succ k ih =>
        intro a b hab; rw [pow_succ'] at hab
        exact ih (habs hab)
    have h0 := hinj n; rw [hn] at h0
    have : Subsingleton V :=
      ⟨fun a b => by have := @h0 a b; simp at this; exact this⟩
    exact absurd hV_nt (not_nontrivial_iff_subsingleton.mpr this)

  rw [Submodule.ne_bot_iff] at hker ⊢
  obtain ⟨⟨v, hv⟩, hvmem, hvne⟩ := hker
  simp only [LinearMap.mem_ker, LinearMap.restrict_apply, Subtype.ext_iff,
    Submodule.coe_zero] at hvmem
  exact ⟨v, Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr hvmem⟩,
    fun heq => hvne (by subst heq; rfl)⟩

omit [IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
lemma ker_ad_e_ad_h_invariant
    {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hV : IsSl2SubmoduleOf h e f V) :
    ∀ v ∈ V ⊓ LinearMap.ker (LieAlgebra.ad ℂ 𝔤 e),
      (LieAlgebra.ad ℂ 𝔤 h) v ∈ V ⊓ LinearMap.ker (LieAlgebra.ad ℂ 𝔤 e) := by
  intro v hv
  simp only [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
  refine ⟨hV.1 v hv.1, ?_⟩
  simp only [LieAlgebra.ad_apply]
  simp only [LieAlgebra.ad_apply] at hv
  rw [leibniz_lie e h v, hv.2, lie_zero, add_zero]
  have : ⁅e, h⁆ = -(2 • e) := by
    rw [← lie_skew]; simp [t.lie_h_e_nsmul]
  rw [this, neg_lie, nsmul_lie, hv.2, smul_zero, neg_zero]





structure BorelSubgroupData (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]
    (rsd : RootSystemData 𝔤) where
  B : Type*
  instGroupB : Group B
  AdB : B → 𝔤 ≃ₗ⁅ℂ⁆ 𝔤
  AdB_mul : ∀ b₁ b₂ : B,
    (@AdB (@HMul.hMul B B B (@instHMul B instGroupB.toMul) b₁ b₂) : 𝔤 → 𝔤) =
    (AdB b₁ : 𝔤 → 𝔤) ∘ (AdB b₂ : 𝔤 → 𝔤)
  numPosRoots : ℕ
  rootVector : Fin numPosRoots → 𝔤
  isSimple : Fin numPosRoots → Prop
  instDecSimple : DecidablePred isSimple
  numSimple_eq_rank : (Finset.univ.filter (fun i => @decide (isSimple i) (instDecSimple i))).card
    = rsd.rankVal
  simpleRootVectorBij : Fin rsd.rankVal → Fin numPosRoots
  simpleRootVectorBij_isSimple : ∀ j, isSimple (simpleRootVectorBij j)
  simpleRootVectorBij_surj : ∀ i, isSimple i → ∃ j, simpleRootVectorBij j = i
  simpleRootVector_eq : ∀ j, rootVector (simpleRootVectorBij j) = rsd.simpleRootVector j
  H_torus : Type*
  instGroupH : Group H_torus
  embedH : @H_torus → B
  N_unip : Type*
  instGroupN : Group N_unip
  embedN : @N_unip → B
  torus_scaling : @H_torus → Fin numPosRoots → ℂˣ
  levi_decomp : ∀ (b : B),
    ∃ (t : @H_torus) (n : @N_unip),
      ∀ (x : 𝔤), (AdB b : 𝔤 → 𝔤) x =
        (AdB (@embedH t) : 𝔤 → 𝔤) ((AdB (@embedN n) : 𝔤 → 𝔤) x)
  unip_orbit_fwd : ∀ (n : @N_unip),
    ∃ (c : Fin numPosRoots → ℂ),
      (∀ i, isSimple i → c i = 1) ∧
      (@AdB (@embedN n) : 𝔤 → 𝔤)
          (∑ j : Fin rsd.rankVal, rootVector (simpleRootVectorBij j))
        = ∑ i, c i • rootVector i
  unip_orbit_bwd : ∀ (c : Fin numPosRoots → ℂ),
    (∀ i, isSimple i → c i = 1) →
    ∃ (n : @N_unip),
      (@AdB (@embedN n) : 𝔤 → 𝔤)
          (∑ j : Fin rsd.rankVal, rootVector (simpleRootVectorBij j))
        = ∑ i, c i • rootVector i
  torus_action_eq : ∀ (t : @H_torus) (i : Fin numPosRoots),
    (@AdB (@embedH t) : 𝔤 → 𝔤) (rootVector i) =
      (torus_scaling t i : ℂ) • rootVector i
  torus_simple_surj : ∀ (s : Fin rsd.rankVal → ℂˣ),
    ∃ (t : @H_torus), ∀ j, torus_scaling t (simpleRootVectorBij j) = s j

omit [LieAlgebra.IsSemisimple ℂ 𝔤] in
theorem BorelSubgroupData.levi_product {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) (t : BD.H_torus) (n : BD.N_unip) :
    ∃ b : BD.B,
      ∀ x : 𝔤, (BD.AdB b : 𝔤 → 𝔤) x =
        (BD.AdB (BD.embedH t) : 𝔤 → 𝔤) ((BD.AdB (BD.embedN n) : 𝔤 → 𝔤) x) := by
  refine ⟨@HMul.hMul BD.B BD.B BD.B (@instHMul BD.B BD.instGroupB.toMul)
    (BD.embedH t) (BD.embedN n), ?_⟩
  intro x
  exact congr_fun (BD.AdB_mul (BD.embedH t) (BD.embedN n)) x

def BorelSubgroupData.regularNilpotentSet {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) : Set 𝔤 :=
  { x : 𝔤 | ∃ (c : Fin BD.numPosRoots → ℂ),
      (∀ i, BD.isSimple i → c i ≠ 0) ∧
      x = ∑ i, c i • BD.rootVector i }

def BorelSubgroupData.borelOrbit {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) (e : 𝔤) : Set 𝔤 :=
  { y : 𝔤 | ∃ b : BD.B, @BD.AdB b e = y }

omit [LieAlgebra.IsSemisimple ℂ 𝔤] in

theorem principal_nilpotent_borel_orbit
    {h e f : 𝔤} (hprinc : IsPrincipalSl2Triple h e f)
    (BD : BorelSubgroupData 𝔤 hprinc.rootData) :

    BD.borelOrbit e = BD.regularNilpotentSet := by


  have he : e = ∑ j : Fin hprinc.rootData.rankVal,
      BD.rootVector (BD.simpleRootVectorBij j) := by
    conv_lhs => rw [hprinc.e_eq_sum]
    congr 1; ext j; exact (BD.simpleRootVector_eq j).symm
  ext x
  simp only [BorelSubgroupData.borelOrbit, BorelSubgroupData.regularNilpotentSet, Set.mem_setOf_eq]
  constructor
  ·


    rintro ⟨b, rfl⟩

    obtain ⟨t, n, hlevi⟩ := BD.levi_decomp b

    obtain ⟨c, hc_simple, hc_eq⟩ := BD.unip_orbit_fwd n

    have hbe : @BD.AdB b e =
        ∑ i, (c i * (BD.torus_scaling t i : ℂ)) • BD.rootVector i := by
      have h1 : @BD.AdB b e = (BD.AdB (BD.embedH t))
          ((BD.AdB (BD.embedN n)) e) := hlevi e
      rw [h1, show (BD.AdB (BD.embedN n) : 𝔤 → 𝔤) e =
          (BD.AdB (BD.embedN n) : 𝔤 → 𝔤) (∑ j, BD.rootVector (BD.simpleRootVectorBij j))
        from by rw [← he], hc_eq, map_sum]
      simp only [map_smul]
      congr 1; ext i; rw [BD.torus_action_eq, smul_smul]
    refine ⟨fun i => c i * (BD.torus_scaling t i : ℂ), fun i hi => ?_, ?_⟩
    · exact mul_ne_zero (by rw [hc_simple i hi]; exact one_ne_zero) (Units.ne_zero _)
    · exact hbe
  ·


    rintro ⟨c, hc_nz, rfl⟩

    have hc_units : ∀ j : Fin hprinc.rootData.rankVal,
        c (BD.simpleRootVectorBij j) ≠ 0 :=
      fun j => hc_nz _ (BD.simpleRootVectorBij_isSimple j)
    let s : Fin hprinc.rootData.rankVal → ℂˣ :=
      fun j => Units.mk0 (c (BD.simpleRootVectorBij j)) (hc_units j)
    obtain ⟨t, ht_simple⟩ := BD.torus_simple_surj s

    let d : Fin BD.numPosRoots → ℂ := fun i => c i / (BD.torus_scaling t i : ℂ)

    have hd_simple : ∀ i, BD.isSimple i → d i = 1 := by
      intro i hi
      obtain ⟨j, hj⟩ := BD.simpleRootVectorBij_surj i hi
      subst hj
      simp only [d]
      have : (BD.torus_scaling t (BD.simpleRootVectorBij j) : ℂ) = (s j : ℂ) := by
        congr 1; exact ht_simple j
      rw [this]
      simp [s, div_self (hc_units j)]

    obtain ⟨n, hn_eq⟩ := BD.unip_orbit_bwd d hd_simple

    obtain ⟨b, hb_eq⟩ := BD.levi_product t n

    refine ⟨b, ?_⟩
    show @BD.AdB b e = ∑ i, c i • BD.rootVector i
    have h1 : @BD.AdB b e = (BD.AdB (BD.embedH t))
        ((BD.AdB (BD.embedN n)) e) := hb_eq e
    rw [h1, show (BD.AdB (BD.embedN n) : 𝔤 → 𝔤) e =
        (BD.AdB (BD.embedN n) : 𝔤 → 𝔤) (∑ j, BD.rootVector (BD.simpleRootVectorBij j))
      from by rw [← he], hn_eq, map_sum]
    simp only [map_smul]
    congr 1; ext i
    rw [BD.torus_action_eq, smul_smul]
    congr 1
    exact div_mul_cancel₀ (c i) (Units.ne_zero (BD.torus_scaling t i))

end PrincipalSl2

section FieldResults

variable {K : Type*} [Field K] {L' : Type*} [LieRing L'] [LieAlgebra K L'] [Module.Finite K L']

theorem exists_regular_and_cartan_engel [Infinite K] :
    ∃ x : L', LieAlgebra.IsRegular K x ∧ (LieSubalgebra.engel K x).IsCartanSubalgebra := by
  have h : (Module.finrank K L' : Cardinal) ≤ Cardinal.mk K :=
    Cardinal.natCast_le_aleph0.trans (Cardinal.infinite_iff.mp ‹Infinite K›)
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isRegular_of_finrank_le_card K L' h
  refine ⟨x, hx, ?_, LieSubalgebra.normalizer_engel _ _⟩
  apply LieSubalgebra.isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {LieSubalgebra.engel K z | z ∈ LieSubalgebra.engel K x} :=
    ⟨LieSubalgebra.engel K x, x, LieSubalgebra.self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨LieSubalgebra.engel K y, y, hy, rfl⟩
  apply engel_isBot_of_isMin h (LieSubalgebra.engel K x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices Module.finrank K (LieSubalgebra.engel K x) ≤
      Module.finrank K (LieSubalgebra.engel K y) by
    suffices LieSubalgebra.engel K y = LieSubalgebra.engel K x from this.ge
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [(LieAlgebra.isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply LieAlgebra.rank_le_finrank_engel

theorem exists_cartan_finrank_eq_rank [Infinite K] :
    ∃ (H : LieSubalgebra K L'), H.IsCartanSubalgebra ∧
      Module.finrank K H = LieAlgebra.rank K L' := by
  obtain ⟨x, hx_reg, hx_cartan⟩ := exists_regular_and_cartan_engel (K := K) (L' := L')
  exact ⟨LieSubalgebra.engel K x, hx_cartan,
    (LieAlgebra.isRegular_iff_finrank_engel_eq_rank K x).mp hx_reg⟩

end FieldResults


end LieAlgebra

namespace LieAlgebra

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

theorem NilpotentCone.nonempty_of_isSemisimple [LieAlgebra.IsSemisimple ℂ 𝔤]
    [Nontrivial 𝔤] :
    (NilpotentCone ℂ 𝔤).Nonempty :=
  ⟨0, NilpotentCone.zero_mem ℂ 𝔤⟩

variable [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

end LieAlgebra





namespace LieAlgebra

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]





theorem adjointOrbit_isIrreducible [LieAlgebra.IsSemisimple ℂ 𝔤]
    [TopologicalSpace 𝔤]
    (Gact : AdjointGroupAction ℂ 𝔤)
    {e : 𝔤} (_he_nil : IsNilpotentElement ℂ 𝔤 e) (_he_reg : IsRegularElement ℂ 𝔤 e) :
    IsIrreducible (AdjointOrbit Gact e) := by


  have orbit_eq : AdjointOrbit Gact e = Set.range (fun g => Gact.Ad g e) := by
    ext y; simp [AdjointOrbit, Set.mem_range]
  rw [orbit_eq, ← Set.image_univ]
  letI : TopologicalSpace Gact.G := Gact.instTopologicalSpaceG
  letI : IrreducibleSpace Gact.G := Gact.instIrreducibleSpaceG
  exact (IrreducibleSpace.isIrreducible_univ Gact.G).image _
    (Gact.orbit_map_continuous _ e).continuousOn




structure NilpotentConeCoordinateRing [LieAlgebra.IsSemisimple ℂ 𝔤] where
  carrier : Type*
  instCommRing : CommRing carrier
  instAlgebra : Algebra ℂ carrier
  instNontrivial : Nontrivial carrier
  genericFiber : Type*
  instGenericFiberCommRing : CommRing genericFiber
  toGenericFiber : @RingHom carrier genericFiber
    instCommRing.toNonAssocRing.toNonAssocSemiring
    instGenericFiberCommRing.toNonAssocRing.toNonAssocSemiring
  instCarrierGenericFiberAlg : @Algebra carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
  locSubmonoid : @Submonoid carrier instCommRing.toMulOneClass
  locSubmonoid_le_nonZeroDivisors :
    ∀ s ∈ locSubmonoid, s ∈ @nonZeroDivisors carrier instCommRing.toMonoidWithZero
  instIsLocalization : @IsLocalization carrier instCommRing.toCommSemiring
    locSubmonoid genericFiber instGenericFiberCommRing.toCommSemiring
    instCarrierGenericFiberAlg
  toGenericFiber_eq : toGenericFiber = @algebraMap carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
    instCarrierGenericFiberAlg
  instGenericFiberSemisimple : @IsSemisimpleRing genericFiber
    instGenericFiberCommRing.toRing

omit [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem NilpotentConeCoordinateRing.instIsReduced_of_structure
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Sg0 : NilpotentConeCoordinateRing 𝔤) :
    @IsReduced Sg0.carrier Sg0.instCommRing.toMonoidWithZero.toZero
      Sg0.instCommRing.toSemiring.toMonoidWithZero.toMonoid.toPow := by
  letI := Sg0.instCommRing
  letI := Sg0.instGenericFiberCommRing
  constructor
  intro x ⟨n, hn⟩
  have h_nilp : IsNilpotent (Sg0.toGenericFiber x) :=
    ⟨n, by rw [← Sg0.toGenericFiber.map_pow, hn, Sg0.toGenericFiber.map_zero]⟩
  haveI := Sg0.instGenericFiberSemisimple
  have hred : @IsReduced Sg0.genericFiber Sg0.instGenericFiberCommRing.toZero
      Sg0.instGenericFiberCommRing.toMonoid.toPow := inferInstance
  have h_zero : Sg0.toGenericFiber x = 0 :=
    @IsReduced.eq_zero Sg0.genericFiber _ _ hred _ h_nilp
  letI := Sg0.instCarrierGenericFiberAlg
  letI := Sg0.instIsLocalization
  have hinj : Function.Injective Sg0.toGenericFiber := by
    rw [show (Sg0.toGenericFiber : Sg0.carrier →+* Sg0.genericFiber) =
      algebraMap Sg0.carrier Sg0.genericFiber from Sg0.toGenericFiber_eq]
    exact IsLocalization.injective (M := Sg0.locSubmonoid) Sg0.genericFiber
      Sg0.locSubmonoid_le_nonZeroDivisors
  exact hinj (by rw [h_zero, Sg0.toGenericFiber.map_zero])




omit [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem NilpotentConeCoordinateRing.toGenericFiber_injective
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Sg0 : NilpotentConeCoordinateRing 𝔤) :
    Function.Injective Sg0.toGenericFiber := by


  letI := Sg0.instCommRing
  letI := Sg0.instGenericFiberCommRing
  letI := Sg0.instCarrierGenericFiberAlg
  letI := Sg0.instIsLocalization
  rw [show (Sg0.toGenericFiber : Sg0.carrier →+* Sg0.genericFiber) =
    algebraMap Sg0.carrier Sg0.genericFiber from Sg0.toGenericFiber_eq]
  exact IsLocalization.injective (M := Sg0.locSubmonoid) Sg0.genericFiber
    Sg0.locSubmonoid_le_nonZeroDivisors

omit [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem NilpotentConeCoordinateRing.genericFiber_isReduced
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Sg0 : NilpotentConeCoordinateRing 𝔤) :
    @IsReduced Sg0.genericFiber Sg0.instGenericFiberCommRing.toZero
      Sg0.instGenericFiberCommRing.toMonoid.toPow := by


  letI := Sg0.instGenericFiberCommRing
  haveI := Sg0.instGenericFiberSemisimple
  exact inferInstance



omit [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] in
theorem NilpotentCone.isReduced [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Sg0 : NilpotentConeCoordinateRing 𝔤) :
    letI := Sg0.instCommRing
    IsReduced Sg0.carrier := by


  letI := Sg0.instCommRing
  letI := Sg0.instGenericFiberCommRing
  constructor
  intro x ⟨n, hn⟩

  have h_nilp : IsNilpotent (Sg0.toGenericFiber x) :=
    ⟨n, by rw [← Sg0.toGenericFiber.map_pow, hn, Sg0.toGenericFiber.map_zero]⟩


  have hred := NilpotentConeCoordinateRing.genericFiber_isReduced 𝔤 Sg0
  have h_zero : Sg0.toGenericFiber x = 0 :=
    @IsReduced.eq_zero Sg0.genericFiber _ _ hred _ h_nilp


  have hinj := NilpotentConeCoordinateRing.toGenericFiber_injective 𝔤 Sg0
  exact hinj (by rw [h_zero, Sg0.toGenericFiber.map_zero])

def maximalQuotientIdeal_17
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :
    TwoSidedIdeal (UniversalEnvelopingAlgebra ℂ 𝔤) :=
  TwoSidedIdeal.span
    { x | ∃ (z : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤))),
      x = (z : UniversalEnvelopingAlgebra ℂ 𝔤) - algebraMap ℂ _ (χ z) }

abbrev MaximalQuotient_17
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :=
  (maximalQuotientIdeal_17 𝔤 χ).ringCon.Quotient

def HasDomainAssociatedGraded (R : Type*) [Ring R] : Prop :=
  ∃ (v : R → WithBot ℤ),
    v 0 = ⊥ ∧
    v 1 ≠ ⊥ ∧
    (∀ a : R, a ≠ 0 → v a ≠ ⊥) ∧
    (∀ a b : R, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)

theorem nontrivial_of_hasDomainAssociatedGraded (R : Type*) [Ring R]
    (h : HasDomainAssociatedGraded R) : Nontrivial R := by
  obtain ⟨v, hv0, hv1, -, -⟩ := h
  exact ⟨⟨0, 1, fun h01 => hv1 (by rw [← h01, hv0])⟩⟩

theorem isDomain_of_hasDomainAssociatedGraded (R : Type*) [Ring R]
    (h : HasDomainAssociatedGraded R) : IsDomain R := by
  haveI : Nontrivial R := nontrivial_of_hasDomainAssociatedGraded R h
  obtain ⟨v, hv0, _, hvne, hvmul⟩ := h
  have hNoZero : NoZeroDivisors R := by
    constructor
    intro a b hab
    by_contra hc
    push Not at hc
    obtain ⟨ha, hb⟩ := hc
    have h1 := hvmul a b ha hb
    rw [hab, hv0] at h1
    have h1' : v a + v b = ⊥ := h1.symm
    rw [WithBot.add_eq_bot] at h1'
    exact h1'.elim (hvne a ha) (hvne b hb)
  exact NoZeroDivisors.to_isDomain R

structure SubMulFiltrationDomain (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)
  gr_domain : ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(v a + v b < v (a * b))

theorem hasDomainAssociatedGraded_of_subMulFiltrationDomain {R : Type*} [Ring R]
    (w : SubMulFiltrationDomain R) : HasDomainAssociatedGraded R :=
  ⟨w.v, w.v_zero, w.v_one, w.v_nonzero, fun a b ha hb =>
    le_antisymm (not_lt.mp (w.gr_domain a b ha hb)) (w.v_submul a b ha hb)⟩

structure SubMulFiltration (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)

def SubMulFiltration.toSubMulFiltrationDomain {R : Type*} [Ring R]
    (F : SubMulFiltration R)
    (hgr : ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(F.v a + F.v b < F.v (a * b))) :
    SubMulFiltrationDomain R :=
  { v := F.v
    v_zero := F.v_zero
    v_one := F.v_one
    v_nonzero := F.v_nonzero
    v_submul := F.v_submul
    gr_domain := hgr }

structure PBWSymbolData {R : Type*} [Ring R] (v : R → WithBot ℤ) where
  D : Type
  instRing : Ring D
  instDomain : @IsDomain D instRing.toSemiring
  σ : R → D
  σ_nonzero : ∀ a : R, a ≠ 0 → σ a ≠ 0
  σ_cancel : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b < v (a * b) → σ a * σ b = 0

theorem no_cancellation_of_pbwSymbolData
    {R : Type*} [Ring R] {v : R → WithBot ℤ}
    (data : PBWSymbolData v) :
    ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(v a + v b < v (a * b)) := by
  intro a b ha hb hlt

  have h := data.σ_cancel a b ha hb hlt

  letI := data.instRing
  haveI := data.instDomain
  rcases mul_eq_zero.mp h with h | h

  · exact data.σ_nonzero a ha h

  · exact data.σ_nonzero b hb h






















end LieAlgebra

end
