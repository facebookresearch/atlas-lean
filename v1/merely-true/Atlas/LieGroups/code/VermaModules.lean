/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure TriangularDecomposition where
  𝔥 : LieSubalgebra R 𝔤
  𝔫_pos : LieSubalgebra R 𝔤
  𝔫_neg : LieSubalgebra R 𝔤
  is_cartan : 𝔥.IsCartanSubalgebra
  h_abelian : IsLieAbelian 𝔥
  decomp_exists : ∀ x : 𝔤, ∃ (n_neg : 𝔫_neg) (h : 𝔥) (n_pos : 𝔫_pos),
    x = (n_neg : 𝔤) + (h : 𝔤) + (n_pos : 𝔤)
  decomp_unique : ∀ (n₁ n₁' : 𝔫_neg) (h₁ h₁' : 𝔥) (p₁ p₁' : 𝔫_pos),
    (n₁ : 𝔤) + (h₁ : 𝔤) + (p₁ : 𝔤) = (n₁' : 𝔤) + (h₁' : 𝔤) + (p₁' : 𝔤) →
    n₁ = n₁' ∧ h₁ = h₁' ∧ p₁ = p₁'

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def 𝔟 : LieSubalgebra R 𝔤 := Δ.𝔥 ⊔ Δ.𝔫_pos

def weightSubspace
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := {m : M | ∀ h : Δ.𝔥, ⁅(h : 𝔤), m⁆ = μ h • m}
  add_mem' {a b} ha hb h := by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' h := by rw [lie_zero, smul_zero]
  smul_mem' c _ hm h := by rw [LieModule.lie_smul, hm h, smul_comm]

theorem weightSubspace_eq_mathlib
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    Δ.weightSubspace M μ =
    (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

end TriangularDecomposition

structure IsHighestWeightModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) where
  highestWeightVec : M
  hwv_ne_zero : highestWeightVec ≠ 0
  cartan_action : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), highestWeightVec⁆ = wt h • highestWeightVec
  npos_action : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), highestWeightVec⁆ = 0
  generates : LieSubmodule.lieSpan R 𝔤 {highestWeightVec} = ⊤

structure IsVermaModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    extends IsHighestWeightModule Δ M wt where
  universal_map :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (v : V),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) →
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) →
      ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η highestWeightVec = v
  universal_unique :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (η₁ η₂ : M →ₗ⁅R, 𝔤⁆ V),
      η₁ highestWeightVec = η₂ highestWeightVec → η₁ = η₂

def ueaSubalgAction (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R (↥𝔫) →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥𝔫) M)

def instModuleUEASubalg (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Module (UniversalEnvelopingAlgebra R (↥𝔫)) M :=
  Module.compHom M (ueaSubalgAction 𝔫 M).toRingHom


section UEASubalgHelpers

variable {R : Type*} [CommRing R]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

lemma ueaSubalg_mul_apply
    (u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (u₁ * u₂)) m =
    (ueaSubalgAction Δ.𝔫_neg M u₁) ((ueaSubalgAction Δ.𝔫_neg M u₂) m) := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ * u₂)) m = _
  rw [map_mul]; rfl

lemma ueaSubalg_add_apply
    (u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (u₁ + u₂)) m =
    (ueaSubalgAction Δ.𝔫_neg M u₁) m + (ueaSubalgAction Δ.𝔫_neg M u₂) m := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ + u₂)) m = _
  rw [map_add]; rfl

lemma ueaSubalg_smul_apply
    (r : R) (u₀ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (r • u₀)) m =
    r • ((ueaSubalgAction Δ.𝔫_neg M u₀) m) := by
  have : ueaSubalgAction Δ.𝔫_neg M (r • u₀) = r • ueaSubalgAction Δ.𝔫_neg M u₀ :=
    map_smul (ueaSubalgAction Δ.𝔫_neg M) r u₀
  rw [this]; rfl

lemma ueaSubalg_one_apply (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom 1) m = m
  rw [map_one]; rfl

lemma ueaSubalg_ι_apply (n : ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆ := by
  change ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥Δ.𝔫_neg) M))
    (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieModule.toEnd_apply_apply]; rfl

lemma ueaSubalg_algebraMap_apply (r : R) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r)) m = r • m := by
  have : ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r) = algebraMap R _ r :=
    AlgHom.commutes (ueaSubalgAction Δ.𝔫_neg M) r
  rw [this, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]; rfl

end UEASubalgHelpers

set_option maxHeartbeats 3200000 in
theorem nminus_orbit_lie_stable
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (x : 𝔤) (m : M)
    (hm : ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
      (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m) :
    ∃ u' : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
      (ueaSubalgAction Δ.𝔫_neg M u') hM.highestWeightVec = ⁅x, m⁆ := by
  obtain ⟨u, hu⟩ := hm
  subst hu
  let Φ := ueaSubalgAction Δ.𝔫_neg M
  let vhw := hM.highestWeightVec


  suffices Q : ∀ (t : TensorAlgebra R ↥Δ.𝔫_neg) (y : 𝔤) (s : M),
      (∃ u₀, (Φ u₀) vhw = s) →
      (∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s⁆) →
      ∃ u₀, (Φ u₀) vhw =
        ⁅y, (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) t)) s⁆ by

    have hvhw : ∃ u₀, (Φ u₀) vhw = vhw := ⟨1, ueaSubalg_one_apply vhw⟩

    have base : ∀ (y : 𝔤), ∃ u₀, (Φ u₀) vhw = ⁅y, vhw⁆ := by
      intro y
      obtain ⟨n_neg, h, n_pos, hdecomp⟩ := Δ.decomp_exists y
      rw [hdecomp, add_lie, add_lie, hM.npos_action n_pos, hM.cartan_action h]
      simp only [add_zero]
      exact ⟨UniversalEnvelopingAlgebra.ι R n_neg + algebraMap R _ (wt h),
        by rw [ueaSubalg_add_apply, ueaSubalg_ι_apply, ueaSubalg_algebraMap_apply]⟩

    obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
      (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) u
    exact Q t x vhw hvhw base

  intro t
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro y s hs hstable
    have heq : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (algebraMap R _ r))) s = r • s := by
      have : RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ r
      rw [this]; exact ueaSubalg_algebraMap_apply r s
    rw [heq, lie_smul]
    obtain ⟨u', hu'⟩ := hstable y
    exact ⟨r • u', by rw [ueaSubalg_smul_apply, hu']⟩
  | ι n =>
    intro y s hs hstable
    have hι : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (TensorAlgebra.ι R n))) s = ⁅(n : 𝔤), s⁆ :=
      ueaSubalg_ι_apply n s
    rw [hι, leibniz_lie]
    obtain ⟨u₁, hu₁⟩ := hstable ⁅y, (n : 𝔤)⁆
    obtain ⟨u₂, hu₂⟩ := hstable y
    exact ⟨u₁ + UniversalEnvelopingAlgebra.ι R n * u₂,
      by rw [ueaSubalg_add_apply, ueaSubalg_mul_apply, ueaSubalg_ι_apply, hu₁, hu₂]⟩
  | add a b iha ihb =>
    intro y s hs hstable
    have hadd : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (a + b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a)) s +
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_add]; exact ueaSubalg_add_apply _ _ s
    rw [hadd, lie_add]
    obtain ⟨u₁, hu₁⟩ := iha y s hs hstable
    obtain ⟨u₂, hu₂⟩ := ihb y s hs hstable
    exact ⟨u₁ + u₂, by rw [ueaSubalg_add_apply, hu₁, hu₂]⟩
  | mul a b iha ihb =>
    intro y s hs hstable
    have hmul : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (a * b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a))
        ((Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s) := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_mul]; exact ueaSubalg_mul_apply _ _ s
    rw [hmul]
    set s' := (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s
    have hs' : ∃ u₀, (Φ u₀) vhw = s' := by
      obtain ⟨u_s, hu_s⟩ := hs
      let mkb : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg :=
        RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b
      exact ⟨mkb * u_s, by rw [ueaSubalg_mul_apply, hu_s]⟩
    have hstable' : ∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s'⁆ :=
      fun z => ihb z s hs hstable
    exact iha y s' hs' hstable'

theorem pbw_verma_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Surjective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  intro m

  set S : Set M := {m : M | ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
    (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m} with hS_def


  have hS_add : ∀ a b : M, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
    exact ⟨u₁ + u₂, by simp [map_add, LinearMap.add_apply]⟩
  have hS_zero : (0 : M) ∈ S := ⟨0, by simp [map_zero, LinearMap.zero_apply]⟩
  have hS_smul : ∀ (r : R) (a : M), a ∈ S → r • a ∈ S := by
    rintro r _ ⟨u, rfl⟩
    exact ⟨r • u, by simp [map_smul, LinearMap.smul_apply]⟩

  have hS_lie : ∀ (x : 𝔤) (a : M), a ∈ S → ⁅x, a⁆ ∈ S :=
    fun x a ha => nminus_orbit_lie_stable hM x a ha

  set N : LieSubmodule R 𝔤 M := {
    carrier := S
    add_mem' := fun ha hb => hS_add _ _ ha hb
    zero_mem' := hS_zero
    smul_mem' := fun r _ hx => hS_smul r _ hx
    lie_mem := fun {x a} ha => hS_lie x a ha
  } with hN_def

  have hvlam : hM.highestWeightVec ∈ N :=
    ⟨1, by simp [map_one]⟩

  have htop : N = ⊤ := by
    rw [eq_top_iff, ← hM.generates]
    exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hvlam)

  have hm : m ∈ N := htop ▸ trivial
  obtain ⟨u, hu⟩ : m ∈ S := hm

  exact ⟨u, hu⟩











section VermaProperties

variable {Δ : TriangularDecomposition R 𝔤}
variable {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable {wt : Δ.𝔥 →ₗ[R] R}




lemma IsVermaModule.hwv_not_mem_proper (hM : IsVermaModule Δ M wt)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤) :
    hM.highestWeightVec ∉ N := by
  intro hmem
  apply hN
  rw [eq_top_iff]
  calc ⊤ = LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} := hM.generates.symm
    _ ≤ N := LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hmem)

def augmentationUEA (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)









theorem IsVermaModule.quotient_by_maximal_irreducible (_hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) :
    LieModule.IsIrreducible R 𝔤 (M ⧸ J) := by

  show IsSimpleOrder (LieSubmodule R 𝔤 (M ⧸ J))

  have : Nontrivial (LieSubmodule R 𝔤 (M ⧸ J)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    apply hJ_ne_top
    rw [eq_top_iff]
    intro m _
    have hmem : (LieSubmodule.Quotient.mk' J) m ∈ (⊤ : LieSubmodule R 𝔤 (M ⧸ J)) := trivial
    rw [← h] at hmem
    rw [LieSubmodule.mem_bot] at hmem
    rwa [LieSubmodule.Quotient.mk_eq_zero] at hmem

  exact {
    eq_bot_or_eq_top := by
      intro N'

      set N := N'.comap (LieSubmodule.Quotient.mk' J) with hN_def

      have hJN : J ≤ N := by
        intro m hm
        show m ∈ N'.comap (LieSubmodule.Quotient.mk' J)
        rw [LieSubmodule.mem_comap]
        rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hm]
        exact N'.zero_mem

      by_cases hN : N = ⊤
      ·
        right; rw [eq_top_iff]; intro x _
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        exact (hN ▸ trivial : m ∈ N)
      ·
        left
        have hNJ : N ≤ J := hJ_max N hN
        rw [eq_bot_iff]; intro x hx
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hNJ hx) }




def WeightSpace (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := { m : M | ∀ (h : Δ.𝔥), ⁅(h : 𝔤), m⁆ = μ h • m }
  add_mem' := fun {a b} ha hb h => by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' := fun h => by rw [lie_zero, smul_zero]
  smul_mem' := fun r {m} hm h => by rw [lie_smul, hm h, smul_comm]

theorem weightSpace_eq_mathlib_weightSpace {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    WeightSpace Δ M μ =
    (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

theorem weightSpace_eq_weightSubspace {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    WeightSpace Δ M μ = Δ.weightSubspace M μ := by
  ext m; exact Iff.rfl

def weights (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Set (Δ.𝔥 →ₗ[R] R) :=
  { μ | WeightSpace Δ M μ ≠ ⊥ }

structure PositiveRootData (Δ : TriangularDecomposition R 𝔤) where
  posRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_ne_zero : ∀ α ∈ posRoots, α ≠ 0
  posRoots_pointed_cone : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ posRoots →
    ∀ (n : ℤ), n < 0 →
    ¬ ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), n • α = ∑ β ∈ posRoots, (c β) • β
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  corootPairing_add_left : ∀ (μ ν α : Δ.𝔥 →ₗ[R] R),
    corootPairing (μ + ν) α = corootPairing μ α + corootPairing ν α
  corootPairing_nsmul_left : ∀ (n : ℕ) (μ α : Δ.𝔥 →ₗ[R] R),
    corootPairing (n • μ) α = n • corootPairing μ α
  corootPairing_self : ∀ α ∈ posRoots, corootPairing α α = 2
  negRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_neg)
  negRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(negRootVec α hα) : 𝔤)⁆ = -(α h) • (↑(negRootVec α hα) : 𝔤)
  ι_negRootVec_ne_zero : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots),
    UniversalEnvelopingAlgebra.ι R (negRootVec α hα) ≠ 0
  uea_nminus_noZeroDivisors : NoZeroDivisors (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  uea_nminus_nontrivial : Nontrivial (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  posRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_pos)
  posRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(posRootVec α hα) : 𝔤)⁆ = (α h) • (↑(posRootVec α hα) : 𝔤)
  npos_span : ∀ (e : Δ.𝔫_pos), ∃ (c : ∀ α ∈ posRoots, R),
    (e : 𝔤) = ∑ x ∈ posRoots.attach, c x.1 x.2 • (↑(posRootVec x.1 x.2) : 𝔤)



def PositiveRootData.IsInQPlus {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), μ = ∑ α ∈ rd.posRoots, (c α) • α



theorem nminus_QPlus_weight_vector
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (rd : PositiveRootData Δ)
    (v : M) (hv : v ∈ WeightSpace Δ M wt)
    (β : Δ.𝔥 →ₗ[R] R) (hβ : rd.IsInQPlus β) :
    ∃ (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      u ≠ 0 ∧
      (ueaSubalgAction Δ.𝔫_neg M u) v ∈ WeightSpace Δ M (wt - β) := by

  obtain ⟨c, hc⟩ := hβ


  have single_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
      (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      ⁅(↑(rd.negRootVec α hα) : 𝔤), m⁆ ∈ WeightSpace Δ M (μ - α) := by
    intro α hα μ m hm h

    rw [leibniz_lie, rd.negRootVec_weight α hα h, hm h]
    rw [neg_smul, neg_lie, lie_smul]
    simp [LinearMap.sub_apply, sub_smul]
    abel

  have ι_act : ∀ (x : ↥(Δ.𝔫_neg)) (m : M),
      (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R x)) m = ⁅(x : 𝔤), m⁆ := by
    intro x m
    simp [ueaSubalgAction]

  have mul_act : ∀ (a b : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)) (m : M),
      (ueaSubalgAction Δ.𝔫_neg M (a * b)) m =
      (ueaSubalgAction Δ.𝔫_neg M a) ((ueaSubalgAction Δ.𝔫_neg M b) m) := by
    intro a b m
    show (ueaSubalgAction Δ.𝔫_neg M (a * b)) m = _
    rw [map_mul]
    rfl

  have one_act : ∀ (m : M), (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
    intro m; show (ueaSubalgAction Δ.𝔫_neg M 1) m = m; rw [map_one]; rfl

  have pow_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) (n : ℕ)
      (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      (ueaSubalgAction Δ.𝔫_neg M
        ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m ∈
        WeightSpace Δ M (μ - n • α) := by
    intro α hα n
    induction n with
    | zero => intro μ m hm; simp; simpa using hm
    | succ n ih =>
      intro μ m hm
      rw [pow_succ', mul_act]
      have hrw : μ - (n + 1) • α = (μ - n • α) - α := by
        simp [add_smul, sub_sub]
      rw [hrw]
      have hmid := ih μ m hm
      have : (ueaSubalgAction Δ.𝔫_neg M
          (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)))
          ((ueaSubalgAction Δ.𝔫_neg M
            ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m) =
        ⁅(↑(rd.negRootVec α hα) : 𝔤),
          (ueaSubalgAction Δ.𝔫_neg M
            ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m⁆ := ι_act _ _
      rw [this]
      exact single_shift α hα (μ - n • α) _ hmid


  haveI := rd.uea_nminus_noZeroDivisors
  haveI := rd.uea_nminus_nontrivial
  suffices key : ∀ (S : Finset (Δ.𝔥 →ₗ[R] R)), S ⊆ rd.posRoots →
      ∃ (u : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)),
        u ≠ 0 ∧
        (ueaSubalgAction Δ.𝔫_neg M u) v ∈
          WeightSpace Δ M (wt - ∑ α ∈ S, (c α) • α) by
    rw [hc]
    exact key rd.posRoots (Finset.Subset.refl _)
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_ne_zero, by rw [one_act]; simpa using hv⟩
  | @insert α₀ S₀ hα₀_notin ih =>
    intro hS
    have hS₀ : S₀ ⊆ rd.posRoots :=
      (Finset.subset_insert α₀ S₀).trans hS
    obtain ⟨u₀, hu₀_ne, hu₀_wt⟩ := ih hS₀


    have hα₀_mem : α₀ ∈ rd.posRoots := hS (Finset.mem_insert_self α₀ S₀)
    set u₁ := (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀
    refine ⟨u₁, ?_, ?_⟩
    ·
      exact mul_ne_zero (pow_ne_zero _ (rd.ι_negRootVec_ne_zero α₀ hα₀_mem)) hu₀_ne
    ·
      rw [Finset.sum_insert hα₀_notin]
      show (ueaSubalgAction Δ.𝔫_neg M u₁) v ∈ _
      change (ueaSubalgAction Δ.𝔫_neg M
        ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀)) v ∈ _
      rw [mul_act]


      have hrw : wt - (c α₀ • α₀ + ∑ α ∈ S₀, c α • α) =
          (wt - ∑ α ∈ S₀, c α • α) - c α₀ • α₀ := by
        simp [sub_sub, add_comm]
      rw [hrw]
      exact pow_shift α₀ hα₀_mem (c α₀) _ _ hu₀_wt






theorem IsVermaModule.highest_weight_module_is_quotient (hM : IsVermaModule Δ M wt)
    (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (hV : IsHighestWeightModule Δ V wt) :
    ∃ (η : M →ₗ⁅R, 𝔤⁆ V), Function.Surjective η := by

  obtain ⟨η, hη⟩ := hM.universal_map V hV.highestWeightVec hV.cartan_action hV.npos_action
  refine ⟨η, ?_⟩

  rw [← LieModuleHom.range_eq_top]

  have hv_in_range : hV.highestWeightVec ∈ η.range := ⟨hM.highestWeightVec, hη⟩

  have hsub : LieSubmodule.lieSpan R 𝔤 {hV.highestWeightVec} ≤ η.range :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
  rw [hV.generates] at hsub
  exact top_le_iff.mp hsub

theorem IsVermaModule.simpleQuotient_of_hwm (hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (_hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J)
    (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (hV : IsHighestWeightModule Δ V wt) :
    ∃ (π : V →ₗ⁅R, 𝔤⁆ (M ⧸ J)), Function.Surjective π := by

  obtain ⟨η, hη_surj⟩ := hM.highest_weight_module_is_quotient V hV

  have hker_ne_top : η.ker ≠ ⊤ := by
    intro h
    have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
    have hV_zero : ∀ v : V, v = 0 := fun v => by
      obtain ⟨m, rfl⟩ := hη_surj v; exact hzero m
    exact hV.hwv_ne_zero (hV_zero hV.highestWeightVec)

  have hker_le_J : η.ker ≤ J := hJ_max η.ker hker_ne_top


  have hker_sub : η.toLinearMap.ker ≤ (LieSubmodule.Quotient.mk' J).toLinearMap.ker := by
    intro m hm
    rw [LinearMap.mem_ker, LieModuleHom.coe_toLinearMap]
    exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hker_le_J hm)
  let f_lin : V →ₗ[R] (M ⧸ J) :=
    (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub).comp
      (η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm.toLinearMap
  have hf : ∀ m : M, f_lin (η m) = LieSubmodule.Quotient.mk' J m := fun m => by
    show (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η m)) = _
    change (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η.toLinearMap m)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl
  refine ⟨⟨f_lin, ?_⟩, ?_⟩
  ·
    intro x v; obtain ⟨m, rfl⟩ := hη_surj v
    change f_lin (⁅x, η m⁆) = ⁅x, f_lin (η m)⁆
    rw [← η.map_lie, hf, hf, (LieSubmodule.Quotient.mk' J).map_lie]
  ·
    intro q
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J q
    exact ⟨η m, hf m⟩


noncomputable def IsVermaModule.maxProperSubmodule (hM : IsVermaModule Δ M wt) :
    LieSubmodule R 𝔤 M :=
  sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤}


theorem IsVermaModule.le_maxProperSubmodule (hM : IsVermaModule Δ M wt)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤) :
    N ≤ hM.maxProperSubmodule :=
  le_sSup hN

noncomputable def IsVermaModule.simpleQuotient (hM : IsVermaModule Δ M wt) :
    Type u_mod :=
  M ⧸ hM.maxProperSubmodule

noncomputable instance IsVermaModule.simpleQuotient_addCommGroup (hM : IsVermaModule Δ M wt) :
    AddCommGroup hM.simpleQuotient :=
  inferInstanceAs (AddCommGroup (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_module (hM : IsVermaModule Δ M wt) :
    Module R hM.simpleQuotient :=
  inferInstanceAs (Module R (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_lieRingModule (hM : IsVermaModule Δ M wt) :
    LieRingModule 𝔤 hM.simpleQuotient :=
  inferInstanceAs (LieRingModule 𝔤 (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_lieModule (hM : IsVermaModule Δ M wt) :
    LieModule R 𝔤 hM.simpleQuotient :=
  inferInstanceAs (LieModule R 𝔤 (M ⧸ hM.maxProperSubmodule))











end VermaProperties

def vermaIdeal (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    RingCon (UniversalEnvelopingAlgebra R 𝔤) :=
  ringConGen (fun a b =>
    (∃ h : Δ.𝔥, a = UniversalEnvelopingAlgebra.ι R (h : 𝔤) ∧
               b = algebraMap R (UniversalEnvelopingAlgebra R 𝔤) (wt h)) ∨
    (∃ e : Δ.𝔫_pos, a = UniversalEnvelopingAlgebra.ι R (e : 𝔤) ∧ b = 0))

def VermaModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Type _ :=
  (vermaIdeal Δ wt).Quotient

instance VermaModule.instRing (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Ring (VermaModule Δ wt) :=
  inferInstanceAs (Ring (vermaIdeal Δ wt).Quotient)

instance VermaModule.instAddCommGroup (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    AddCommGroup (VermaModule Δ wt) :=
  inferInstanceAs (AddCommGroup (vermaIdeal Δ wt).Quotient)

instance VermaModule.instModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Module R (VermaModule Δ wt) :=
  ((vermaIdeal Δ wt).mk'.comp (algebraMap R (UniversalEnvelopingAlgebra R 𝔤))).toModule

def VermaModule.highestWeightVec (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    VermaModule Δ wt :=
  (vermaIdeal Δ wt).toQuotient 1

lemma liftQ_comp_quotKerEquiv_symm_apply
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f₁ : M₀ →ₗ[R] N₁) (hf₁ : Function.Surjective f₁)
    (f₂ : M₀ →ₗ[R] N₂) (h : f₁.ker ≤ f₂.ker) (m : M₀) :
    (f₁.ker.liftQ f₂ h) ((f₁.quotKerEquivOfSurjective hf₁).symm (f₁ m)) = f₂ m := by
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl

def lieModuleEquivOfSurjEqKer
    {M₀ V₁ V₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V₁] [Module R V₁] [LieRingModule 𝔤 V₁] [LieModule R 𝔤 V₁]
    [AddCommGroup V₂] [Module R V₂] [LieRingModule 𝔤 V₂] [LieModule R 𝔤 V₂]
    (η₁ : M₀ →ₗ⁅R,𝔤⁆ V₁) (hη₁ : Function.Surjective η₁)
    (η₂ : M₀ →ₗ⁅R,𝔤⁆ V₂) (hη₂ : Function.Surjective η₂)
    (hker : η₁.ker = η₂.ker) : V₁ ≃ₗ⁅R,𝔤⁆ V₂ := by
  have hker_sub : η₁.toLinearMap.ker = η₂.toLinearMap.ker :=
    congr_arg LieSubmodule.toSubmodule hker
  have h12 : η₁.toLinearMap.ker ≤ η₂.toLinearMap.ker := le_of_eq hker_sub
  have h21 : η₂.toLinearMap.ker ≤ η₁.toLinearMap.ker := le_of_eq hker_sub.symm

  let f_lin : V₁ →ₗ[R] V₂ :=
    (η₁.toLinearMap.ker.liftQ η₂.toLinearMap h12).comp
      (η₁.toLinearMap.quotKerEquivOfSurjective hη₁).symm.toLinearMap

  let g_lin : V₂ →ₗ[R] V₁ :=
    (η₂.toLinearMap.ker.liftQ η₁.toLinearMap h21).comp
      (η₂.toLinearMap.quotKerEquivOfSurjective hη₂).symm.toLinearMap

  have hf : ∀ m, f_lin (η₁ m) = η₂ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₁.toLinearMap hη₁ η₂.toLinearMap h12 m
  have hg : ∀ m, g_lin (η₂ m) = η₁ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₂.toLinearMap hη₂ η₁.toLinearMap h21 m
  exact LieModuleEquiv.mk
    { toLinearMap := f_lin
      map_lie' := by
        intro x v₁; obtain ⟨m, rfl⟩ := hη₁ v₁
        change f_lin (⁅x, η₁ m⁆) = ⁅x, f_lin (η₁ m)⁆
        rw [← η₁.map_lie, hf, hf, η₂.map_lie] }
    g_lin
    (fun v₁ => by
      obtain ⟨m, rfl⟩ := hη₁ v₁; change g_lin (f_lin (η₁ m)) = η₁ m; rw [hf, hg])
    (fun v₂ => by
      obtain ⟨m, rfl⟩ := hη₂ v₂; change f_lin (g_lin (η₂ m)) = η₂ m; rw [hg, hf])

lemma ker_ne_top_of_surj_irreducible
    {M₀ V : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (η : M₀ →ₗ⁅R,𝔤⁆ V) (hη : Function.Surjective η)
    (hirr : LieModule.IsIrreducible R 𝔤 V) :
    η.ker ≠ ⊤ := by
  intro h
  have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
  have hV : ∀ v : V, v = 0 := fun v => by obtain ⟨m, rfl⟩ := hη v; exact hzero m
  exact absurd (show (⊥ : LieSubmodule R 𝔤 V) = ⊤ by ext v; simp [hV v]) IsSimpleOrder.bot_ne_top

lemma ker_eq_unique_max_of_surj_irreducible
    {Δ : TriangularDecomposition R 𝔤}
    {M₀ : Type u_mod} [AddCommGroup M₀] [Module R M₀]
    [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    {wt : Δ.𝔥 →ₗ[R] R}
    (_hM : IsVermaModule Δ M₀ wt)
    {V : Type u_mod} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (η : M₀ →ₗ⁅R,𝔤⁆ V) (hη : Function.Surjective η)
    (hirr : LieModule.IsIrreducible R 𝔤 V)
    (J : LieSubmodule R 𝔤 M₀) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M₀), N ≠ ⊤ → N ≤ J) :
    η.ker = J := by
  apply le_antisymm
  ·
    exact hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr)
  ·

    rcases IsSimpleOrder.eq_bot_or_eq_top (LieSubmodule.map η J) with hbot | htop
    ·
      intro j hj
      have : η j ∈ LieSubmodule.map η J :=
        (LieSubmodule.mem_map (η j)).mpr ⟨j, hj, rfl⟩
      rw [hbot] at this; exact this
    ·
      exfalso; apply hJ_ne_top; rw [eq_top_iff]; intro m _
      have : η m ∈ LieSubmodule.map η J := htop ▸ trivial
      obtain ⟨j, hj, hjm⟩ := (LieSubmodule.mem_map (η m)).mp this
      have hmj : m - j ∈ η.ker := show η (m - j) = 0 by simp [hjm]
      have : m - j ∈ J :=
        hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr) hmj
      have := J.add_mem this hj; rwa [sub_add_cancel] at this


end
