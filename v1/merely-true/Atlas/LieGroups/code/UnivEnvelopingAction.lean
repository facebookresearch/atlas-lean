/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.ContinuousRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Killing
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

noncomputable section

namespace UnivEnvelopingAction

section ExtendToUEA

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {V : Type*} [AddCommGroup V] [Module R V]

def extendToUEA (f : L →ₗ⁅R⁆ Module.End R V) :
    UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V :=
  UniversalEnvelopingAlgebra.lift R f

end ExtendToUEA

abbrev CenterUEA (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    Subalgebra R (UniversalEnvelopingAlgebra R L) :=
  Subalgebra.center R (UniversalEnvelopingAlgebra R L)

theorem centerUEA_comm (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (a b : CenterUEA R L) : a * b = b * a := by
  ext
  simp only [Subalgebra.coe_mul]
  exact (Subalgebra.mem_center_iff.mp a.2 (b : UniversalEnvelopingAlgebra R L)).symm

section InfinitesimalCharacter

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]

def ActsByScalar {V : Type*} [AddCommGroup V] [Module R V]
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V)
    (z : UniversalEnvelopingAlgebra R L) (c : R) : Prop :=
  φ z = c • LinearMap.id

structure InfinitesimalCharacter where
  toAlgHom : CenterUEA R L →ₐ[R] R

def InfinitesimalCharacter.apply (χ : InfinitesimalCharacter R L) (z : CenterUEA R L) : R :=
  χ.toAlgHom z

end InfinitesimalCharacter

section CenterActsByScalar

variable (R : Type*) [Field R] [IsAlgClosed R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]

theorem center_acts_by_scalar
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module (UniversalEnvelopingAlgebra R L) V]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) V]
    [IsSimpleModule (UniversalEnvelopingAlgebra R L) V]
    [Nontrivial V]
    [FiniteDimensional R V]
    (z : CenterUEA R L) :
    ∃ c : R, ∀ v : V, (z : UniversalEnvelopingAlgebra R L) • v = c • v := by


  let T : Module.End R V :=
  { toFun := fun v => (z : UniversalEnvelopingAlgebra R L) • v
    map_add' := fun v w => smul_add _ v w
    map_smul' := fun r v => by
      simp only [RingHom.id_apply]
      rw [show r • v = (algebraMap R (UniversalEnvelopingAlgebra R L) r) • v from by
            rw [Algebra.algebraMap_eq_smul_one, smul_assoc]; simp,
          show r • ((z : UniversalEnvelopingAlgebra R L) • v) =
               (algebraMap R (UniversalEnvelopingAlgebra R L) r) •
                 ((z : UniversalEnvelopingAlgebra R L) • v) from by
            rw [Algebra.algebraMap_eq_smul_one, smul_assoc]; simp]
      rw [← mul_smul, ← mul_smul]
      congr 1
      exact (Subalgebra.mem_center_iff.mp z.2 _).symm }

  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T

  let W : Submodule (UniversalEnvelopingAlgebra R L) V :=
  { carrier := {v : V | (z : UniversalEnvelopingAlgebra R L) • v = μ • v}
    add_mem' := fun {a b} (ha : _ • a = μ • a) (hb : _ • b = μ • b) => by
      show (z : UniversalEnvelopingAlgebra R L) • (a + b) = μ • (a + b)
      rw [smul_add, smul_add, ha, hb]
    zero_mem' := by simp
    smul_mem' := fun a v (hv : (z : UniversalEnvelopingAlgebra R L) • v = μ • v) => by
      show (z : UniversalEnvelopingAlgebra R L) • (a • v) = μ • (a • v)
      rw [← mul_smul, (Subalgebra.mem_center_iff.mp z.2 a).symm, mul_smul, hv, smul_comm] }

  have hW_ne_bot : W ≠ ⊥ := by
    intro h
    have hT_eig : T.eigenspace μ ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
    apply hT_eig
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have : v ∈ W := hv
    rw [h] at this
    exact (Submodule.mem_bot _).mp this

  have hW_top : W = ⊤ := by
    rcases eq_bot_or_eq_top W with h | h
    · exact absurd h hW_ne_bot
    · exact h

  exact ⟨μ, fun v => by
    have : v ∈ W := by rw [hW_top]; exact Submodule.mem_top
    exact this⟩

end CenterActsByScalar

section Casimir

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure IsKillingDualBasis (b d : ι → L) : Prop where
  orthonormal : ∀ i j : ι, killingForm R L (b i) (d j) = if i = j then 1 else 0
  expand_b : ∀ y : L, y = ∑ i : ι, (killingForm R L y (d i)) • (b i)
  expand_d : ∀ y : L, y = ∑ i : ι, (killingForm R L (b i) y) • (d i)

def casimirElement (b d : ι → L) : UniversalEnvelopingAlgebra R L :=
  ∑ i : ι, (UniversalEnvelopingAlgebra.ι R (b i)) * (UniversalEnvelopingAlgebra.ι R (d i))

theorem casimirElement_central (b d : ι → L)
    (hbd : IsKillingDualBasis R L b d) :
    casimirElement R L b d ∈ Subalgebra.center R (UniversalEnvelopingAlgebra R L) := by

  have comm_gen : ∀ x : L, UniversalEnvelopingAlgebra.ι R x * casimirElement R L b d =
                            casimirElement R L b d * UniversalEnvelopingAlgebra.ι R x := by
    intro x
    suffices h : UniversalEnvelopingAlgebra.ι R x * casimirElement R L b d -
                 casimirElement R L b d * UniversalEnvelopingAlgebra.ι R x = 0 by
      exact sub_eq_zero.mp h
    show UniversalEnvelopingAlgebra.ι R x *
      (∑ i : ι, UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R (d i)) -
      (∑ i : ι, UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R (d i)) *
      UniversalEnvelopingAlgebra.ι R x = 0
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

    have comm_term : ∀ i : ι,
        (UniversalEnvelopingAlgebra.ι R x : UniversalEnvelopingAlgebra R L) *
         (UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R (d i)) -
        (UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R (d i)) *
         UniversalEnvelopingAlgebra.ι R x =
        UniversalEnvelopingAlgebra.ι R ⁅x, b i⁆ * UniversalEnvelopingAlgebra.ι R (d i) +
        UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R ⁅x, d i⁆ := by
      intro i
      have hxb : (UniversalEnvelopingAlgebra.ι R ⁅x, b i⁆ : UniversalEnvelopingAlgebra R L) =
        UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R (b i) -
        UniversalEnvelopingAlgebra.ι R (b i) * UniversalEnvelopingAlgebra.ι R x := by
        rw [LieHom.map_lie, Ring.lie_def]
      have hxd : (UniversalEnvelopingAlgebra.ι R ⁅x, d i⁆ : UniversalEnvelopingAlgebra R L) =
        UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R (d i) -
        UniversalEnvelopingAlgebra.ι R (d i) * UniversalEnvelopingAlgebra.ι R x := by
        rw [LieHom.map_lie, Ring.lie_def]
      set α := (UniversalEnvelopingAlgebra.ι R x : UniversalEnvelopingAlgebra R L)
      set β := (UniversalEnvelopingAlgebra.ι R (b i) : UniversalEnvelopingAlgebra R L)
      set γ := (UniversalEnvelopingAlgebra.ι R (d i) : UniversalEnvelopingAlgebra R L)
      rw [show UniversalEnvelopingAlgebra.ι R ⁅x, b i⁆ = α * β - β * α from hxb]
      rw [show UniversalEnvelopingAlgebra.ι R ⁅x, d i⁆ = α * γ - γ * α from hxd]
      noncomm_ring
    simp_rw [comm_term, Finset.sum_add_distrib]


    have hexp_b : ∀ i, (UniversalEnvelopingAlgebra.ι R (⁅x, b i⁆) :
        UniversalEnvelopingAlgebra R L) =
        ∑ j : ι, (killingForm R L ⁅x, b i⁆ (d j)) •
          (UniversalEnvelopingAlgebra.ι R (b j) : UniversalEnvelopingAlgebra R L) := by
      intro i; conv_lhs => rw [hbd.expand_b ⁅x, b i⁆]; simp only [map_sum, map_smul]
    have hexp_d : ∀ i, (UniversalEnvelopingAlgebra.ι R (⁅x, d i⁆) :
        UniversalEnvelopingAlgebra R L) =
        ∑ j : ι, (killingForm R L (b j) ⁅x, d i⁆) •
          (UniversalEnvelopingAlgebra.ι R (d j) : UniversalEnvelopingAlgebra R L) := by
      intro i; conv_lhs => rw [hbd.expand_d ⁅x, d i⁆]; simp only [map_sum, map_smul]
    simp_rw [hexp_b, Finset.sum_mul, smul_mul_assoc]
    simp_rw [hexp_d, Finset.mul_sum, mul_smul_comm]

    rw [Finset.sum_comm (f := fun i j => ((killingForm R L) (b j)) ⁅x, d i⁆ • _)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro i _
    rw [← add_smul]

    have : killingForm R L ⁅x, b j⁆ (d i) + killingForm R L (b j) ⁅x, d i⁆ = 0 := by
      unfold killingForm
      rw [← LieModule.traceForm_apply_lie_apply R L L (b j) x (d i)]
      have h : ⁅b j, x⁆ = -⁅x, b j⁆ := by rw [← lie_skew x (b j), neg_neg]
      rw [h, map_neg, LinearMap.neg_apply, add_neg_cancel]
    rw [this, zero_smul]


  rw [Subalgebra.mem_center_iff]
  intro u
  let S := Subalgebra.centralizer R
    ({casimirElement R L b d} : Set (UniversalEnvelopingAlgebra R L))
  let ι' : L →ₗ⁅R⁆ S := {
    toFun := fun x => ⟨UniversalEnvelopingAlgebra.ι R x, by
      change UniversalEnvelopingAlgebra.ι R x ∈ Set.centralizer {casimirElement R L b d}
      rw [Set.mem_centralizer_iff]
      intro g hg; simp at hg; rw [hg]; exact (comm_gen x).symm⟩
    map_add' := fun x y => by ext; simp [map_add]
    map_smul' := fun r x => by ext; simp [map_smul]
    map_lie' := fun {x y} => by
      ext; change (UniversalEnvelopingAlgebra.ι R) ⁅x, y⁆ = _
      rw [LieHom.map_lie]; simp only [Ring.lie_def, Subalgebra.coe_sub, Subalgebra.coe_mul]
  }
  let φ : UniversalEnvelopingAlgebra R L →ₐ[R] S := UniversalEnvelopingAlgebra.lift R ι'

  have hid : S.val.comp φ = AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
    have : (UniversalEnvelopingAlgebra.lift R).symm (S.val.comp φ) =
           (UniversalEnvelopingAlgebra.lift R).symm (AlgHom.id R _) := by
      ext x
      change S.val (φ (UniversalEnvelopingAlgebra.ι R x)) =
             (AlgHom.id R _) (UniversalEnvelopingAlgebra.ι R x)
      simp only [AlgHom.coe_id, id_eq]
      rw [show φ (UniversalEnvelopingAlgebra.ι R x) = ι' x from
            UniversalEnvelopingAlgebra.lift_ι_apply R ι' x]
      rfl
    exact (UniversalEnvelopingAlgebra.lift R).symm.injective this

  have hu_eq : u = S.val (φ u) := by
    have := AlgHom.congr_fun hid u; simp [AlgHom.comp_apply] at this; exact this.symm
  rw [hu_eq]
  have hφu_mem : (φ u : UniversalEnvelopingAlgebra R L) ∈
                 Set.centralizer ({casimirElement R L b d} : Set _) := (φ u).2
  rw [Set.mem_centralizer_iff] at hφu_mem
  exact (hφu_mem (casimirElement R L b d) (Set.mem_singleton _)).symm

end Casimir

end UnivEnvelopingAction

end
