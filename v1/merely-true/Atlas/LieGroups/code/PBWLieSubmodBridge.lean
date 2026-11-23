/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

section AlgHomExt

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem UniversalEnvelopingAlgebra.algHom_ext' {A : Type*} [Ring A] [Algebra R A]
    {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h : ∀ x : L,
      g₁ (UniversalEnvelopingAlgebra.ι R x) = g₂ (UniversalEnvelopingAlgebra.ι R x)) :
    g₁ = g₂ := by
  have h1 := (UniversalEnvelopingAlgebra.lift R).apply_symm_apply g₁
  have h2 := (UniversalEnvelopingAlgebra.lift R).apply_symm_apply g₂
  rw [← h1, ← h2]; congr 1; ext x
  have := h x; rw [← h1, ← h2] at this; simpa using this

end AlgHomExt

section LieSubmoduleBridge

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]
variable [Module (UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]

def LieSubmodule.preservingSubalgebra (N : LieSubmodule R L M) :
    Subalgebra R (UniversalEnvelopingAlgebra R L) where
  carrier := {u | ∀ m ∈ N, u • m ∈ N}
  mul_mem' {a b} ha hb m hm := by rw [mul_smul]; exact ha _ (hb _ hm)
  one_mem' m hm := by simp [hm]
  add_mem' {a b} ha hb m hm := by rw [add_smul]; exact N.add_mem (ha _ hm) (hb _ hm)
  zero_mem' m hm := by simp [N.zero_mem]
  algebraMap_mem' r m hm := by rw [algebraMap_smul]; exact N.smul_mem r hm

set_option linter.unusedSectionVars false in
theorem LieSubmodule.preservingSubalgebra_eq_top
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : LieSubmodule R L M) :
    N.preservingSubalgebra = ⊤ := by
  rw [eq_top_iff]; intro u _
  let S := N.preservingSubalgebra
  let ιS : L →ₗ⁅R⁆ S :=
    { toFun := fun x => ⟨UniversalEnvelopingAlgebra.ι R x, fun m hm => by
        rw [← hcompat]; exact N.lie_mem hm⟩
      map_add' := fun x y => by ext; simp [map_add]
      map_smul' := fun r x => by ext; simp [map_smul]
      map_lie' := fun {x y} => by
        ext; simp [LieRing.of_associative_ring_bracket] }
  let Ψ := UniversalEnvelopingAlgebra.lift R ιS
  have hΨ : S.val.comp Ψ = AlgHom.id R _ :=
    UniversalEnvelopingAlgebra.algHom_ext' (fun x => by
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, Subalgebra.coe_val, Ψ,
        UniversalEnvelopingAlgebra.lift_ι_apply, ιS]
      rfl)
  have : S.val (Ψ u) = u := AlgHom.congr_fun hΨ u
  rw [← this]; exact (Ψ u).2

def LieSubmodule.toUEASubmodule
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : LieSubmodule R L M) : Submodule (UniversalEnvelopingAlgebra R L) M where
  carrier := N.carrier
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' u m hm := by
    have hu : u ∈ N.preservingSubalgebra :=
      (N.preservingSubalgebra_eq_top hcompat) ▸ trivial
    exact hu m hm

theorem LieSubmodule.mem_toUEASubmodule
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : LieSubmodule R L M) (m : M) :
    m ∈ N.toUEASubmodule hcompat ↔ m ∈ N :=
  Iff.rfl

theorem LieSubmodule.toUEASubmodule_bot
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
    (⊥ : LieSubmodule R L M).toUEASubmodule hcompat = ⊥ := by
  ext m
  simp only [LieSubmodule.mem_toUEASubmodule, LieSubmodule.mem_bot, Submodule.mem_bot]

theorem LieSubmodule.toUEASubmodule_top
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
    (⊤ : LieSubmodule R L M).toUEASubmodule hcompat = ⊤ := by
  ext m
  simp only [LieSubmodule.mem_toUEASubmodule, LieSubmodule.mem_top, Submodule.mem_top]

def LieSubmodule.ofUEASubmodule'
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : Submodule (UniversalEnvelopingAlgebra R L) M) : LieSubmodule R L M where
  carrier := N.carrier
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' r m hm := by
    have h : (algebraMap R (UniversalEnvelopingAlgebra R L) r) • m ∈ N :=
      N.smul_mem (algebraMap R (UniversalEnvelopingAlgebra R L) r) hm
    rwa [algebraMap_smul] at h
  lie_mem {x m} hm := by
    rw [hcompat x m]
    exact N.smul_mem _ hm

theorem LieSubmodule.toUEASubmodule_ofUEASubmodule'
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : Submodule (UniversalEnvelopingAlgebra R L) M) :
    (LieSubmodule.ofUEASubmodule' hcompat N).toUEASubmodule hcompat = N := by
  ext m; rfl

end LieSubmoduleBridge

end
