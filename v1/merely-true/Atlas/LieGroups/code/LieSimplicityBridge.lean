/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Submodule
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]
variable [Module (UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]

def LieSubmodule.ofUEASubmodule
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

theorem LieSubmodule.mem_ofUEASubmodule
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : Submodule (UniversalEnvelopingAlgebra R L) M) (m : M) :
    m ∈ LieSubmodule.ofUEASubmodule hcompat N ↔ m ∈ N :=
  Iff.rfl

theorem isSimpleOrder_submodule_of_isIrreducible
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    [hirr : LieModule.IsIrreducible R L M] :
    IsSimpleOrder (Submodule (UniversalEnvelopingAlgebra R L) M) := by
  haveI hnt : Nontrivial M :=
    (LieSubmodule.nontrivial_iff R L M).mp hirr.toNontrivial
  haveI : Nontrivial (Submodule (UniversalEnvelopingAlgebra R L) M) :=
    (Submodule.nontrivial_iff (UniversalEnvelopingAlgebra R L)).mpr hnt
  apply IsSimpleOrder.of_forall_eq_top
  intro N hN
  have h := hirr.eq_bot_or_eq_top (LieSubmodule.ofUEASubmodule hcompat N)
  rcases h with hbot | htop
  ·
    exfalso
    apply hN
    ext m
    simp only [Submodule.mem_bot]
    constructor
    · intro hm
      have hmem : m ∈ LieSubmodule.ofUEASubmodule hcompat N :=
        (LieSubmodule.mem_ofUEASubmodule hcompat N m).mpr hm
      rw [hbot] at hmem
      exact (LieSubmodule.mem_bot m).mp hmem
    · intro hm
      rw [hm]; exact N.zero_mem
  ·
    ext m
    simp only [Submodule.mem_top, iff_true]
    have hmem : m ∈ LieSubmodule.ofUEASubmodule hcompat N := by
      rw [htop]; exact LieSubmodule.mem_top m
    exact (LieSubmodule.mem_ofUEASubmodule hcompat N m).mp hmem

theorem LieModule.isSimpleModule_of_isIrreducible
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    [hirr : LieModule.IsIrreducible R L M] :
    IsSimpleModule (UniversalEnvelopingAlgebra R L) M where
  __ := isSimpleOrder_submodule_of_isIrreducible hcompat

end
