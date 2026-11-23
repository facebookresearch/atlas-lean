/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Def2213
import Atlas.NumberTheoryI.code.GlobalCFT
import Atlas.NumberTheoryI.code.Prop229

noncomputable section

open scoped NumberField
open GlobalCFT

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayClassChar.IsPrimitive {m : Modulus K} (chi : RayClassChar K m) : Prop :=
  ∀ (m' : Modulus K) (h : m'.dvd m) (chi' : RayClassChar K m'),
    IsInducedBy K m' m h chi' chi → m' = m



theorem isEquiv_kernel_of_induced
    {m m' : Modulus K} (chi : RayClassChar K m) (chi' : RayClassChar K m')
    (h : m'.dvd m)
    (hind : IsInducedBy K m' m h chi' chi) :
    chi.kernelCongruenceSubgroup.IsEquiv chi'.kernelCongruenceSubgroup := by


  have hmapOfDvd_eq : ∀ (x : FracIdealsCoprime K m),
      RayClassGroup.mapOfDvd h (toRayClass K m x) =
        toRayClass K m' (FracIdealsCoprime.inclusion K m' m h x) := by
    intro x
    show QuotientGroup.map _ _ _ _ ((QuotientGroup.mk' _) x) = (QuotientGroup.mk' _) _
    rw [QuotientGroup.map_mk']; rfl

  have hincl_subtype : ∀ (x : FracIdealsCoprime K m),
      ((FracIdealsCoprime_subgroup K m').subtype
        (FracIdealsCoprime.inclusion K m' m h x) : (FracIdeal K)ˣ) =
      (FracIdealsCoprime_subgroup K m).subtype x := by
    intro x; rfl

  have hker_iff : ∀ (x : FracIdealsCoprime K m),
      x ∈ chi.kernelSubgroup ↔
        FracIdealsCoprime.inclusion K m' m h x ∈ chi'.kernelSubgroup := by
    intro x
    simp only [RayClassChar.kernelSubgroup, Subgroup.mem_comap, MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [← hmapOfDvd_eq]
      rw [IsInducedBy] at hind
      rw [hind, MonoidHom.comp_apply] at hx
      exact hx
    · intro hx'
      rw [IsInducedBy] at hind
      rw [hind, MonoidHom.comp_apply, hmapOfDvd_eq]
      exact hx'

  unfold CongruenceSubgroupPair.IsEquiv CongruenceSubgroupPair.toAmbientSubgroup
  simp only [RayClassChar.kernelCongruenceSubgroup]
  ext I
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  ·
    rintro ⟨hIm, ⟨J', hJ'_ker, hJ'_eq⟩⟩
    refine ⟨FracIdealsCoprime_subgroup_le K m' m h hIm, ?_⟩
    refine ⟨⟨I, hIm⟩, ?_, rfl⟩


    have hJ'_eq_incl : J' = FracIdealsCoprime.inclusion K m' m h ⟨I, hIm⟩ := by
      have := hincl_subtype ⟨I, hIm⟩
      exact Subtype.val_injective (hJ'_eq.trans this.symm)
    exact (hker_iff ⟨I, hIm⟩).mpr (hJ'_eq_incl ▸ hJ'_ker)
  ·
    rintro ⟨hIm', ⟨J, hJ_ker, hJ_eq⟩⟩
    have hIm : I ∈ FracIdealsCoprime_subgroup K m := by
      rw [← hJ_eq]; exact J.2
    refine ⟨hIm, ?_⟩
    refine ⟨⟨I, FracIdealsCoprime_subgroup_le K m' m h hIm⟩, ?_, rfl⟩


    have hincl_eq : FracIdealsCoprime.inclusion K m' m h J =
        ⟨I, FracIdealsCoprime_subgroup_le K m' m h hIm⟩ := by
      apply Subtype.val_injective
      exact hJ_eq
    rw [← hincl_eq]
    exact (hker_iff J).mp hJ_ker






end RayClassField
