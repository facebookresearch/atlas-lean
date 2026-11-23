/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.EtaleAlgebras
import Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure

universe u v

noncomputable section EtaleAlgebraCharacterizations

open scoped TensorProduct
open EtaleAlgebra

variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]

lemma formallyUnramified_baseChange {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]
    [Algebra.FormallyUnramified K B]
    {Ω : Type*} [CommRing Ω] [Algebra K Ω] :
    Algebra.FormallyUnramified Ω (Ω ⊗[K] B) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro C _ _ I hI
  letI : Algebra K C := (algebraMap Ω C).comp (algebraMap K Ω) |>.toAlgebra
  haveI : IsScalarTower K Ω C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro f₁ f₂ he
  apply Algebra.TensorProduct.ext
  · ext
  · exact Algebra.FormallyUnramified.comp_injective I hI (by
      ext b; simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply]
      exact AlgHom.congr_fun he (1 ⊗ₜ b))

theorem sep_tensor_reduced (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsSeparable K L]
    (Ω : Type*) [Field Ω] [Algebra K Ω] : IsReduced (L ⊗[K] Ω) := by

  suffices h : IsReduced (Ω ⊗[K] L) from
    isReduced_of_injective
      (Algebra.TensorProduct.comm K L Ω).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm K L Ω).toRingEquiv.injective

  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hfg

  haveI : Algebra.IsIntegral K L := ⟨Algebra.IsSeparable.isIntegral K⟩
  haveI : Algebra.IsIntegral K B := Algebra.IsIntegral.of_injective B.val Subtype.val_injective
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B

  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI : Module.Finite K B := Algebra.IsIntegral.finite

  letI : Field B := (isField_of_isIntegral_of_isField' (Field.toIsField K)).toField

  haveI : Algebra.IsSeparable K B := Algebra.IsSeparable.of_algHom K L B.val
  haveI : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_isSeparable K B

  haveI : Algebra.FormallyUnramified Ω (Ω ⊗[K] B) := formallyUnramified_baseChange
  haveI : Module.Finite Ω (Ω ⊗[K] B) := Module.Finite.base_change K Ω B
  haveI : Algebra.EssFiniteType Ω (Ω ⊗[K] B) :=
    Algebra.EssFiniteType.of_finiteType Ω (Ω ⊗[K] B)

  exact Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[K] B)

theorem isReduced_pi_tensor (K : Type*) [Field K] (ι : Type) [Fintype ι]
    (F : ι → Type) [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    [∀ i, Algebra.IsSeparable K (F i)]
    (Ω : Type*) [Field Ω] [Algebra K Ω] : IsReduced ((∀ i, F i) ⊗[K] Ω) := by
  classical

  let e := (Algebra.TensorProduct.comm K (∀ i, F i) Ω).toRingEquiv.trans
    (Algebra.TensorProduct.piRight K Ω Ω F).toRingEquiv

  haveI : ∀ i, IsReduced (Ω ⊗[K] F i) := fun i => by
    haveI := sep_tensor_reduced K (F i) Ω
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm K (F i) Ω).toRingEquiv.symm.toRingHom
      (Algebra.TensorProduct.comm K (F i) Ω).toRingEquiv.symm.injective

  exact isReduced_of_injective e.toRingHom e.injective


end EtaleAlgebraCharacterizations

noncomputable section EtaleFieldExtensions

open scoped TensorProduct
open Polynomial IntermediateField EtaleAlgebra

end EtaleFieldExtensions
