/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace SheafTensorExact

/-- **Locally free** module of rank `n`: there is a finite set `S ⊆ R` generating
the unit ideal such that for each `f ∈ S`, the localization `M[f⁻¹]` is a free
`R[f⁻¹]`-module of rank `n`. This is the algebraic version of "locally free
sheaf trivializes on the principal open cover `{D(f) : f ∈ S}`". -/
def IsLocallyFree (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (n : ℕ) : Prop :=
  ∃ (S : Finset R), Ideal.span (S : Set R) = ⊤ ∧
    ∀ f ∈ S, Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ∧
      Module.finrank (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) = n

/-- A locally free module is flat: flatness is a local property, and free modules
over the localizations are flat. -/
theorem locally_free_isFlat (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)
    (hlf : IsLocallyFree R M n) :
    Module.Flat R M := by
  obtain ⟨S, hspan, hfree⟩ := hlf


  apply Module.flat_of_localized_span R M (S : Set R) hspan
  intro ⟨f, hf⟩
  have hfr := (hfree f hf).1

  haveI : Module.Free (Localization.Away f) (LocalizedModule.Away f M) := hfr

  haveI : Module.Flat (Localization.Away f) (LocalizedModule.Away f M) := inferInstance

  haveI : Module.Flat R (Localization.Away f) :=
    IsLocalization.flat (Localization.Away f) (Submonoid.powers f)

  exact Module.Flat.trans R (Localization.Away f) (LocalizedModule.Away f M)

/-- **Tensoring with a locally free module preserves exactness** (right tensor
version): if `F' → F → F''` is exact and `L` is locally free, then
`F' ⊗ L → F ⊗ L → F'' ⊗ L` is exact. -/
theorem locally_free_tensor_exact (R : Type*) [CommRing R]
    (L : Type*) [AddCommGroup L] [Module R L] (n : ℕ)
    (hlf : IsLocallyFree R L n)
    {F' F F'' : Type*}
    [AddCommGroup F'] [Module R F']
    [AddCommGroup F] [Module R F]
    [AddCommGroup F''] [Module R F'']
    (f : F' →ₗ[R] F) (g : F →ₗ[R] F'')
    (hex : Function.Exact f g) :
    Function.Exact (f.rTensor L) (g.rTensor L) := by
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact Module.Flat.rTensor_exact L hex

/-- **Tensoring with a locally free module preserves short exact sequences**:
`0 → F' → F → F'' → 0` exact and `L` locally free imply
`0 → F' ⊗ L → F ⊗ L → F'' ⊗ L → 0` is exact. -/
theorem locally_free_tensor_short_exact (R : Type*) [CommRing R]
    (L : Type*) [AddCommGroup L] [Module R L] (n : ℕ)
    (hlf : IsLocallyFree R L n)
    {F' F F'' : Type*}
    [AddCommGroup F'] [Module R F']
    [AddCommGroup F] [Module R F]
    [AddCommGroup F''] [Module R F'']
    (f : F' →ₗ[R] F) (g : F →ₗ[R] F'')
    (hinj : Function.Injective f)
    (hex : Function.Exact f g)
    (hsurj : Function.Surjective g) :
    Function.Injective (f.rTensor L) ∧
    Function.Exact (f.rTensor L) (g.rTensor L) ∧
    Function.Surjective (g.rTensor L) := by
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact ⟨Module.Flat.rTensor_preserves_injective_linearMap f hinj,
         Module.Flat.rTensor_exact L hex,
         LinearMap.rTensor_surjective L hsurj⟩

/-- Left-tensor version of `locally_free_tensor_exact`: tensoring on the left
with a locally free module preserves exactness. -/
theorem locally_free_lTensor_exact (R : Type*) [CommRing R]
    (L : Type*) [AddCommGroup L] [Module R L] (n : ℕ)
    (hlf : IsLocallyFree R L n)
    {F' F F'' : Type*}
    [AddCommGroup F'] [Module R F']
    [AddCommGroup F] [Module R F]
    [AddCommGroup F''] [Module R F'']
    (f : F' →ₗ[R] F) (g : F →ₗ[R] F'')
    (hex : Function.Exact f g) :
    Function.Exact (f.lTensor L) (g.lTensor L) := by
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact Module.Flat.lTensor_exact L hex

/-- **Invertible sheaves preserve exactness**: tensoring an exact sequence with
a line bundle (locally free of rank `1`) preserves exactness. This is the
algebraic shadow of the fact that twisting by `O(D)` is an exact functor. -/
theorem invertible_sheaf_tensor_exact (R : Type*) [CommRing R]
    (L : Type*) [AddCommGroup L] [Module R L]
    (hlf : IsLocallyFree R L 1)
    {F' F F'' : Type*}
    [AddCommGroup F'] [Module R F']
    [AddCommGroup F] [Module R F]
    [AddCommGroup F''] [Module R F'']
    (f : F' →ₗ[R] F) (g : F →ₗ[R] F'')
    (hex : Function.Exact f g) :
    Function.Exact (f.rTensor L) (g.rTensor L) :=
  locally_free_tensor_exact R L 1 hlf f g hex

end SheafTensorExact
