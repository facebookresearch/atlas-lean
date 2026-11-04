/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Abelian.Basic

open CategoryTheory Limits MonoidalCategory

namespace SingularCohomology

/-- **Categorical exactness of the kernel inclusion in `ModuleCat`** (Section
28 helper for the cup product).  For any morphism `f : A ⟶ B` in
`ModuleCat R`, the underlying linear-map sequence
`kernel.ι f → f` is exact in the sense of `Function.Exact`: the image of
`kernel.ι f` coincides with the kernel of `f`.  This bridges Mathlib's
categorical `kernel.ι` with the concrete linear-algebra notion of
exactness used in the cohomology development. -/
lemma exact_kernel_ι_ModuleCat {R : Type} [CommRing R] {A B : ModuleCat.{0} R}
    (f : A ⟶ B) : Function.Exact (kernel.ι f).hom f.hom := by
  rw [LinearMap.exact_iff]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    rw [← ModuleCat.kernelIsoKer_hom_ker_subtype f]
    simp only [ModuleCat.hom_comp]
    exact ⟨(ModuleCat.kernelIsoKer f).inv.hom ⟨x, hx⟩, by simp⟩
  · rintro ⟨y, rfl⟩
    change (kernel.ι f ≫ f).hom y = (0 : kernel f ⟶ B).hom y
    rw [kernel.condition]

end SingularCohomology
