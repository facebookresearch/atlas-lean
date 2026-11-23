/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.LeftExact

universe u

theorem corollary_23_60
    {R : Type u} [CommRing R]
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (_hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (LinearMap.lcomp R A g) ∧
    Function.Exact (LinearMap.lcomp R A g) (LinearMap.lcomp R A f) :=
  ⟨LinearMap.lcomp_injective_of_surjective g hg,
   LinearMap.exact_lcomp_of_exact_of_surjective A hfg hg⟩
