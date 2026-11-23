/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.TensorProduct.RightExactness

theorem tensor_rTensor_rightExact
    {R : Type*} [CommRing R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (A : Type*) [AddCommGroup A] [Module R A]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.rTensor A f) (LinearMap.rTensor A g) ∧
    Function.Surjective (LinearMap.rTensor A g) :=
  ⟨rTensor_exact A hfg hg, LinearMap.rTensor_surjective A hg⟩
