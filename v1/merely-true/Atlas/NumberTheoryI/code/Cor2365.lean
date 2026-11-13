/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.TensorProduct.Map

open TensorProduct LinearMap in
theorem tensor_rTensor_additive
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (A : Type*) [AddCommGroup A] [Module R A] :
    (LinearMap.rTensor A (0 : M →ₗ[R] N) = 0) ∧
    (∀ (f g : M →ₗ[R] N),
      LinearMap.rTensor A (f + g) = LinearMap.rTensor A f + LinearMap.rTensor A g) :=
  ⟨LinearMap.rTensor_zero A, LinearMap.rTensor_add A⟩
