/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation

open FiniteDimensional Module

/-- Convert the orthogonal-complement form of nondegeneracy
(`Garrett.BilinForm.IsNondegenerate'`) into Mathlib's `BilinForm.Nondegenerate`. -/
lemma IsNondegenerate'_to_Nondegenerate
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {B : LinearMap.BilinForm k V}
    (h : Garrett.BilinForm.IsNondegenerate' B) : B.Nondegenerate :=
  Garrett.IsNondegenerate'_to_Nondegenerate_inline h
