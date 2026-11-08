/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ZPlusModules

/-- Lemma 2.8.5 (EGNO). An indecomposable exact `ℤ₊`-module over a `ℤ₊`-ring is irreducible.
This delegates to the implementation in `ZPlusModule.lemma_2_8_5`. -/
theorem Lemma_2_8_5
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ZPlusRing ι}
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (M : ZPlusModule R κ)
    (hindec : M.IsIndecomposable) (hexact : M.IsExact) :
    M.IsIrreducible :=
  M.lemma_2_8_5 hindec hexact
