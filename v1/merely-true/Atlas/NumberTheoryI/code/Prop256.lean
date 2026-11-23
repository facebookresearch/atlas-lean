/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped RestrictedProduct
open Filter Set Topology

theorem proposition_25_6
    {ι : Type*}
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, WeaklyLocallyCompactSpace (X i)]
    (U : (i : ι) → Set (X i))
    (hU_open : ∀ i, IsOpen (U i))
    (hU_compact : ∀ᶠ i in cofinite, IsCompact (U i)) :
    WeaklyLocallyCompactSpace (Πʳ i, [X i, U i]) :=
  RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite hU_open hU_compact
