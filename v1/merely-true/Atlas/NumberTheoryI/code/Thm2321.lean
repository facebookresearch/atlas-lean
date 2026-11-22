/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Atlas.NumberTheoryI.code.GroupCohomology

noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

theorem homology_long_exact_sequence_exact₁
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    {i j : ℕ} (hij : j + 1 = i) :
    (groupHomology.mapShortComplex₁ hX hij).Exact :=
  groupHomology.mapShortComplex₁_exact hX hij

end GroupCohomology
