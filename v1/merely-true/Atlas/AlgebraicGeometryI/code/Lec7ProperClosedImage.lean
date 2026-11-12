/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact

section Lemma19

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Lec 7 / Lem 19: a closed subset of a compact space is compact. -/
theorem closedSubset_compactSpace [CompactSpace X] {Z : Set X} (hZ : IsClosed Z) :
    CompactSpace Z :=
  isCompact_iff_compactSpace.mp hZ.isCompact

/-- Lec 7: the image of a closed set under a continuous map from a
compact space to a Hausdorff space is closed (topological analogue of
"proper image closed"). -/
theorem isClosed_image_of_complete [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {Z : Set X} (hZ : IsClosed Z) :
    IsClosed (f '' Z) :=
  hf.isProperMap.isClosedMap Z hZ

/-- The range of a continuous map from a compact space to a Hausdorff
space is closed. -/
theorem isClosed_range_of_complete [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) :
    IsClosed (Set.range f) := by
  rw [← Set.image_univ]
  exact isClosed_image_of_complete hf isClosed_univ

/-- The product of two compact spaces is compact. -/
theorem prod_compactSpace [CompactSpace X] [CompactSpace Y] : CompactSpace (X × Y) :=
  inferInstance

end Lemma19
