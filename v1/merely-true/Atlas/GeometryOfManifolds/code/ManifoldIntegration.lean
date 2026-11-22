/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.Integration
import Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open DifferentialFormSpace

open scoped Manifold ContDiff


/-- A smooth manifold $M$ is compact and oriented: it carries a compact topology together with
an (abstractly recorded) orientation, the standard hypothesis under which Stokes-type integration
is defined. -/
class IsCompactOrientedManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] : Prop where
  compact : CompactSpace M
  oriented : True

/-- Projects out the underlying `CompactSpace` structure of a compact oriented manifold. -/
theorem IsCompactOrientedManifold.compactSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (h : IsCompactOrientedManifold I M) : CompactSpace M :=
  h.compact




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsCompactOrientedManifold I M]




