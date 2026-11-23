/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Classical
open Finset AffineSubspace

namespace BeckTheorem

/-- An affine subspace `L ⊆ ℝ²` is a line iff its direction has dimension 1. -/
def IsLine (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The number of points of the finite set `E ⊂ ℝ²` lying on the line `L`. -/
noncomputable def pointsOnLine (E : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (E.filter (· ∈ (L : Set (EuclideanSpace ℝ (Fin 2))))).card

/-- The set of lines determined by `E`: lines that contain at least two points of `E`. -/
def determinedLines (E : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | IsLine L ∧ 2 ≤ pointsOnLine E L}

/-- The set of lines through `x ∈ ℝ²` which are determined by `E`, i.e. pass through
`x` and at least one other point of `E`. -/
noncomputable def linesThrough (E : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | IsLine L ∧ x ∈ (L : Set (EuclideanSpace ℝ (Fin 2))) ∧ 2 ≤ pointsOnLine E L}








end BeckTheorem
