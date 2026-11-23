/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SeparatedHausdorff

/-- Complex points of a scheme `X`: morphisms `Spec ℂ → X`. -/
def complexPoints (X : Scheme) : Type _ :=
  (Spec (CommRingCat.of ℂ)) ⟶ X






end SeparatedHausdorff
