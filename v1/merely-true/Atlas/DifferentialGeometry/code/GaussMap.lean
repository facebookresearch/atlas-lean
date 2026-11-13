/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.Manifolds
import Mathlib.Topology.Connected.Basic

noncomputable section

open Metric Set

namespace GaussMap

variable {n : ℕ}

abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1



end GaussMap
