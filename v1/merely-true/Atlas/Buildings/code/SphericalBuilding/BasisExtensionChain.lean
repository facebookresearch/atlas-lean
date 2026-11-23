/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnCommonApartment
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: any finite list of proper non-zero subspaces is simultaneously compatible
with some frame $F$ — i.e.\ admits a simultaneous adapted basis. -/
structure AdaptedBasisHyp where
  adapt : ∀ (subs : List (Submodule k (Vec k n))),
    (∀ V ∈ subs, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ F : Frame k n, ∀ V ∈ subs, F.IsCompatible k n V

/-- Wrap `AdaptedBasisHyp` as a `SimultaneousRefinementHyp` — they are the same property
phrased identically. -/
noncomputable def simultaneousRefinementOfAdapted
    (h : AdaptedBasisHyp k n) : SimultaneousRefinementHyp k n where
  refine_list := h.adapt

end GLnBuilding
