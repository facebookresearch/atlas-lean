/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Lemma24


/-- The collection of affine opens of `Y` covers the whole space in the Grothendieck
topology of opens. -/
lemma affineOpens_coversTop (Y : Scheme.{u}) :
    (Opens.grothendieckTopology Y).CoversTop
      (fun (U : Y.affineOpens) => (U : TopologicalSpace.Opens Y)) := by
  intro V x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨W, homOfLE hWV, ⟨⟨W, hW⟩, ⟨𝟙 _⟩⟩, hxW⟩





end Lemma24

end
