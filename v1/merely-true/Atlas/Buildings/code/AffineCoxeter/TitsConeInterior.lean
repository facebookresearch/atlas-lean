/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **interior** of the Tits cone $\mathcal U^\circ$: points which are $\sigma^*_w$-images of
strictly positive vectors $y > 0$, i.e. images of points in the open fundamental chamber. -/
def titsConeInterior (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {x | ∃ (y : B → ℝ), (∀ s, y s > 0) ∧
    ∃ (ws : List B), x = wordAction M ws y}

/-- The interior $\mathcal U^\circ$ is contained in $\mathcal U$. -/
theorem titsConeInterior_subset_titsCone (M : CoxeterMatrix B) :
    titsConeInterior M ⊆ titsConeSet M := by
  intro x hx
  obtain ⟨y, hy, ws, rfl⟩ := hx
  exact ⟨y, fun s => le_of_lt (hy s), ws, rfl⟩

/-- Characterization of $\mathcal U^\circ$: a point $x \in \mathcal U$ lies in the interior iff
**every** fundamental-domain representative of $x$ is in the open chamber $C$. This is essentially
the rigidity of fundamental-domain uniqueness lifted to the interior. -/
theorem titsCone_interior_iff_open_chamber (M : CoxeterMatrix B)
    (x : B → ℝ) (hx : x ∈ titsConeSet M) :
    x ∈ titsConeInterior M ↔
    ∀ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M →
      x = wordAction M ws y → y ∈ titsFundamentalChamber M := by
  constructor
  ·

    intro ⟨y₀, hy₀, ws₀, hx_eq⟩ ws y hy hxy
    have hy₀_cl : y₀ ∈ titsFundamentalClosure M := fun s => le_of_lt (hy₀ s)

    have heq : wordAction M ws y = wordAction M ws₀ y₀ := hxy.symm.trans hx_eq

    have hcomb : wordAction M (ws₀ ++ ws.reverse) y₀ = y := by
      rw [wordAction_append, ← heq, wordAction_reverse_cancel]

    have : y = y₀ := fundamental_domain_uniqueness M y y₀ hy hy₀_cl
      (ws₀ ++ ws.reverse) hcomb
    rw [this]
    exact hy₀
  ·
    intro h
    obtain ⟨y, hy, ws, rfl⟩ := hx
    exact ⟨y, h ws y hy rfl, ws, rfl⟩

end TitsCone
