/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.CellCoverProof
import Atlas.Buildings.code.BNPair.ParabolicDefs

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace BNPair

/-- Unconditional cell-cover restatement: every $g \in G$ lies in some Bruhat cell $C(w) = BwB$,
i.e. $G = \bigcup_{w \in W} BwB$. -/
theorem cell_cover_unconditional (bp : BNPair G M) (ax : BNPairAxioms bp) :
    ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w :=
  CellCover.cell_cover_from_bnpair bp ax

end BNPair
