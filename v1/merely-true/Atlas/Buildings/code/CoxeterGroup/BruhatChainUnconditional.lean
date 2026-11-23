/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.BruhatSubexpression
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeUnconditional

set_option maxHeartbeats 400000

open StrongExchangeUnconditional

namespace CoxeterBruhat

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Chain property for the Bruhat order: assuming the Strong Exchange Condition
and the Reduced Sublist Property, any strict Bruhat inequality $v < w$ can be
refined to a chain $v = u_0 < u_1 < \cdots < u_{n+1} = w$ in which consecutive
elements differ by exactly one in length. -/
theorem bruhat_chain_property_unconditional
    (M : CoxeterMatrix B)
    (hSEC_full : StrongExchangeCondition M.toCoxeterSystem)
    (hRSP : ReducedSublistProperty M.toCoxeterSystem)
    {v w : M.Group} (hvw : BruhatLT M.toCoxeterSystem v w) :
    ∃ (n : ℕ) (f : Fin (n + 2) → M.Group),
      f ⟨0, by omega⟩ = v ∧
      f ⟨n + 1, by omega⟩ = w ∧
      ∀ (i : Fin (n + 1)),
        BruhatLT M.toCoxeterSystem
          (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧
        M.toCoxeterSystem.length (f ⟨i.val, by omega⟩) + 1 =
          M.toCoxeterSystem.length (f ⟨i.val + 1, by omega⟩) :=
  bruhat_chain_property M.toCoxeterSystem
    hSEC_full hRSP (strongExchangeForBruhat_unconditional M)
    hvw

end CoxeterBruhat
