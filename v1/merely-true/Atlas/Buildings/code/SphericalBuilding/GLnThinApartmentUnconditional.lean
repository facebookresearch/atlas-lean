/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnB0Cascade

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Unconditional thin-apartment hypothesis for the $\mathrm{GL}_n$ building: for $n \geq 2$
it follows from the cascade of B0 lemmas, and for $n < 2$ it holds vacuously since no panels exist. -/
noncomputable def thinApartmentHypUnconditional : ThinApartmentHyp k n := by
  by_cases hn : 2 ≤ n
  · exact thinApartmentHypComposed k n hn
  · push_neg at hn
    exact ⟨fun F panel hcompat hlen => by
      exfalso
      have hpos : panel.chain.length ≥ 1 := List.length_pos_of_ne_nil panel.chain_nonempty
      omega⟩

end GLnBuilding
