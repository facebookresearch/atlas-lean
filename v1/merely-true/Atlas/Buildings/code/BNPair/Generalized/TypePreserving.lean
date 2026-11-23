/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Generalized.Defs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

namespace GeneralizedBNPair

variable {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]
variable {Gt : Type*} [Group Gt] {M : CoxeterMatrix B_idx}
variable (gbp : GeneralizedBNPair Gt M)

/-- The enlarged torus is contained in the enlarged Borel: $\tilde T = \tilde B \cap \tilde N
\leq \tilde B$. -/
theorem Tt_le_Bt : gbp.Tt ≤ gbp.Bt := by
  rw [gbp.Tt_eq]
  exact inf_le_left


/-- An element $t \in \tilde G$ acts trivially on types of the standard apartment:
for every simple reflection $s$ and every $N$-lift $n$ of $s$, the conjugate
$t n t^{-1}$ is again an $N$-lift of the *same* simple reflection $s$. -/
def ActsTriviallyOnTypes (t : Gt) : Prop :=
  ∀ (s : B_idx) (n : gbp.strictBNPair.N),
    gbp.strictBNPair.π n = M.toCoxeterSystem.simple s →
    ∃ (n' : gbp.strictBNPair.N),
      gbp.strictBNPair.π n' = M.toCoxeterSystem.simple s ∧
      ((n' : gbp.G) : Gt) = t * ((n : gbp.G) : Gt) * t⁻¹

/-- $g \in \tilde G$ preserves types on the base chamber: synonym for
`ActsTriviallyOnTypes g`, packaged to clarify the geometric meaning. -/
def PreservesTypesOnBaseChbr (g : Gt) : Prop :=
  gbp.ActsTriviallyOnTypes g

/-- $g \in \tilde G$ preserves types on the chamber $h \cdot C_0$: this means the
conjugate $h^{-1} g h$ preserves types on the base chamber $C_0$. -/
def PreservesTypesOnChamber (g h : Gt) : Prop :=
  gbp.PreservesTypesOnBaseChbr (h⁻¹ * g * h)



end GeneralizedBNPair
