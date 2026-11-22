/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace BNPair

/-- The $(P, Q)$-double coset of $g$ in $G$: the set $PgQ = \{pgq : p \in P,\ q \in Q\}$. -/
def doubleCoset (P Q : Set G) (g : G) : Set G :=
  { x : G | ∃ p ∈ P, ∃ q ∈ Q, x = p * g * q }

/-- The $(P_{S_1}, P_{S_2})$-double coset of $g$: $P_{S_1} \cdot g \cdot P_{S_2}$. -/
def parabolicDoubleCoset (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) (g : G) : Set G :=
  doubleCoset (bp.standardParabolic S₁) (bp.standardParabolic S₂) g

/-- The Weyl-side $(W_{S_1}, W_{S_2})$-double coset of $w \in W$:
$W_{S_1} \cdot w \cdot W_{S_2} \subseteq W$. -/
def weylDoubleCoset (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) (w : M.Group) : Set M.Group :=
  { x : M.Group | ∃ w₁ ∈ (bp.parabolicSubgroupW S₁ : Set M.Group),
    ∃ w₂ ∈ (bp.parabolicSubgroupW S₂ : Set M.Group), x = w₁ * w * w₂ }

/-- The set of all $(P_{S_1}, P_{S_2})$-double cosets in $G$, i.e. $P_{S_1} \backslash G / P_{S_2}$
as a collection of subsets of $G$. -/
def parabolicDoubleCosets (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) : Set (Set G) :=
  { C : Set G | ∃ g : G, C = bp.parabolicDoubleCoset S₁ S₂ g }

/-- The set of all $(W_{S_1}, W_{S_2})$-double cosets in $W$, i.e. $W_{S_1} \backslash W / W_{S_2}$. -/
def weylDoubleCosets (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) : Set (Set M.Group) :=
  { C : Set M.Group | ∃ w : M.Group, C = bp.weylDoubleCoset S₁ S₂ w }

/-- The image of a Weyl double coset under the assignment $w \mapsto P_{S_1} \cdot n \cdot P_{S_2}$
for any $N$-lift $n$ of $w$. Realizes the bijection
$W_{S_1} \backslash W / W_{S_2} \to P_{S_1} \backslash G / P_{S_2}$. -/
def doubleCosetMap (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) (w : M.Group) : Set G :=
  ⋃ (n : bp.N) (_ : bp.π n = w), bp.parabolicDoubleCoset S₁ S₂ n

end BNPair
