/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BSG

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The neighborhood `N(b) = {a ∈ α : (a, b) ∈ X}` of an element `b ∈ β` in a bipartite
relation `X ⊆ α × β`. -/
def neighborhood (X : Finset (α × β)) (b : β) : Finset α :=
  (X.filter (fun p => p.2 = b)).image Prod.fst

/-- The codegree `P₂(a₁, a₂) := #{b ∈ β : (a₁, b) ∈ X ∧ (a₂, b) ∈ X}` — the number of
common neighbors of `a₁` and `a₂` in the bipartite relation `X`. -/
def codegree (X : Finset (α × β)) (a₁ a₂ : α) : ℕ :=
  ((X.filter (fun p => p.1 = a₁)).image Prod.snd ∩
   (X.filter (fun p => p.1 = a₂)).image Prod.snd).card

/-- **Definition (`ε`-bad pair).** A pair `(a₁, a₂)` is `ε`-bad (relative to `K`) if
`P₂(a₁, a₂) < ε · K⁻² · |β|`, i.e. the codegree is unusually small compared with the
typical scale `K⁻² |β|`. -/
def IsEpsilonBad (X : Finset (α × β)) (K ε : ℝ) (a₁ a₂ : α) : Prop :=
  (codegree X a₁ a₂ : ℝ) < ε * K⁻¹ ^ 2 * (Fintype.card β : ℝ)

/-- Decidability of the `ε`-bad predicate (used to define the badness counting function
below). -/
noncomputable instance instDecidableIsEpsilonBad (X : Finset (α × β)) (K ε : ℝ) (a₁ a₂ : α) :
    Decidable (IsEpsilonBad X K ε a₁ a₂) :=
  inferInstanceAs (Decidable (_ < _))

/-- The bad-pairs counting function `BP_ε(b) = #{(a₁, a₂) ∈ N(b)² : (a₁, a₂) is ε-bad}`
from the BSG analysis. -/
noncomputable def badPairsCount (X : Finset (α × β)) (K ε : ℝ) (b : β) : ℕ :=
  ((neighborhood X b) ×ˢ (neighborhood X b)).filter
    (fun (p : α × α) => IsEpsilonBad X K ε p.1 p.2) |>.card

end BSG
