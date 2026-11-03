/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Pointwise Finset

namespace BSG

variable {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]

/-- The sumset image of a finite set $X \subseteq G \times G$ under addition: $\{a + b : (a,b) \in X\}$. -/
noncomputable def sumsetImage (X : Finset (G × G)) : Finset G :=
  X.image (fun p => p.1 + p.2)

/-- Auxiliary counting bound: for any $S$, the total number of triples
$(t_0, t_1, t_2) \in (\text{sumsetImage}\,X)^3$ with $t_0 - t_1 + t_2 \in S$, summed
over $s \in S$, is at most $|\text{sumsetImage}\,X|^3$. -/
lemma sum_fiber_le (X : Finset (G × G)) (S : Finset G) :
    ∑ s ∈ S, ((sumsetImage X ×ˢ (sumsetImage X ×ˢ sumsetImage X)).filter
      (fun t => t.1 - t.2.1 + t.2.2 = s)).card ≤
    (sumsetImage X).card ^ 3 := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc Finset.card _ ≤ (sumsetImage X ×ˢ (sumsetImage X ×ˢ sumsetImage X)).card :=
        Finset.card_filter_le _ _
    _ = (sumsetImage X).card ^ 3 := by
        simp [Finset.card_product, pow_succ, pow_zero, mul_comm]

end BSG

open Pointwise in
/-- **BSG (Balog–Szemerédi–Gowers) proposition / energy lower bound**: for finite sets
$A, B$ in an additive structure, $|A|^2 |B|^2 \leq |A + B| \cdot E(A, B)$, where $E(A,B)$
denotes the additive energy. -/
theorem BSG.card_sq_mul_card_sq_le_card_add_mul_addEnergy
    {α : Type*} [DecidableEq α] [Add α] (A B : Finset α) :
    A.card ^ 2 * B.card ^ 2 ≤ (A + B).card * A.addEnergy B :=
  Finset.le_card_add_mul_addEnergy A B
