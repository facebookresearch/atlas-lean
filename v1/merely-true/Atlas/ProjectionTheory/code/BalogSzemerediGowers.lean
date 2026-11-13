/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.KeyLemmaBSG

open Finset Pointwise

namespace BalogSzemerediGowers

section AdditiveLemmaLocal

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- Auxiliary counting lemma used in the proof of Balog–Szemerédi–Gowers. For a
finite set `X ⊂ G × G` and any `S ⊂ G`, the sum over `s ∈ S` of the number of
triples `(t₀, t₁, t₂) ∈ (X.image (+))^3` with `t₀ - t₁ + t₂ = s` is bounded by
`|X.image (+)|^3` — the total number of triples available. -/
lemma sum_fiber_le (X : Finset (G × G)) (S : Finset G) :
    ∑ s ∈ S, (((X.image (fun p => p.1 + p.2)) ×ˢ
      ((X.image (fun p => p.1 + p.2)) ×ˢ (X.image (fun p => p.1 + p.2)))).filter
      (fun t => t.1 - t.2.1 + t.2.2 = s)).card ≤
    (X.image (fun p => p.1 + p.2)).card ^ 3 := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc Finset.card _ ≤ ((X.image (fun p => p.1 + p.2)) ×ˢ
      ((X.image (fun p => p.1 + p.2)) ×ˢ (X.image (fun p => p.1 + p.2)))).card :=
        Finset.card_filter_le _ _
    _ = (X.image (fun p => p.1 + p.2)).card ^ 3 := by
        simp [Finset.card_product, pow_succ, pow_zero, mul_comm]

end AdditiveLemmaLocal

end BalogSzemerediGowers
