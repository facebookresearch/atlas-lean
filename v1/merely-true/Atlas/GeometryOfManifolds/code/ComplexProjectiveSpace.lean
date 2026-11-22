/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AdvancedKahler
import Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open scoped Manifold ContDiff

noncomputable section

/-- The setoid on nonzero vectors in $\mathbb{C}^{n+1}$: $v \sim w$ iff $w = c v$ for some $c \in \mathbb{C}^\times$, used to define $\mathbb{CP}^n$. -/
def CPnSetoid (n : ℕ) : Setoid {v : Fin (n + 1) → ℂ // v ≠ 0} where
  r v w := ∃ (c : ℂ), c ≠ 0 ∧ (∀ i, w.1 i = c * v.1 i)
  iseqv :=
    ⟨fun v => ⟨1, one_ne_zero, fun i => by simp⟩,
     fun ⟨c, hc, h⟩ => ⟨c⁻¹, inv_ne_zero hc, fun i => by
        rw [h i, inv_mul_cancel_left₀ hc]⟩,
     fun ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ => ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun i => by
        rw [h₂ i, h₁ i]; ring⟩⟩

/-- Complex projective space $\mathbb{CP}^n = (\mathbb{C}^{n+1} \setminus \{0\}) / \mathbb{C}^\times$. -/
def ComplexProjectiveSpace (n : ℕ) : Type :=
  Quotient (CPnSetoid n)

/-- $\mathbb{CP}^n$ carries the quotient topology from $\mathbb{C}^{n+1} \setminus \{0\}$. -/
instance CPn_topologicalSpace (n : ℕ) : TopologicalSpace (ComplexProjectiveSpace n) :=
  instTopologicalSpaceQuotient (s := CPnSetoid n)

































end
