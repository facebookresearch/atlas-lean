/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis providing a fixed maximal flag (chain of length $n-1$ of proper non-zero
subspaces) to act as a starting point for refinements. -/
structure BaseFlagHyp where
  base_chain : List (Submodule k (Vec k n))
  base_chain_is_chain : base_chain.IsChain (· < ·)
  base_chain_length : base_chain.length = n - 1
  base_chain_proper : ∀ V ∈ base_chain, V ≠ ⊥ ∧ V ≠ ⊤


/-- Hypothesis: every pair $A < B$ of subspaces with $\dim B \ge \dim A + 2$ admits an
intermediate subspace $W$ with $A < W < B$. -/
structure ChainInsertionHyp where
  fill_gap : ∀ (A B : Submodule k (Vec k n)),
    A < B →
    Module.finrank k ↥A + 2 ≤ Module.finrank k ↥B →
    ∃ W : Submodule k (Vec k n), A < W ∧ W < B

/-- Existence of an intermediate subspace whenever the dimension gap is at least $2$, by
adjoining a single vector $v \in B \setminus A$. -/
noncomputable def chainInsertionHyp : ChainInsertionHyp k n where
  fill_gap := fun A B hAB hgap => by

    obtain ⟨v, hv_in_B, hv_not_A⟩ := Set.exists_of_ssubset hAB

    have hv_ne : v ≠ 0 := fun h => hv_not_A (h ▸ Submodule.zero_mem A)

    have hdisjoint : Disjoint A (Submodule.span k {v}) := by
      rw [Submodule.disjoint_span_singleton]; exact fun h => absurd h hv_not_A

    have hfr : Module.finrank k ↥(A ⊔ Submodule.span k {v}) =
        Module.finrank k ↥A + 1 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span k {v})
      rw [hdisjoint.eq_bot, finrank_bot, finrank_span_singleton hv_ne] at h; omega
    exact ⟨A ⊔ Submodule.span k {v},

      lt_of_le_of_ne le_sup_left (fun heq =>
        hv_not_A (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))),

      Submodule.lt_of_le_of_finrank_lt_finrank
        (sup_le hAB.le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_in_B)))
        (hfr ▸ by omega)⟩


/-- Hypothesis: a proper subspace $V$ can be inserted into any maximal flag to produce a new
maximal flag containing both the original chain and $V$. -/
structure FlagInsertionHyp where
  insert : ∀ (chain : List (Submodule k (Vec k n)))
    (V : Submodule k (Vec k n)),
    chain.IsChain (· < ·) →
    chain.length = n - 1 →
    (∀ W ∈ chain, W ≠ ⊥ ∧ W ≠ ⊤) →
    V ≠ ⊥ →
    V ≠ ⊤ →
    ∃ (chain' : List (Submodule k (Vec k n))),
      V ∈ chain' ∧
      (∀ W ∈ chain, W ∈ chain') ∧
      chain'.IsChain (· < ·) ∧
      chain'.length = n - 1 ∧
      (∀ W ∈ chain', W ≠ ⊥ ∧ W ≠ ⊤)


/-- Given a base flag and a single-subspace insertion hypothesis, refine any finite list of
proper subspaces into a single maximal flag containing all of them, by inductively
inserting them one at a time. -/
noncomputable def latticeChainRefinementOfInsertion
    (base : BaseFlagHyp k n)
    (ins : FlagInsertionHyp k n) : LatticeChainRefinementHyp k n where
  refine_via_chain := fun subs hproper => by
    induction subs with
    | nil =>
      exact ⟨base.base_chain,
        fun _ h => absurd h (List.not_mem_nil),
        base.base_chain_is_chain,
        base.base_chain_length,
        base.base_chain_proper⟩
    | cons V rest ih =>
      have hV_proper := hproper V List.mem_cons_self
      have hrest_proper : ∀ W ∈ rest, W ≠ ⊥ ∧ W ≠ ⊤ :=
        fun W hW => hproper W (List.mem_cons_of_mem V hW)
      obtain ⟨chain₀, hcontains₀, hchain₀, hlen₀, hproper₀⟩ := ih hrest_proper
      obtain ⟨chain₁, hV_mem, hold_mem, hchain₁, hlen₁, hproper₁⟩ :=
        ins.insert chain₀ V hchain₀ hlen₀ hproper₀ hV_proper.1 hV_proper.2
      exact ⟨chain₁,
        fun W hW => by
          rcases List.mem_cons.mp hW with heq | hrest
          · exact heq ▸ hV_mem
          · exact hold_mem W (hcontains₀ W hrest),
        hchain₁,
        hlen₁,
        hproper₁⟩

end GLnBuilding
