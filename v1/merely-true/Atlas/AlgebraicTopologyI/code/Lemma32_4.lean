/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section32
import Mathlib.Analysis.Convex.Contractible

open Set Function

namespace OrientationTheorem

/-- If `A i` is a decreasing sequence of closed sets and `K` is a compact set disjoint
from `⋂ i, A i`, then `K` is already disjoint from some `A i`. -/
lemma compact_subset_complement_eventually
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (K : Set X) (hK : IsCompact K)
    (hKA : K ⊆ (⋂ i, A i)ᶜ) :
    ∃ i, K ⊆ (A i)ᶜ := by

  rw [compl_iInter] at hKA


  exact hK.elim_directed_cover _ (fun i => (hA_closed i).isOpen_compl) hKA
    (Monotone.directed_le (fun i j hij =>
      compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hij)))

/-- Data packaging "compactly supported" surjectivity and injectivity hypotheses for the
sequence of groups `G (A i)` mapping to `G (⋂ A i)`. Each element of the limit group is
represented modulo a compact support condition, and each kernel element vanishes after
restricting to a compact support. This is the abstract input to the colimit step of the
proof of Lemma 32.4. -/
structure CompactlySupportedDiagram {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (G : Set X → Type*)
    [∀ K, AddCommGroup (G K)] where
  ρ : ∀ i, G (A i) →+ G (⋂ j, A j)
  φ : ∀ (i j : ℕ), i ≤ j → G (A i) →+ G (A j)
  compat : ∀ i j (hij : i ≤ j), (ρ j).comp (φ i j hij) = ρ i
  surj_support : ∀ (x : G (⋂ j, A j)),
    ∃ (K : Set X), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
      ∀ i, K ⊆ (A i)ᶜ → ∃ g : G (A i), ρ i g = x
  inj_support : ∀ (i : ℕ) (g : G (A i)), ρ i g = 0 →
    ∃ (K : Set X), IsCompact K ∧ K ⊆ (⋂ n, A n)ᶜ ∧
      ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φ i j hij g = 0

/-- Construction of the `RelativeHomologyColimitData` from a `CompactlySupportedDiagram`
on a decreasing sequence of compact closed subsets. The surjectivity and injectivity
conditions of the colimit are extracted from the compactly-supported data by combining
them with `compact_subset_complement_eventually`. This is the core lemma giving
$\varinjlim_i H_q(X, X - A_i) \cong H_q(X, X - A)$ in Lemma 32.4. -/
def RelativeHomologyColimitData.ofCompactDecreasing
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (_hA_compact : ∀ i, IsCompact (A i))
    (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (G : Set X → Type*) [∀ K, AddCommGroup (G K)]
    (csd : CompactlySupportedDiagram A G) :
    RelativeHomologyColimitData A G where
  ρ := csd.ρ
  φ := csd.φ
  compat := csd.compat
  surj := by
    intro x

    obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := csd.surj_support x

    obtain ⟨i, hKi⟩ := compact_subset_complement_eventually A hA_closed hA_decreasing K
      hK_compact hK_sub

    obtain ⟨g, hg⟩ := hK_lift i hKi
    exact ⟨i, g, hg⟩
  inj := by
    intro i g hg

    obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := csd.inj_support i g hg

    obtain ⟨j, hKj⟩ := compact_subset_complement_eventually A hA_closed hA_decreasing K
      hK_compact hK_sub

    have hij : i ≤ max i j := le_max_left i j
    have hjmax : j ≤ max i j := le_max_right i j
    have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
      (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))

    exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩


end OrientationTheorem
