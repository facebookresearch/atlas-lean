/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.ThresholdDef

open Filter Finset Asymptotics

namespace GraphProperty

/-- A family $(\mu_n)$ of edge-probability-indexed quantities is monotone if, for each $n$,
    $p \mapsto \mu_n(p)$ is nondecreasing on $[0, 1]$. -/
def IsMonotone (μ : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ p₁ p₂ : ℝ, 0 ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ 1 → μ n p₁ ≤ μ n p₂

/-- A family $(\mu_n)$ comes from an isomorphism-invariant monotone graph property if
    there exist decidable, permutation-invariant, upwards-closed predicates $\mathrm{prop}_n$
    on edge sets such that $\mu_n(p)$ equals the probability under $G(n, p)$ that the edge
    set satisfies $\mathrm{prop}_n$. -/
def IsIsomorphismInvariant (μ : ℕ → ℝ → ℝ) : Prop :=
  ∃ (prop_n : (n : ℕ) → Finset (Sym2 (Fin n)) → Prop)
    (_ : ∀ n, DecidablePred (prop_n n)),

    (∀ n (σ : Equiv.Perm (Fin n)) (E : Finset (Sym2 (Fin n))),
      prop_n n E ↔ prop_n n (E.image (Sym2.map σ))) ∧

    (∀ n (E₁ E₂ : Finset (Sym2 (Fin n))), E₁ ⊆ E₂ → prop_n n E₁ → prop_n n E₂) ∧

    (∀ n : ℕ, ∀ p : ℝ,
      μ n p = ∑ E : Finset (Sym2 (Fin n)),
        if prop_n n E then
          p ^ E.card * (1 - p) ^ (Fintype.card (Sym2 (Fin n)) - E.card)
        else 0)


end GraphProperty
