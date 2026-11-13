/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.EpsilonNFA

open Computability Set

namespace Sipser

/-- **Nondeterministic Finite Automaton (Sipser-style).**

An NFA is a 5-tuple `(Q, Σ, δ, q₀, F)` where `Q` is a finite set of states,
`Σ` an alphabet, `q₀ ∈ Q` the start state, `F ⊆ Q` the accept states, and
`δ : Q × Σ_ε → 𝒫(Q)` the transition function (where `Σ_ε = Σ ∪ {ε}`).

Here `δ q (some a)` gives the transitions on input symbol `a`, while
`δ q none` gives the ε-transitions. Successor sets are represented as
`Finset Q`. The alphabet `Σ` and the implicit `Q` are tracked by the type
parameters. -/
structure NFA (Q : Type*) (σ : Type*) [DecidableEq Q] where
  δ : Q → Option σ → Finset Q
  q₀ : Q
  accept : Finset Q

namespace NFA

variable {Q : Type*} {σ : Type*} [DecidableEq Q]

/-- Convert a Sipser-style `NFA` into Mathlib's `εNFA σ Q` by coercing each
finset of successor states to a `Set`, and packaging the singleton start set
`{q₀}` and accept set `F`. -/
def toεNFA (M : NFA Q σ) : εNFA σ Q where
  step q a := ↑(M.δ q a)
  start := {M.q₀}
  accept := ↑M.accept

/-- The ε-closure of a set of states `S ⊆ Q`: all states reachable from `S`
by zero or more ε-transitions. -/
def εClosure (M : NFA Q σ) (S : Set Q) : Set Q :=
  εNFA.εClosure M.toεNFA S

/-- `M` accepts the input word `w` iff some computation branch of the
underlying ε-NFA reaches an accept state after reading `w`. -/
def accepts (M : NFA Q σ) (w : List σ) : Prop :=
  w ∈ εNFA.accepts M.toεNFA

/-- The language recognized by an NFA `M`: the set of words it accepts. -/
def language (M : NFA Q σ) : Language σ :=
  εNFA.accepts M.toεNFA

/-- The language of `M` is, by definition, the accepting language of the
underlying Mathlib `εNFA`. -/
theorem language_eq_toεNFA_accepts (M : NFA Q σ) :
    M.language = εNFA.accepts M.toεNFA :=
  rfl

/-- **NFA to DFA conversion (Sipser).** If an NFA `M` with finite state
space `Q` recognizes a language `A`, then `A` is regular.

The proof passes through Mathlib's `εNFA → NFA → DFA` subset construction:
the resulting DFA has state space `Set Q`, which is finite since `Q` is. -/
theorem language_isRegular [Fintype Q] (M : NFA Q σ) :
    M.language.IsRegular := by
  rw [language_eq_toεNFA_accepts, Language.isRegular_iff]
  exact ⟨Set Q, inferInstance, M.toεNFA.toNFA.toDFA,
    by simp [εNFA.toNFA_correct, NFA.toDFA_correct]⟩

end NFA

end Sipser

namespace NFAtoDFA

open Computability

end NFAtoDFA
