/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset

open Computability

/-- A finite automaton over alphabet `α` with state space `σ`, defined as a `DFA α σ`.

In Sipser's textbook, a finite automaton is a 5-tuple `(Q, Σ, δ, q₀, F)` where
`Q` is a finite set of states, `Σ` a finite alphabet, `δ : Q × Σ → Q` the
transition function, `q₀` the start state, and `F ⊆ Q` the accept states.
This is exactly the data packaged by Mathlib's `DFA`. -/
abbrev FiniteAutomaton (α : Type*) (σ : Type*) := DFA α σ

namespace DFA

variable {α : Type*} {σ : Type*}

/-- The language recognized by a DFA `M`: the set of strings `M` accepts. -/
def language (M : DFA α σ) : Language α :=
  M.accepts

end DFA

namespace RegularLanguages

/-- A language `L` is **regular** if some finite automaton recognizes it.

Equivalent to Mathlib's `Language.IsRegular`. This matches Sipser's
definition: `L` is regular iff `L = L(M)` for some DFA `M`. -/
def IsRegular {α : Type*} (L : Language α) : Prop :=
  L.IsRegular

/-- **Closure of regular languages under union.**

If `A` and `B` are regular languages over the same alphabet, then so is their
union `A ∪ B` (written `A + B`). The proof takes DFAs `M₁` and `M₂` recognizing
`A` and `B` respectively and uses the product DFA `M₁.union M₂` whose state
space is `σ₁ × σ₂`. -/
theorem regular_union {α : Type*} {A B : Language α}
    (hA : IsRegular A) (hB : IsRegular B) : IsRegular (A + B) := by

  unfold IsRegular at *

  obtain ⟨σ₁, _, M₁, hM₁⟩ := hA
  obtain ⟨σ₂, _, M₂, hM₂⟩ := hB


  exact ⟨σ₁ × σ₂, inferInstance, M₁.union M₂, by simp [hM₁, hM₂]⟩

end RegularLanguages

namespace RegularLanguages

open Language Set

/-- The Kleene star `A*` is closed under concatenation: if `x, y ∈ A*` then
`x ++ y ∈ A*`. Combine the witnessing factorizations of `x` and `y`. -/
lemma kstar_append {α : Type*} {A : Language α} {x y : List α}
    (hx : x ∈ KStar.kstar A) (hy : y ∈ KStar.kstar A) :
    x ++ y ∈ KStar.kstar A := by
  rw [mem_kstar] at hx hy ⊢
  obtain ⟨L₁, hf₁, hL₁⟩ := hx; obtain ⟨L₂, hf₂, hL₂⟩ := hy
  exact ⟨L₁ ++ L₂, by simp [hf₁, hf₂], fun w hw => by
    simp at hw; rcases hw with h | h <;> [exact hL₁ w h; exact hL₂ w h]⟩

/-- Prepending a word `w ∈ A` to `y ∈ A*` stays in `A*`. -/
lemma kstar_cons {α : Type*} {A : Language α} {w y : List α}
    (hw : w ∈ A) (hy : y ∈ KStar.kstar A) :
    w ++ y ∈ KStar.kstar A := by
  rw [mem_kstar] at hy ⊢; obtain ⟨L, hf, hL⟩ := hy
  refine ⟨w :: L, by simp [hf], fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv <;> [exact hw; exact hL v hv]

/-- Splitting lemma for Kleene star.

If `x ++ y ∈ A*`, then either
* both `x ∈ A*` and `y ∈ A*` (the split between `x` and `y` aligns with a
  word boundary in some `A*`-factorization), or
* the boundary cuts through a single word of `A`: there exist `p ∈ A*`,
  nonempty `c`, and `d, r` with `x = p ++ c`, `c ++ d ∈ A`, `r ∈ A*` and
  `y = d ++ r`. -/
lemma kstar_split {α : Type*} {A : Language α} {x y : List α}
    (h : x ++ y ∈ KStar.kstar A) :
    (x ∈ KStar.kstar A ∧ y ∈ KStar.kstar A) ∨
    (∃ p c d r, p ∈ KStar.kstar A ∧ x = p ++ c ∧ c ≠ [] ∧ c ++ d ∈ A ∧
      r ∈ KStar.kstar A ∧ y = d ++ r) := by
  rw [mem_kstar] at h; obtain ⟨L, hfl, hL⟩ := h
  induction L generalizing x with
  | nil =>
    simp [List.flatten] at hfl
    have hx : x = [] := by cases x <;> simp_all
    subst hx; simp at hfl; subst hfl
    exact Or.inl ⟨nil_mem_kstar A, nil_mem_kstar A⟩
  | cons w L ih =>
    simp [List.flatten] at hfl
    have hw : w ∈ A := hL w (List.mem_cons.mpr (Or.inl rfl))
    have hL' : ∀ v ∈ L, v ∈ A := fun v hv => hL v (List.mem_cons.mpr (Or.inr hv))
    rcases List.append_eq_append_iff.mp hfl with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    ·
      by_cases hx : x = []
      ·
        subst hx; simp at hc1; subst hc1
        left; exact ⟨nil_mem_kstar A, hc2 ▸ kstar_cons hw (join_mem_kstar hL')⟩
      ·
        right
        exact ⟨[], x, c, L.flatten, nil_mem_kstar A, by simp, hx,
          hc1 ▸ hw, join_mem_kstar hL', hc2⟩
    ·
      rcases ih hc2.symm hL' with
        ⟨hc_star, hy_star⟩ | ⟨p, c', d, r, hp, hcp, hc', hcd, hr, hyr⟩
      · left; exact ⟨hc1 ▸ kstar_cons hw hc_star, hy_star⟩
      · right; exact ⟨w ++ p, c', d, r, kstar_cons hw hp,
          by rw [hc1, hcp, List.append_assoc], hc', hcd, hr, hyr⟩

/-- Transfer membership in `A*` between prefixes that have the same set of
"residual left-quotients" of nonempty pending words.

If every left-quotient `A / c` realized by a nonempty residual `c` of `x₁` (with
some `p ∈ A*` so that `x₁ = p ++ c`) is also realized by `x₂`, and `x₂ ∈ A*`
whenever `x₁ ∈ A*`, then `x₁ ++ y ∈ A*` implies `x₂ ++ y ∈ A*`. This is the
core step in proving that `A*` has finitely many left-quotients. -/
lemma kstar_leftQuotient_transfer {α : Type*} {A : Language α} {x₁ x₂ y : List α}
    (hS : A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } ⊆
          A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₂ = p ++ c ∧ c ≠ [] })
    (hB : x₁ ∈ KStar.kstar A → x₂ ∈ KStar.kstar A)
    (hy : x₁ ++ y ∈ KStar.kstar A) :
    x₂ ++ y ∈ KStar.kstar A := by
  rcases kstar_split hy with
    ⟨hx₁_star, hy_star⟩ | ⟨p, c, d, r, hp, hxpc, hc, hcd, hr, hyr⟩
  ·
    exact kstar_append (hB hx₁_star) hy_star
  ·

    have hmem : A.leftQuotient c ∈
        A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } :=
      ⟨c, ⟨p, hp, hxpc, hc⟩, rfl⟩
    obtain ⟨c', ⟨p', hp', hx₂pc', _⟩, heq⟩ := hS hmem


    have hd : d ∈ A.leftQuotient c' := by rw [heq, mem_leftQuotient]; exact hcd
    subst hyr

    rw [hx₂pc', List.append_assoc,
        show c' ++ (d ++ r) = (c' ++ d) ++ r from (List.append_assoc _ _ _).symm]
    exact kstar_append hp' (kstar_cons ((mem_leftQuotient c' d).mp hd) hr)

/-- If `x₁` and `x₂` induce the same set of residual `A`-left-quotients and the
same membership in `A*`, then their left-quotients under `A*` agree:
`A* / x₁ = A* / x₂`. This is the equivalence relation underlying the
Myhill–Nerode-style proof that `A*` is regular. -/
lemma leftQuotient_kstar_determined {α : Type*} (A : Language α) (x₁ x₂ : List α)
    (hS : A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₁ = p ++ c ∧ c ≠ [] } =
          A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x₂ = p ++ c ∧ c ≠ [] })
    (hB : (x₁ ∈ KStar.kstar A) = (x₂ ∈ KStar.kstar A)) :
    (KStar.kstar A).leftQuotient x₁ = (KStar.kstar A).leftQuotient x₂ := by
  ext y; simp only [mem_leftQuotient]
  exact ⟨kstar_leftQuotient_transfer (hS ▸ le_refl _) (hB ▸ id),
         kstar_leftQuotient_transfer (hS.symm ▸ le_refl _) (hB.symm ▸ id)⟩

/-- The range of any function `f : X → Prop` is finite (it has at most two
elements, `True` and `False`, by propositional extensionality). -/
lemma finite_range_prop {X : Type*} (f : X → Prop) : Set.Finite (Set.range f) := by
  apply Set.Finite.subset (Set.Finite.insert True (Set.finite_singleton False))
  intro p ⟨n, hn⟩; subst hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h : f n
  · left; exact propext ⟨fun _ => trivial, fun _ => h⟩
  · right; exact propext ⟨fun hf => absurd hf h, False.elim⟩

/-- **Closure of regular languages under Kleene star.**

If `A` is a regular language then so is `A* = A.kstar`. The proof uses the
Myhill–Nerode characterization: `A*` has finitely many left-quotients because
each one is determined by the pair `(set of residual A-left-quotients, membership
of x in A*)`, and both components live in finite sets when `A` is regular. -/
theorem regular_star {α : Type*} {A : Language α}
    (hA : A.IsRegular) : (KStar.kstar A).IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient

  set descr : List α → Set (Language α) × Prop :=
    fun x => (A.leftQuotient '' { c | ∃ p ∈ KStar.kstar A, x = p ++ c ∧ c ≠ [] },
              x ∈ KStar.kstar A) with descr_def

  have hfin_descr : (Set.range descr).Finite := by
    apply Set.Finite.subset
      (Set.Finite.prod hA.finite_range_leftQuotient.powerset (finite_range_prop _))
    rintro ⟨S, b⟩ ⟨x, hx⟩
    simp only [descr_def] at hx
    exact ⟨by rw [Set.mem_powerset_iff, ← (Prod.ext_iff.mp hx).1]
              exact Set.image_subset_range _ _,
           ⟨x, (Prod.ext_iff.mp hx).2⟩⟩

  have hfactor : ∀ x₁ x₂, descr x₁ = descr x₂ →
      (KStar.kstar A).leftQuotient x₁ = (KStar.kstar A).leftQuotient x₂ := by
    intro x₁ x₂ h
    exact leftQuotient_kstar_determined A x₁ x₂
      (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

  apply Set.Finite.subset
    (hfin_descr.image ((KStar.kstar A).leftQuotient ∘ Function.invFun descr))
  rintro L ⟨x, rfl⟩
  exact ⟨descr x, ⟨x, rfl⟩, hfactor _ _ (Function.invFun_eq ⟨x, rfl⟩)⟩

end RegularLanguages

namespace RegularLanguages

open Computability

/-- **Pumping lemma at the DFA level.**

If a DFA `M` with finite state space `σ` accepts a string `s` of length at
least `|σ|`, then `s` factors as `s = x ++ y ++ z` with `|xy| ≤ |σ|`,
`y ≠ []`, and `{x} · {y}* · {z} ⊆ L(M)`. -/
theorem DFA.pumping_lemma' {α σ : Type*} (M : DFA α σ) [Fintype σ] {s : List α}
    (hs : s ∈ M.accepts) (hlen : Fintype.card σ ≤ s.length) :
    ∃ x y z,
      s = x ++ y ++ z ∧
        x.length + y.length ≤ Fintype.card σ ∧
          y ≠ [] ∧
            {x} * {y}∗ * {z} ≤ M.accepts :=
  M.pumping_lemma hs hlen

/-- **Pumping lemma for regular languages.**

For every regular language `A`, there is a pumping length `p > 0` such that any
`s ∈ A` with `|s| ≥ p` factors as `s = xyz` with
1. `xyⁱz ∈ A` for all `i ≥ 0` (encoded here as `{x} · {y}* · {z} ⊆ A`),
2. `y ≠ ε`,
3. `|xy| ≤ p`.

The pumping length is taken to be the cardinality of the state space of a DFA
recognizing `A`. -/
theorem pumping_lemma {α : Type*} {A : Language α} (hA : IsRegular A) :
    ∃ p : ℕ, 0 < p ∧ ∀ s ∈ A, p ≤ s.length →
      ∃ x y z : List α,
        s = x ++ y ++ z ∧
          x.length + y.length ≤ p ∧
            y ≠ [] ∧
              {x} * {y}∗ * {z} ≤ A := by

  obtain ⟨σ, hfin, M, hM⟩ := hA

  haveI : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩

  intro s hs hlen
  rw [← hM] at hs
  obtain ⟨x, y, z, hsplit, hxylen, hne, hpump⟩ := M.pumping_lemma hs hlen
  exact ⟨x, y, z, hsplit, hxylen, hne, hM ▸ hpump⟩

end RegularLanguages

namespace RegularLanguages

open Language Set

/-- Concatenation of two languages: `A · B = { ab | a ∈ A, b ∈ B }`,
realized in Mathlib as `A * B`. -/
def concat {α : Type*} (A B : Language α) : Language α := A * B

/-- The left-quotient of `A * B` by `x` is determined by the pair
`(A.leftQuotient x, { B.leftQuotient c | a ∈ A, x = a ++ c })`.

If two strings `x₁, x₂` agree in both components then they have the same
left-quotient under the concatenation `A * B`. This is the key lemma for
showing `A * B` is regular via Myhill–Nerode. -/
lemma leftQuotient_mul_determined {α : Type*} (A B : Language α) (x₁ x₂ : List α)
    (h1 : A.leftQuotient x₁ = A.leftQuotient x₂)
    (h2 : B.leftQuotient '' { c | ∃ a ∈ A, x₁ = a ++ c } =
          B.leftQuotient '' { c | ∃ a ∈ A, x₂ = a ++ c }) :
    (A * B).leftQuotient x₁ = (A * B).leftQuotient x₂ := by
  ext y
  simp only [mem_leftQuotient, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · have hmem : B.leftQuotient c ∈ B.leftQuotient '' { c | ∃ a ∈ A, x₁ = a ++ c } :=
        ⟨c, ⟨a, ha, hc1⟩, rfl⟩
      rw [h2] at hmem
      obtain ⟨c', ⟨a', ha', hc1'⟩, heq⟩ := hmem
      refine ⟨a', ha', c' ++ y, ?_, by rw [hc1', List.append_assoc]⟩
      rw [← mem_leftQuotient, heq, mem_leftQuotient]
      exact hc2 ▸ hb
    · exact ⟨x₂ ++ c,
        by rw [← mem_leftQuotient, ← h1, mem_leftQuotient, ← hc1]; exact ha,
        b, hb, by rw [List.append_assoc, hc2.symm]⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · have hmem : B.leftQuotient c ∈ B.leftQuotient '' { c | ∃ a ∈ A, x₂ = a ++ c } :=
        ⟨c, ⟨a, ha, hc1⟩, rfl⟩
      rw [← h2] at hmem
      obtain ⟨c', ⟨a', ha', hc1'⟩, heq⟩ := hmem
      refine ⟨a', ha', c' ++ y, ?_, by rw [hc1', List.append_assoc]⟩
      rw [← mem_leftQuotient, heq, mem_leftQuotient]
      exact hc2 ▸ hb
    · exact ⟨x₁ ++ c,
        by rw [← mem_leftQuotient, h1, mem_leftQuotient, ← hc1]; exact ha,
        b, hb, by rw [List.append_assoc, hc2.symm]⟩

/-- **Closure of regular languages under concatenation.**

If `A` and `B` are regular then so is `A · B = A * B`. The proof uses the
Myhill–Nerode characterization, showing that `A * B` has finitely many
left-quotients because each is determined by a pair lying in the product of
two finite sets. -/
theorem regular_concat {α : Type*} {A B : Language α}
    (hA : A.IsRegular) (hB : B.IsRegular) : (A * B).IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient

  set descr : List α → Language α × Set (Language α) :=
    fun x => (A.leftQuotient x, B.leftQuotient '' { c | ∃ a ∈ A, x = a ++ c }) with descr_def


  have hfin_descr : (range descr).Finite := by
    apply Set.Finite.subset
      (Set.Finite.prod hA.finite_range_leftQuotient hB.finite_range_leftQuotient.powerset)
    rintro ⟨L, S⟩ ⟨x, hx⟩
    simp only [descr_def] at hx
    exact ⟨⟨x, (Prod.ext_iff.mp hx).1⟩,
      by rw [mem_powerset_iff, ← (Prod.ext_iff.mp hx).2]; exact image_subset_range _ _⟩

  have hfactor : ∀ x₁ x₂, descr x₁ = descr x₂ →
      (A * B).leftQuotient x₁ = (A * B).leftQuotient x₂ := by
    intro x₁ x₂ h
    exact leftQuotient_mul_determined A B x₁ x₂
      (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

  apply Set.Finite.subset (hfin_descr.image ((A * B).leftQuotient ∘ Function.invFun descr))
  rintro L ⟨x, rfl⟩
  exact ⟨descr x, ⟨x, rfl⟩, hfactor _ _ (Function.invFun_eq ⟨x, rfl⟩)⟩

end RegularLanguages
