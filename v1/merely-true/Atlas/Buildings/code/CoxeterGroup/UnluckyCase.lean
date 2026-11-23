/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers

namespace CoxeterSystemFromDeletion

/-- The "$H$-equation" at rotation $k$: $\prod_{i=k+1}^{k+m} g_i = \prod_{i=k}^{k+m-1} g_i$. -/
def HTypeEq {W' : Type*} [Monoid W'] (g : ℕ → W') (m : ℕ) (k : ℕ) : Prop :=
  consecProd g (k + 1) m = consecProd g k m

/-- The "unlucky" case: the $H$-equation holds at every cyclic rotation $k$. -/
def AllRotationsUnlucky {W' : Type*} [Monoid W'] (g : ℕ → W') (m : ℕ) : Prop :=
  ∀ k, HTypeEq g m k




/-- For a length-$2m$ word that is $2$-periodic, the product factors as $(f(w_0) f(w_1))^m$. -/
lemma alternating_word_prod_eq_pow_local {B' : Type*} {G : Type*} [Group G]
    (f : B' → G) (word : List B') (m : ℕ)
    (hlen : word.length = 2 * m) (hm : m ≥ 1)
    (halt : ∀ (k : ℕ) (hk : k + 2 < word.length),
      word.get ⟨k, by omega⟩ = word.get ⟨k + 2, hk⟩) :
    (word.map f).prod = (f (word.get ⟨0, by omega⟩) * f (word.get ⟨1, by omega⟩)) ^ m := by
  induction m using Nat.strongRecOn generalizing word with
  | ind n ih =>
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, word = a :: b :: rest := by
      match word, show word.length ≥ 2 by omega with
      | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp only [List.map_cons, List.prod_cons]
    have hget0 : (a :: b :: rest).get ⟨0, by omega⟩ = a := rfl
    have hget1 : (a :: b :: rest).get ⟨1, by omega⟩ = b := rfl
    rw [hget0, hget1]
    by_cases hn1 : n = 1
    · subst hn1
      simp only [List.length_cons] at hlen
      have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [pow_one]
    · have hrest_len : rest.length = 2 * (n - 1) := by
        simp only [List.length_cons] at hlen; omega
      have hge : n - 1 ≥ 1 := by omega
      have hrest0 : rest.get ⟨0, by omega⟩ = a := by
        have := halt 0 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have hrest1 : rest.get ⟨1, by omega⟩ = b := by
        have := halt 1 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have halt_rest : ∀ (k : ℕ) (hk : k + 2 < rest.length),
          rest.get ⟨k, by omega⟩ = rest.get ⟨k + 2, hk⟩ := by
        intro k hk
        have := halt (k + 2) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at this; exact this
      have ih_rest := ih (n - 1) (by omega) rest hrest_len hge halt_rest
      have hget0' : rest.get ⟨0, by omega⟩ = a := hrest0
      have hget1' : rest.get ⟨1, by omega⟩ = b := hrest1
      rw [hget0', hget1'] at ih_rest
      rw [ih_rest, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

end CoxeterSystemFromDeletion
