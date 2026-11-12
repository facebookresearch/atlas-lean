/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Perm

set_option maxHeartbeats 800000

namespace SignedPerm

/-- The sign group $(\{\pm 1\})^n$ realized multiplicatively as $\operatorname{Fin}(n) \to (\mathbb{Z}/2)^\times$. -/
abbrev SignGroup (n : ℕ) := Fin n → Multiplicative (ZMod 2)

/-- The permutation action of $S_n$ on the sign group $(\{\pm 1\})^n$ by index permutation,
encoded as a group homomorphism into $\operatorname{MulAut}$. -/
noncomputable def signGroupPermAction (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (SignGroup n) where
  toFun σ := {
    toFun := fun ε => ε ∘ σ.symm
    invFun := fun ε => ε ∘ σ
    left_inv := by intro ε; ext i; simp
    right_inv := by intro ε; ext i; simp
    map_mul' := by intros; ext; simp [Pi.mul_apply]
  }
  map_one' := by ext; simp
  map_mul' := by
    intros σ₁ σ₂; ext ε i
    simp [MulAut.mul_apply, Function.comp, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-- The signed permutation group (hyperoctahedral group) $S_n^\pm = (\{\pm 1\})^n \rtimes S_n$,
the Coxeter group of type $C_n$ (Section 10.2). -/
abbrev SignedPermGroup (n : ℕ) := SignGroup n ⋊[signGroupPermAction n] Equiv.Perm (Fin n)

/-- As a set, $S_n^\pm$ is in bijection with $(\{\pm 1\})^n \times S_n$. -/
def signedPermGroupEquivProd (n : ℕ) :
    SignedPermGroup n ≃ (SignGroup n × Equiv.Perm (Fin n)) where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The cardinality of the signed permutation group is $|S_n^\pm| = 2^n \cdot n!$. -/
theorem signedPermGroup_card (n : ℕ) :
    Nat.card (SignedPermGroup n) = 2 ^ n * n.factorial := by
  rw [Nat.card_congr (signedPermGroupEquivProd n), Nat.card_prod]
  congr 1
  · rw [Nat.card_pi]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The generator $\varepsilon_j \in (\{\pm 1\})^n$ that flips the sign at coordinate $j$ only. -/
def signChangeAt (n : ℕ) (j : Fin n) : SignGroup n :=
  Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 2))

/-- The $S_n$-action permutes the single-coordinate sign flips: $\sigma \cdot \varepsilon_j = \varepsilon_{\sigma j}$. -/
lemma signGroupPermAction_signChangeAt (n : ℕ) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (signGroupPermAction n σ) (signChangeAt n j) = signChangeAt n (σ j) := by
  ext i
  simp [signGroupPermAction, signChangeAt, Pi.mulSingle_apply, Equiv.symm_apply_eq]

/-- Conjugation of a sign vector by a permutation in the semidirect product:
$\sigma \varepsilon \sigma^{-1} = \sigma \cdot \varepsilon$. -/
lemma inr_conj_inl (n : ℕ) (σ : Equiv.Perm (Fin n)) (ε : SignGroup n) :
    (SemidirectProduct.inr (φ := signGroupPermAction n) σ) *
    (SemidirectProduct.inl ε) *
    (SemidirectProduct.inr (φ := signGroupPermAction n) σ)⁻¹ =
    SemidirectProduct.inl ((signGroupPermAction n σ) ε) := by
  apply SemidirectProduct.ext
  · simp [mul_one, map_inv]
  · simp [mul_inv_cancel]

/-- The Coxeter generators of $S_{n+1}^\pm$: the $n$ adjacent transpositions
plus the sign flip at the last coordinate. -/
noncomputable def generators (n : ℕ) : Set (SignedPermGroup (n + 1)) :=
  (Set.range fun (i : Fin n) =>
    (SemidirectProduct.inr (Equiv.swap (Fin.castSucc i) (Fin.succ i))
      : SignedPermGroup (n + 1))) ∪
  {SemidirectProduct.inl (signChangeAt (n + 1) (Fin.last n))}

/-- Every element of $\mathbb{Z}/2$ is either $0$ or $1$. -/
lemma ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> [left; right] <;> rfl

/-- Every element of $(\mathbb{Z}/2)^\times$ (multiplicative form) is either the identity or
$\operatorname{ofAdd} 1$. -/
lemma Multiplicative_ZMod2_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  rcases ZMod2_eq_zero_or_one (Multiplicative.toAdd x) with h | h
  · left; exact Multiplicative.toAdd.injective (by simpa using h)
  · right; exact Multiplicative.toAdd.injective (by simpa using h)

/-- The single-coordinate sign flips generate the whole sign group $(\{\pm 1\})^n$. -/
lemma signGroup_closure_signChangeAt (n : ℕ) :
    Subgroup.closure (Set.range (signChangeAt n)) = ⊤ := by
  rw [eq_top_iff]; intro ε _
  rw [← Finset.univ_prod_mulSingle ε]
  apply Subgroup.prod_mem; intro j _
  rcases Multiplicative_ZMod2_cases (ε j) with h | h
  · rw [h, Pi.mulSingle_one]; exact Subgroup.one_mem _
  · rw [h]; exact Subgroup.subset_closure ⟨j, rfl⟩

/-- A subgroup containing every single-coordinate sign flip contains every signed-coordinate
element from the $\inl$ embedding. -/
lemma inl_mem_of_signChangeAt_mem (n : ℕ) (ε : SignGroup n)
    (S : Subgroup (SignedPermGroup n))
    (h : ∀ j, (SemidirectProduct.inl (signChangeAt n j) : SignedPermGroup n) ∈ S) :
    (SemidirectProduct.inl ε : SignedPermGroup n) ∈ S := by
  have htop : S.comap (SemidirectProduct.inl (φ := signGroupPermAction n)) = ⊤ := by
    rw [eq_top_iff, ← signGroup_closure_signChangeAt n]
    exact (Subgroup.closure_le _).mpr (fun ε' ⟨j, hj⟩ => hj ▸ h j)
  have : ε ∈ S.comap (SemidirectProduct.inl (φ := signGroupPermAction n)) := by
    rw [htop]; exact Subgroup.mem_top ε
  exact this

/-- A subgroup containing all adjacent transpositions (via the $\inr$ embedding) contains every
permutation in $S_{n+1}$. -/
lemma inr_mem_of_adj_swaps_mem (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Subgroup (SignedPermGroup (n + 1)))
    (hS : ∀ i : Fin n,
      SemidirectProduct.inr (Equiv.swap (Fin.castSucc i) (Fin.succ i)) ∈ S) :
    SemidirectProduct.inr σ ∈ S := by
  have htop : S.comap (SemidirectProduct.inr (φ := signGroupPermAction (n + 1))) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ n)]
    exact (Subgroup.closure_le _).mpr (fun σ' ⟨i, hi⟩ => hi ▸ hS i)
  have : σ ∈ S.comap (SemidirectProduct.inr (φ := signGroupPermAction (n + 1))) := by
    rw [htop]; exact Subgroup.mem_top σ
  exact this

end SignedPerm
