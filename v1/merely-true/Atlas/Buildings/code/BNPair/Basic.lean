/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

set_option linter.unusedSectionVars false

/-- A *BN-pair* (Tits system) on a group $G$ relative to a Coxeter matrix $M$:
data of subgroups $B, N, T = B \cap N$ together with a surjection $\pi : N \twoheadrightarrow W = M.\text{Group}$
whose kernel is $T$, such that $B \cup N$ generates $G$. The Coxeter group $W = N/T$ acts as
the *Weyl group*; the cells $BwB$ partition $G$ (Bruhat decomposition). -/
structure BNPair (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  B : Subgroup G
  N : Subgroup G
  T : Subgroup G
  T_eq : T = B ⊓ N
  π : N →* M.Group
  π_surj : Function.Surjective π
  π_ker : ∀ n : N, π n = 1 ↔ (n : G) ∈ T
  generates : Subgroup.closure ((B : Set G) ∪ (N : Set G)) = ⊤

/-- The *Bruhat cell* $C(w) = BwB \subseteq G$ associated to $w \in W$: the set of $g$
of the form $b_1 \, n \, b_2$ with $b_1, b_2 \in B$ and $n \in N$ a lift of $w$. -/
def BNPair.bruhatCell {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (w : M.Group) : Set G :=
  { g : G | ∃ (b₁ : bp.B) (n : bp.N) (b₂ : bp.B),
    bp.π n = w ∧ g = b₁ * n * b₂ }

/-- Pointwise product $X \cdot Y = \{xy : x \in X, y \in Y\}$ of two subsets of a group. -/
def setMul {G : Type*} [Group G] (X Y : Set G) : Set G :=
  { g | ∃ x ∈ X, ∃ y ∈ Y, g = x * y }

/-- The set of lifts in $N$ of a simple reflection $s \in S$ along $\pi : N \twoheadrightarrow W$. -/
def BNPair.liftSimple {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (s : B_idx) : Set G :=
  { (n : G) | ∃ (n' : bp.N), bp.π n' = M.toCoxeterSystem.simple s ∧ n = n' }

/-- The defining axioms of a Tits system: multiplication rules
$C(w) \cdot C(s) \subseteq C(ws)$ when $\ell(ws) > \ell(w)$, and
$C(w) \cdot C(s) \subseteq C(ws) \cup C(w)$ otherwise, together with the
non-normality condition $\exists b \in B, nbn^{-1} \notin B$ for each lift $n$ of a simple $s$. -/
structure BNPairAxioms {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) where
  cell_mul_length_increasing : ∀ (w : M.Group) (s : B_idx),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) >
      M.toCoxeterSystem.length w →
    setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      bp.bruhatCell (w * M.toCoxeterSystem.simple s)
  cell_mul_length_decreasing : ∀ (w : M.Group) (s : B_idx),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) <
      M.toCoxeterSystem.length w →
    setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      bp.bruhatCell (w * M.toCoxeterSystem.simple s) ∪ bp.bruhatCell w
  conjugate_not_sub : ∀ (s : B_idx) (n : bp.N),
    bp.π n = M.toCoxeterSystem.simple s →
    ∃ b : bp.B, (n : G) * b * (n : G)⁻¹ ∉ bp.B
