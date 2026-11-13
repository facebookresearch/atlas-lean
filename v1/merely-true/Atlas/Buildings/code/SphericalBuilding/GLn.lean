/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.RelClasses
import Mathlib.Data.Matrix.Basic

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- The ambient vector space $k^n$ realised as the function type $\mathrm{Fin}\ n \to k$. -/
abbrev Vec := Fin n → k

/-- Abstract data of a flag-like simplicial complex: a vertex type, a simplex type, and a
function assigning to each simplex its finite set of vertices. -/
structure FlagData where
  vertex : Type*
  simplex : Type*
  verticesOf : simplex → Finset vertex

/-- A simplex of the $\mathrm{GL}_n(k)$-building: a non-empty, strictly increasing chain of
proper non-zero subspaces $0 \subsetneq V_1 \subsetneq \cdots \subsetneq V_r \subsetneq k^n$. -/
structure SubspaceFlag where
  chain : List (Submodule k (Vec k n))
  chain_nonempty : chain ≠ []
  chain_strictly_increasing : chain.IsChain (· < ·)
  chain_proper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤

/-- A `SubspaceFlag` is a chamber iff its chain has length $n-1$, i.e.\ it is a maximal flag. -/
def IsChamber (F : SubspaceFlag k n) : Prop :=
  F.chain.length = n - 1

/-- A frame of $k^n$: an ordered direct-sum decomposition $k^n = L_1 \oplus \cdots \oplus L_n$
into $n$ lines. -/
structure Frame where
  lines : Fin n → Submodule k (Vec k n)
  one_dim : ∀ i, Module.finrank k (lines i) = 1
  indep : iSupIndep lines
  spanning : ⨆ i, lines i = ⊤

/-- A subspace $W$ is compatible with the frame $F$ iff $W = \bigoplus_{i \in S} L_i$ for some
$S \subseteq \{1,\dots,n\}$. -/
def Frame.IsCompatible (F : Frame k n) (W : Submodule k (Vec k n)) : Prop :=
  ∃ S : Finset (Fin n), W = ⨆ i ∈ S, F.lines i

/-- An apartment associated to the frame $F$: a flag every member of which is compatible
with $F$. -/
structure Apartment (F : Frame k n) where
  flag : SubspaceFlag k n
  compatible : ∀ V ∈ flag.chain, F.IsCompatible k n V

/-- The building axioms for the flag complex of $\mathrm{GL}_n(k)$: (i) every panel extends to
two distinct chambers (thinness), (ii) any two flags lie in a common apartment, and
(iii) two apartments sharing two chambers admit a compatibility-preserving isomorphism
fixing both chambers. -/
structure IsBuilding where
  apartment_thin : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain ∧ V ∈ C₂.chain)
  common_apartment : ∀ (σ τ : SubspaceFlag k n),
    ∃ F : Frame k n, (∀ V ∈ σ.chain, F.IsCompatible k n V) ∧
                      (∀ V ∈ τ.chain, F.IsCompatible k n V)
  apartment_iso : ∀ (F₁ F₂ : Frame k n) (C₁ C₂ : SubspaceFlag k n),
    IsChamber k n C₁ → IsChamber k n C₂ →
    (∀ V ∈ C₁.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₁.chain, F₂.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₂.IsCompatible k n V) →
    ∃ f : Submodule k (Vec k n) → Submodule k (Vec k n),
      Function.Bijective f ∧
      (∀ V, F₁.IsCompatible k n V → F₂.IsCompatible k n (f V)) ∧
      (∀ V ∈ C₁.chain, f V = V) ∧
      (∀ V ∈ C₂.chain, f V = V)

/-- Data of a $BN$-pair for $\mathrm{GL}_n(k)$: a standard chamber, standard frame, and the
subgroups $B$ and $N$ (encoded as sets of matrices). -/
structure GLnBNPairData where
  stdFlag : SubspaceFlag k n
  stdFlag_chamber : IsChamber k n stdFlag
  stdFrame : Frame k n
  B : Set (Matrix (Fin n) (Fin n) k)
  N : Set (Matrix (Fin n) (Fin n) k)

/-- A Coxeter matrix is of type $A_{n-1}$ when its diagonal entries are $1$, off-diagonal
entries lie in $\{2,3\}$, and it is symmetric. -/
def TypeA (M : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ) : Prop :=
  (∀ i, M i i = 1) ∧
  (∀ i j, i ≠ j → (M i j = 2 ∨ M i j = 3)) ∧
  (∀ i j, M i j = M j i)

/-- The standard Coxeter matrix of type $A_{n-1}$: ones on the diagonal, threes on adjacent
positions, twos elsewhere. -/
def coxeterMatrixA : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ := fun i j =>
  if i = j then 1
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3
  else 2

/-- The Coxeter matrix `coxeterMatrixA n` satisfies the type-$A$ predicate. -/
theorem typeA : TypeA n (coxeterMatrixA n) := by
  refine ⟨fun i => by simp [coxeterMatrixA], fun i j hij => ?_, fun i j => ?_⟩
  ·
    simp only [coxeterMatrixA, if_neg hij]
    split_ifs with h
    · right; rfl
    · left; rfl
  ·
    unfold coxeterMatrixA
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
      · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
        simp [hadj, hadj']
      · have hadj' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
          push_neg at hadj ⊢; constructor <;> omega
        simp [hadj, hadj']

end GLnBuilding
