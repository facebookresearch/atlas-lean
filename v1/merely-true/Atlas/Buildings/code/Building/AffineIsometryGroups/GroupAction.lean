/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AffineIsometryBuilding

open DVRContext

variable (C : DVRContext)


/-- The Iwahori subgroup of the isometry group $\mathrm{Isom}(B) \subseteq
GL_n(k)$: isometries that lie in $GL_n(\mathfrak{o})$ with unit diagonal
entries and strictly-below-diagonal entries in $\mathfrak{m}$. -/
def IwahoriSubgroupIsometry (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) :
    Set C.GL_n_k :=
  { g |

    IsIsometry C B g ∧

    (∀ i j : Fin C.n, C.isInO (g.val i j)) ∧

    (∀ i : Fin C.n, C.isUnitInO (g.val i i)) ∧

    (∀ i j : Fin C.n, j < i → C.isInMaxIdeal (g.val i j)) }


/-- Combinatorial characterisation of an affine Coxeter matrix of type
$\tilde C_n$: symmetric matrix with diagonal $1$, edges of label $3$ along
the interior of the diagram and label $4$ at both ends, all other pairs
labelled $2$. -/
def IsAffineCn (numGen : ℕ) (m : Fin numGen → Fin numGen → ℕ) : Prop :=
  numGen ≥ 3 ∧

  (∀ i, m i i = 1) ∧

  (∀ i j, m i j = m j i) ∧

  (∀ i j : Fin numGen, i.val + 1 = j.val →
    1 ≤ i.val → j.val + 1 < numGen → m i j = 3) ∧

  (∀ (h : 1 < numGen), m ⟨0, by omega⟩ ⟨1, by omega⟩ = 4) ∧

  (∀ (h : 1 < numGen),
    m ⟨numGen - 2, by omega⟩ ⟨numGen - 1, by omega⟩ = 4) ∧

  (∀ i j : Fin numGen, i.val + 2 ≤ j.val → m i j = 2)

/-- Combinatorial characterisation of an affine Coxeter matrix of type
$\tilde D_n$: symmetric matrix with diagonal $1$ and all off-diagonal labels
in $\{2, 3\}$. -/
def IsAffineDn (numGen : ℕ) (m : Fin numGen → Fin numGen → ℕ) : Prop :=
  numGen ≥ 5 ∧
  (∀ i, m i i = 1) ∧
  (∀ i j, m i j = m j i) ∧


  (∀ i j : Fin numGen, i ≠ j → m i j = 2 ∨ m i j = 3)

/-- Combinatorial characterisation of an affine Coxeter matrix of type
$\tilde B_n$: symmetric, diagonal $1$, with at least one entry equal to $4$
and all off-diagonal labels in $\{2, 3, 4\}$. -/
def IsAffineBn (numGen : ℕ) (m : Fin numGen → Fin numGen → ℕ) : Prop :=
  numGen ≥ 4 ∧
  (∀ i, m i i = 1) ∧
  (∀ i j, m i j = m j i) ∧

  (∃ i j : Fin numGen, m i j = 4) ∧
  (∀ i j : Fin numGen, i ≠ j → m i j = 2 ∨ m i j = 3 ∨ m i j = 4)

/-- Explicit construction of the affine $\tilde C_n$ Coxeter matrix on $n+1$
generators: labels $4$ on the two end edges, $3$ on interior edges, and $2$
elsewhere. -/
def affineCnMatrix (n : ℕ) (_hn : n ≥ 2) :
    Fin (n + 1) → Fin (n + 1) → ℕ :=
  fun i j =>
    if i.val = j.val then 1
    else
      let lo := min i.val j.val
      let hi := max i.val j.val
      if hi = lo + 1 then
        if lo = 0 ∨ hi = n then 4 else 3
      else 2

/-- Explicit construction of the affine $\tilde D_n$ Coxeter matrix on $n+1$
generators: labels $3$ on the edges of the $\tilde D_n$ Dynkin diagram and
$2$ elsewhere. -/
def affineDnMatrix (n : ℕ) (_hn : n ≥ 4) :
    Fin (n + 1) → Fin (n + 1) → ℕ :=
  fun i j =>
    if i = j then 1
    else
      let lo := min i.val j.val
      let hi := max i.val j.val
      if (lo = 0 ∧ hi = 2) ∨ (lo = 1 ∧ hi = 2) ∨
         (lo ≥ 2 ∧ hi = lo + 1 ∧ hi ≤ n - 2) ∨
         (lo = n - 2 ∧ hi = n - 1) ∨ (lo = n - 2 ∧ hi = n)
      then 3
      else 2

/-- Explicit construction of the affine $\tilde B_n$ Coxeter matrix on $n+1$
generators: a single label-$4$ edge at the right end, label $3$ on the
interior diagram, and $2$ elsewhere. -/
def affineBnMatrix (n : ℕ) (_hn : n ≥ 3) :
    Fin (n + 1) → Fin (n + 1) → ℕ :=
  fun i j =>
    if i = j then 1
    else
      let lo := min i.val j.val
      let hi := max i.val j.val
      if lo = n - 1 ∧ hi = n then 4
      else if (lo = 0 ∧ hi = 2) ∨ (lo = 1 ∧ hi = 2) ∨
              (lo ≥ 2 ∧ hi = lo + 1 ∧ hi ≤ n - 1)
      then 3
      else 2

/-- The alternating-form building has affine Coxeter type $\tilde C_n$. -/
def AlternatingBuildingCoxeterType
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (_X : AffineAlternatingComplex C B)
    (wittIndex : ℕ) : Prop :=
  ∃ (m : Fin (wittIndex + 1) → Fin (wittIndex + 1) → ℕ),
    IsAffineCn (wittIndex + 1) m

/-- The double oriflamme building has affine Coxeter type $\tilde D_n$. -/
def DoubleOriflammeBuildingCoxeterType
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) (_X : DoubleOriflammeComplex C B halfDim) : Prop :=
  ∃ (m : Fin (halfDim + 1) → Fin (halfDim + 1) → ℕ),
    IsAffineDn (halfDim + 1) m

/-- The single oriflamme building has affine Coxeter type $\tilde B_n$. -/
def SingleOriflammeBuildingCoxeterType
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (_X : SingleOriflammeComplex C B)
    (wittIndex : ℕ) : Prop :=
  ∃ (m : Fin (wittIndex + 1) → Fin (wittIndex + 1) → ℕ),
    IsAffineBn (wittIndex + 1) m

end AffineIsometryBuilding
