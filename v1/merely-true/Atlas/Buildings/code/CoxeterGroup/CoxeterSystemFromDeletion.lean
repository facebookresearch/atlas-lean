/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement

open Function Set

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- For involutions $\mathtt{gen}\,s$ and $\mathtt{gen}\,t$, the products
$(\mathtt{gen}\,s)(\mathtt{gen}\,t)$ and $(\mathtt{gen}\,t)(\mathtt{gen}\,s)$
have the same order, since they are conjugate via $\mathtt{gen}\,s$. -/
theorem orderOf_mul_comm_of_involution
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1) (s t : B) :
    orderOf (gen s * gen t) = orderOf (gen t * gen s) := by
  have h : SemiconjBy (gen s) (gen s * gen t) (gen t * gen s) := by
    show gen s * (gen s * gen t) = gen t * gen s * gen s
    rw [← mul_assoc, hgen_inv, one_mul, mul_assoc, hgen_inv, mul_one]
  exact h.orderOf_eq

/-- The Coxeter matrix canonically associated to a family of involutions
$\mathtt{gen} : B \to W$ with no nontrivial relations $\mathtt{gen}\,s
\cdot \mathtt{gen}\,t = 1$ for $s \ne t$: the $(s,t)$-entry is the order of
$\mathtt{gen}\,s \cdot \mathtt{gen}\,t$ in $W$. -/
noncomputable def deletionCoxeterMatrix
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) : CoxeterMatrix B where
  M := Matrix.of fun s t => orderOf (gen s * gen t)
  isSymm := by
    ext s t
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact (orderOf_mul_comm_of_involution gen hgen_inv s t).symm
  diagonal s := by
    simp only [Matrix.of_apply]
    rw [hgen_inv s, orderOf_one]
  off_diagonal s t hne := by
    simp only [Matrix.of_apply]
    intro h
    exact hgen_ne s t hne (orderOf_eq_one_iff.mp h)

/-- The family $\mathtt{gen}$ satisfies the lifting hypothesis for the
canonically associated Coxeter matrix: each pairwise relation
$(\mathtt{gen}\,s \cdot \mathtt{gen}\,t)^{m(s,t)} = 1$ holds tautologically by
the definition of order. -/
theorem deletionCoxeterMatrix_isLiftable
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
    (deletionCoxeterMatrix gen hgen_inv hgen_ne).IsLiftable gen := by
  intro s t
  show (gen s * gen t) ^ (Matrix.of fun s' t' => orderOf (gen s' * gen t')) s t = 1
  simp only [Matrix.of_apply]
  exact pow_orderOf_eq_one _

/-- The canonical group homomorphism from the abstract Coxeter group on $B$
(with the matrix induced by the family $\mathtt{gen}$) to $W$, sending each
generator $\mathtt{simple}\,s$ to $\mathtt{gen}\,s$. -/
noncomputable def deletionCanonicalHom
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
    (deletionCoxeterMatrix gen hgen_inv hgen_ne).Group →* W :=
  (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.lift
    ⟨gen, deletionCoxeterMatrix_isLiftable gen hgen_inv hgen_ne⟩

/-- The canonical homomorphism sends the abstract simple generator
$\mathtt{simple}\,s$ to the concrete involution $\mathtt{gen}\,s$. -/
theorem deletionCanonicalHom_apply_simple
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) (s : B) :
    deletionCanonicalHom gen hgen_inv hgen_ne
      ((deletionCoxeterMatrix gen hgen_inv hgen_ne).simple s) = gen s :=
  (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.lift_apply_simple
    (deletionCoxeterMatrix_isLiftable gen hgen_inv hgen_ne) s

/-- If the image of $\mathtt{gen}$ generates $W$, then the canonical
homomorphism from the abstract Coxeter group to $W$ is surjective. -/
theorem deletionCanonicalHom_surjective
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤) :
    Function.Surjective (deletionCanonicalHom gen hgen_inv hgen_ne) := by
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff, ← hgen_surj, Subgroup.closure_le]
  intro w hw
  obtain ⟨s, rfl⟩ := hw
  exact ⟨(deletionCoxeterMatrix gen hgen_inv hgen_ne).simple s,
    deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s⟩

/-- The deletion condition for a family of generators $\mathtt{gen} : B \to W$:
whenever a word $\omega$ in $B$ can be shortened (its $\mathtt{gen}$-product
equals that of a strictly shorter word), there exist two indices $i < j$ in
$\omega$ whose deletion preserves the product. -/
def SatisfiesDeletionConditionGen (gen : B → W) : Prop :=
  ∀ (word : List B),
    (∃ (shorter : List B), shorter.length < word.length ∧
      (shorter.map gen).prod = (word.map gen).prod) →
    ∃ (i j : ℕ), i < j ∧ j < word.length ∧
      (((word.eraseIdx j).eraseIdx i).map gen).prod = (word.map gen).prod

end CoxeterSystemFromDeletion
