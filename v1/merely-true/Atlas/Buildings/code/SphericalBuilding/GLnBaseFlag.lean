/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The $i$-th subspace of the standard flag: the span of the first $i+1$ standard basis
vectors in $k^n$. -/
noncomputable def stdFlagSubspace (i : Fin (n - 1)) : Submodule k (Vec k n) :=
  Submodule.span k (Set.range (fun (j : Fin (i.val + 1)) =>
    (Pi.basisFun k (Fin n)) (⟨j.val, by omega⟩ : Fin n)))

/-- The chosen generators of `stdFlagSubspace k n i` are linearly independent. -/
theorem stdFlagSubspace_generators_linIndep (i : Fin (n - 1)) :
    LinearIndependent k (fun (j : Fin (i.val + 1)) =>
      (Pi.basisFun k (Fin n)) (⟨j.val, by omega⟩ : Fin n)) := by
  apply (Pi.basisFun k (Fin n)).linearIndependent.comp
  intro a b hab
  exact Fin.ext (by simp [Fin.ext_iff] at hab; exact hab)

/-- $\dim_k(\mathrm{stdFlagSubspace}\ k\ n\ i) = i + 1$. -/
theorem stdFlagSubspace_finrank (i : Fin (n - 1)) :
    Module.finrank k ↥(stdFlagSubspace k n i) = i.val + 1 := by
  rw [stdFlagSubspace, finrank_span_eq_card (stdFlagSubspace_generators_linIndep k n i)]
  simp [Fintype.card_fin]


/-- Standard flag subspaces are monotone in the index. -/
theorem stdFlagSubspace_mono {i j : Fin (n - 1)} (h : i ≤ j) :
    stdFlagSubspace k n i ≤ stdFlagSubspace k n j := by
  apply Submodule.span_mono
  intro x hx
  obtain ⟨m, rfl⟩ := hx
  exact ⟨⟨m.val, by omega⟩, by simp⟩

/-- Standard flag subspaces are strictly monotone in the index. -/
theorem stdFlagSubspace_strictMono {i j : Fin (n - 1)} (h : i < j) :
    stdFlagSubspace k n i < stdFlagSubspace k n j := by
  apply Submodule.lt_of_le_of_finrank_lt_finrank (stdFlagSubspace_mono k n h.le)
  rw [stdFlagSubspace_finrank, stdFlagSubspace_finrank]
  omega


/-- Each standard flag subspace is non-zero. -/
theorem stdFlagSubspace_ne_bot (i : Fin (n - 1)) :
    stdFlagSubspace k n i ≠ ⊥ := by
  intro h
  have h1 := stdFlagSubspace_finrank k n i
  rw [h] at h1
  simp at h1

/-- Each standard flag subspace is a proper subspace of $k^n$. -/
theorem stdFlagSubspace_ne_top (i : Fin (n - 1)) :
    stdFlagSubspace k n i ≠ ⊤ := by
  intro h
  have h1 := stdFlagSubspace_finrank k n i
  rw [h] at h1
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  omega


/-- The complete standard flag in $k^n$ as a list of subspaces of length $n-1$. -/
noncomputable def stdFlagChain : List (Submodule k (Vec k n)) :=
  List.ofFn (stdFlagSubspace k n)

/-- The standard flag chain has length $n-1$. -/
theorem stdFlagChain_length : (stdFlagChain k n).length = n - 1 :=
  List.length_ofFn

/-- The standard flag chain is strictly increasing. -/
theorem stdFlagChain_isChain :
    (stdFlagChain k n).IsChain (· < ·) := by
  rw [stdFlagChain, List.isChain_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp [List.length_ofFn] at hi hj
  rw [List.getElem_ofFn, List.getElem_ofFn]
  exact stdFlagSubspace_strictMono k n (Fin.mk_lt_mk.mpr hij)

/-- Every subspace in the standard flag chain is proper and non-zero. -/
theorem stdFlagChain_proper :
    ∀ V ∈ stdFlagChain k n, V ≠ ⊥ ∧ V ≠ ⊤ := by
  intro V hV
  rw [stdFlagChain, List.mem_ofFn] at hV
  obtain ⟨i, rfl⟩ := hV
  exact ⟨stdFlagSubspace_ne_bot k n i, stdFlagSubspace_ne_top k n i⟩


/-- The standard flag witnesses the existence of a `BaseFlagHyp k n`, providing a fixed
maximal flag to which we may refine arbitrary subspaces. -/
noncomputable def baseFlagHyp : BaseFlagHyp k n where
  base_chain := stdFlagChain k n
  base_chain_is_chain := stdFlagChain_isChain k n
  base_chain_length := stdFlagChain_length k n
  base_chain_proper := stdFlagChain_proper k n

end GLnBuilding
