/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.RefinementFrame
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.Fin

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The set of indices $\{j : j < i\}$ used to assemble $V_i$ from the first $i$ frame lines. -/
def sigmaWitness (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i.val)

/-- The cardinality of `sigmaWitness i` is $i$. -/
theorem card_sigmaWitness_eq (i : Fin (n + 1)) :
    (sigmaWitness i).card = i.val := by
  simp only [sigmaWitness]
  rw [show Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ =
    Finset.univ.filter (fun j : Fin n => (j : ℕ) < i.val) from rfl]
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (by omega)

/-- If $j < i$ then the $j$-th gap vector of a strict flag lies in $V_i$. -/
theorem gapVector_mem_of_lt {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (j : Fin n) (i : Fin (n + 1))
    (hjlt : j.val < i.val) :
    hσ.gapVector j ∈ σ.spaces i :=
  hσ.gapVector_mem_of_le j i (by omega)

/-- For a linearly independent family $\{v_i\}$ and a finite subset $S$, the dimension of
$\bigvee_{i \in S} k \cdot v_i$ equals $|S|$. -/
theorem finrank_biSup_span_singleton_eq_card {M : Type*}
    [AddCommGroup M] [Module k M]
    {ι : Type*} [Fintype ι] {v : ι → M}
    (hli : LinearIndependent k v) (S : Finset ι) :
    Module.finrank k ↥(⨆ i ∈ S, k ∙ v i) = S.card := by
  have heq : (⨆ i ∈ S, k ∙ v i) =
      Submodule.span k (Set.range (fun j : (S : Set ι) => v j)) := by
    conv_lhs => rw [show (⨆ i ∈ S, k ∙ v i) = ⨆ i : (S : Set ι), k ∙ v ↑i from by
      simp [iSup_subtype']]
    rw [← Submodule.span_range_eq_iSup]
  rw [heq]
  have hli' := hli.comp (fun j : (S : Set ι) => (j : ι)) Subtype.val_injective
  have : Set.range (fun j : (S : Set ι) => v ↑j) = Set.range (v ∘ fun j : (S : Set ι) => (j : ι)) := by
    ext; simp [Function.comp]
  rw [this, finrank_span_eq_card hli']
  simp [Fintype.card_coe]

/-- Equality criterion: $\bigvee_{i \in S} k \cdot v_i = W$ whenever the left side is contained
in $W$ and their dimensions agree. -/
theorem biSup_span_singleton_eq_of_le_of_finrank {M : Type*}
    [AddCommGroup M] [Module k M]
    {ι : Type*} [Fintype ι] {v : ι → M}
    (hli : LinearIndependent k v) (S : Finset ι)
    (W : Submodule k M) [FiniteDimensional k W]
    (hle : (⨆ i ∈ S, k ∙ v i) ≤ W)
    (hfr : Module.finrank k W = S.card) :
    (⨆ i ∈ S, k ∙ v i) = W := by
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_biSup_span_singleton_eq_card hli S, hfr]

/-- **Refinement compatibility**: each subspace $V_i$ of a strict flag $\sigma$ is reconstructed
from the refinement frame as $V_i = \bigvee_{j < i} (\text{frame line } j)$. -/
theorem refinementFrame_sigma_eq {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) [FiniteDimensional k (Vec k n)]
    (i : Fin (n + 1)) :
    (⨆ j ∈ sigmaWitness i, (refinementFrame hσ).lines j) = σ.spaces i := by
  have hFD : FiniteDimensional k ↥(σ.spaces i) :=
    FiniteDimensional.finiteDimensional_submodule (σ.spaces i)

  have hle : (⨆ j ∈ sigmaWitness i, (refinementFrame hσ).lines j) ≤ σ.spaces i := by
    apply iSup_le; intro j; apply iSup_le; intro hj
    simp only [sigmaWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show k ∙ hσ.gapVector j ≤ σ.spaces i
    rw [Submodule.span_singleton_le_iff_mem]
    exact gapVector_mem_of_lt hσ j i hj

  have hfr : Module.finrank k ↥(σ.spaces i) = (sigmaWitness i).card := by
    rw [hσ i, card_sigmaWitness_eq]

  exact biSup_span_singleton_eq_of_le_of_finrank
    hσ.linearIndependent_gapVectors (sigmaWitness i) (σ.spaces i) hle hfr

end GLnBuilding
