/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation
import Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility

set_option maxHeartbeats 800000

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The $i$-th **Jordan-Hölder line vector** for two complete strict flags $\sigma, \tau$: a
nonzero vector representing the gap $V_{i+1}/V_i$ in the Schreier refinement of $\sigma$ by $\tau$. -/
noncomputable def jhLine (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) : Vec k n :=
  jhGapVector σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

/-- The Jordan-Hölder line vector $\ell_i$ lies in $V_{i+1}$ of the flag $\sigma$. -/
theorem jhLine_mem_Vi_succ (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ∈ σ.spaces ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ :=
  jhGapVector_mem_Vi σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

/-- The Jordan-Hölder line vector $\ell_i$ does **not** lie in $V_i$, i.e., it realizes a
genuine dimension jump. -/
theorem jhLine_not_mem_Vi (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ∉ σ.spaces ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  have h := jhGapVector_not_mem_lower σ τ hσ hτ
    ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

  simp only [Nat.succ_sub_one] at h
  exact h

/-- Each Jordan-Hölder line vector is nonzero. -/
theorem jhLine_ne_zero (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ≠ 0 :=
  jhGapVector_ne_zero σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

/-- Monotonicity: if $i + 1 \le j$ then $\ell_i \in V_j$. -/
theorem jhLine_mem_of_le (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin n) (j : Fin (n + 1)) (hij : i.val + 1 ≤ j.val) :
    jhLine σ τ hσ hτ i ∈ σ.spaces j :=
  σ.monotone (Fin.mk_le_mk.mpr hij) (jhLine_mem_Vi_succ σ τ hσ hτ i)

/-- The Jordan-Hölder line vectors $\{\ell_i\}_{i < n}$ are linearly independent in $k^n$. -/
theorem jhLine_linearIndependent (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) :
    LinearIndependent k (fun i : Fin n => jhLine σ τ hσ hτ i) := by
  suffices ∀ (m : ℕ) (hm : m ≤ n),
      LinearIndependent k (fun i : Fin m => jhLine σ τ hσ hτ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) by
    have h := this n le_rfl
    convert h using 1
  intro m
  induction m with
  | zero => intro _; exact linearIndependent_empty_type
  | succ p ih =>
    intro hp
    rw [linearIndependent_fin_succ']
    constructor
    · convert ih (by omega) using 1
    · intro hmem
      have hspan_le : Submodule.span k (Set.range (Fin.init (fun i : Fin (p + 1) =>
          jhLine σ τ hσ hτ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hp⟩))) ≤ σ.spaces ⟨p, Nat.lt_succ_of_lt (by omega)⟩ := by
        rw [Submodule.span_le]
        rintro x ⟨⟨j, hj⟩, rfl⟩
        simp only [Fin.init]
        exact jhLine_mem_of_le σ τ hσ hτ ⟨j, by omega⟩ ⟨p, by omega⟩ (by simp; omega)
      exact jhLine_not_mem_Vi σ τ hσ hτ ⟨p, by omega⟩ (hspan_le hmem)

/-- The span of the $n$ Jordan-Hölder line vectors equals all of $k^n$. -/
theorem jhLine_span_eq_top (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Submodule.span k (Set.range (fun i : Fin n => jhLine σ τ hσ hτ i)) = ⊤ := by
  apply (jhLine_linearIndependent σ τ hσ hτ).span_eq_top_of_card_eq_finrank'
  simp

/-- The **Jordan-Hölder frame** of two complete flags $\sigma, \tau$: the apartment frame
whose lines are spanned by the Jordan-Hölder gap vectors $\ell_i$, simultaneously refining both
flags. -/
noncomputable def jordanHolderFrame (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Frame k n where
  lines i := k ∙ (jhLine σ τ hσ hτ i)
  one_dim i := finrank_span_singleton (jhLine_ne_zero σ τ hσ hτ i)
  indep := (jhLine_linearIndependent σ τ hσ hτ).iSupIndep_span_singleton
  spanning := by
    rw [← Submodule.span_range_eq_iSup]
    exact jhLine_span_eq_top σ τ hσ hτ

/-- The Jordan-Hölder frame is compatible with the flag $\sigma$: each subspace $V_i$ of
$\sigma$ is a sum of frame lines, namely $V_i = \bigoplus_{j < i} k \cdot \ell_j$. -/
theorem jordanHolderFrame_compatible_sigma (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)]
    (i : Fin (n + 1)) :
    (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (σ.spaces i) := by
  use sigmaWitness i
  have hFD : FiniteDimensional k ↥(σ.spaces i) :=
    FiniteDimensional.finiteDimensional_submodule (σ.spaces i)
  symm
  apply biSup_span_singleton_eq_of_le_of_finrank (jhLine_linearIndependent σ τ hσ hτ)
  · apply iSup_le; intro j; apply iSup_le; intro hj
    simp only [sigmaWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show k ∙ jhLine σ τ hσ hτ j ≤ σ.spaces i
    rw [Submodule.span_singleton_le_iff_mem]
    exact jhLine_mem_of_le σ τ hσ hτ j i (by omega)
  · rw [hσ i, card_sigmaWitness_eq]

end GLnBuilding
