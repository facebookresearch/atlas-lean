/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- Strict flags are strictly increasing: $V_i \subsetneq V_{i+1}$. -/
theorem CompleteFlag.IsStrictFlag.spaces_lt {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) :
    σ.spaces ⟨i.val, by omega⟩ < σ.spaces ⟨i.val + 1, by omega⟩ := by
  rw [lt_iff_le_and_ne]
  constructor
  · exact σ.monotone (Fin.mk_le_mk.mpr (by omega))
  · intro h
    have h1 := hσ ⟨i.val, by omega⟩
    have h2 := hσ ⟨i.val + 1, by omega⟩
    simp only at h1 h2
    rw [h] at h1; omega

/-- Choice of a **gap vector** at step $i$ of a strict flag: a vector in $V_{i+1} \setminus V_i$. -/
noncomputable def CompleteFlag.IsStrictFlag.gapVector {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) : Vec k n :=
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose

/-- The gap vector lies in $V_{i+1}$. -/
theorem CompleteFlag.IsStrictFlag.gapVector_mem {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) :
    hσ.gapVector i ∈ σ.spaces ⟨i.val + 1, by omega⟩ :=
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose_spec.1

/-- The gap vector does not lie in $V_i$. -/
theorem CompleteFlag.IsStrictFlag.gapVector_not_mem {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) :
    hσ.gapVector i ∉ σ.spaces ⟨i.val, by omega⟩ :=
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose_spec.2

/-- The gap vector is nonzero. -/
theorem CompleteFlag.IsStrictFlag.gapVector_ne_zero {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) :
    hσ.gapVector i ≠ 0 := by
  intro h
  exact hσ.gapVector_not_mem i (h ▸ zero_mem _)

/-- Monotonicity: if $i + 1 \le j$ then the $i$-th gap vector lies in $V_j$. -/
theorem CompleteFlag.IsStrictFlag.gapVector_mem_of_le {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) (j : Fin (n + 1)) (hij : i.val + 1 ≤ j.val) :
    hσ.gapVector i ∈ σ.spaces j :=
  σ.monotone (Fin.mk_le_mk.mpr hij) (hσ.gapVector_mem i)

/-- The $n$ gap vectors $\{v_i\}_{i < n}$ of a strict flag are linearly independent. -/
theorem CompleteFlag.IsStrictFlag.linearIndependent_gapVectors {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) :
    LinearIndependent k (fun i : Fin n => hσ.gapVector i) := by

  suffices ∀ (m : ℕ) (hm : m ≤ n),
      LinearIndependent k (fun i : Fin m => hσ.gapVector ⟨i.val, by omega⟩) by
    have h := this n le_rfl
    convert h using 1
  intro m
  induction m with
  | zero => intro _; exact linearIndependent_empty_type
  | succ p ih =>
    intro hp
    rw [linearIndependent_fin_succ']
    constructor
    ·
      convert ih (by omega) using 1
    ·
      intro hmem

      have hspan_le : Submodule.span k (Set.range (Fin.init (fun i : Fin (p + 1) =>
          hσ.gapVector ⟨i.val, by omega⟩))) ≤ σ.spaces ⟨p, by omega⟩ := by
        rw [Submodule.span_le]
        rintro x ⟨⟨j, hj⟩, rfl⟩
        simp only [Fin.init]
        exact hσ.gapVector_mem_of_le ⟨j, by omega⟩ ⟨p, by omega⟩ (by simp; omega)

      exact hσ.gapVector_not_mem ⟨p, by omega⟩ (hspan_le hmem)

/-- The gap vectors span all of $k^n$, hence form a basis. -/
theorem CompleteFlag.IsStrictFlag.span_gapVectors_eq_top {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Submodule.span k (Set.range (fun i : Fin n => hσ.gapVector i)) = ⊤ := by
  apply hσ.linearIndependent_gapVectors.span_eq_top_of_card_eq_finrank'
  simp

/-- The **refinement frame** of a strict flag: the apartment frame whose lines are spanned by
the gap vectors $v_i$, giving an apartment containing $\sigma$ as a chamber. -/
noncomputable def refinementFrame {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) [FiniteDimensional k (Vec k n)] : Frame k n where
  lines i := k ∙ (hσ.gapVector i)
  one_dim i := finrank_span_singleton (hσ.gapVector_ne_zero i)
  indep := hσ.linearIndependent_gapVectors.iSupIndep_span_singleton
  spanning := by
    rw [← Submodule.span_range_eq_iSup]
    exact hσ.span_gapVectors_eq_top

/-- Wrapper: the refinement frame of a strict flag $\sigma$, ignoring a second flag $\tau$. -/
noncomputable def refinementFrameFromPair (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (_hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Frame k n :=
  refinementFrame hσ

end GLnBuilding
