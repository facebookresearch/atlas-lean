/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps

set_option maxHeartbeats 800000

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- For any monotone $g : \{0, \dots, n\} \to \mathbb{N}$ with step increments $\le 1$ and
total increase $g(n) = g(0) + 1$, there is a **unique** index $j$ where $g$ jumps by $1$. -/
theorem existsUnique_step_jump {n : ℕ} (g : Fin (n + 1) → ℕ)
    (hmono : Monotone g)
    (hstep : ∀ j : Fin n, g ⟨j.val + 1, by omega⟩ ≤ g ⟨j.val, by omega⟩ + 1)
    (htotal : g ⟨n, by omega⟩ = g ⟨0, by omega⟩ + 1) :
    ∃! j : Fin n, g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 := by

  have hexist : ∃ j : Fin n, g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 := by
    by_contra hall
    push_neg at hall
    have hconst : ∀ (k : ℕ) (hk : k < n + 1), g ⟨k, hk⟩ = g ⟨0, by omega⟩ := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hkn : k < n := by omega
        have hmono_step : g ⟨k, by omega⟩ ≤ g ⟨k + 1, hk⟩ :=
          hmono (Fin.mk_le_mk.mpr (by omega))
        have hno_jump := hall ⟨k, hkn⟩
        have hstep_k := hstep ⟨k, hkn⟩
        have hprev := ih (by omega)
        simp only at hno_jump hstep_k hprev
        omega
    have h0 := hconst n (by omega)
    omega

  have huniq : ∀ j j' : Fin n,
      g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 →
      g ⟨j'.val + 1, by omega⟩ = g ⟨j'.val, by omega⟩ + 1 → j = j' := by
    intro j j' hj hj'
    by_contra h
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hjlt | hjlt
    · have hge2 : g ⟨j'.val, by omega⟩ ≥ g ⟨j.val + 1, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hle : g ⟨j'.val + 1, by omega⟩ ≤ g ⟨n, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hge : g ⟨j.val, by omega⟩ ≥ g ⟨0, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      omega
    · have hge2 : g ⟨j.val, by omega⟩ ≥ g ⟨j'.val + 1, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hle : g ⟨j.val + 1, by omega⟩ ≤ g ⟨n, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hge : g ⟨j'.val, by omega⟩ ≥ g ⟨0, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      omega
  obtain ⟨j, hj⟩ := hexist
  exact ⟨j, hj, fun j' hj' => huniq j' j hj' hj⟩

/-- Monotonicity of the Schreier cell dimensions along the second index. -/
theorem schreierCell_finrank_mono (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j j' : Fin (n + 1)) (hjj' : j ≤ j') :
    Module.finrank k ↥(schreierCell σ τ i hi j) ≤
    Module.finrank k ↥(schreierCell σ τ i hi j') :=
  Submodule.finrank_mono (schreierCell_mono σ τ i hi j j' hjj')

/-- For each row $i > 0$ of the Schreier refinement of $\sigma$ by $\tau$, there is a unique
column $j$ where the dimension jumps from $\dim(\sigma_{i-1} + \sigma_i \cap \tau_j)$ to
$\dim(\sigma_{i-1} + \sigma_i \cap \tau_{j+1})$ by exactly $1$. -/
theorem existsUnique_jump_col (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ∃! j : Fin n,
      Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) =
      Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1 := by
  exact existsUnique_step_jump
    (fun j => Module.finrank k ↥(schreierCell σ τ i hi j))
    (fun _ _ hab => Submodule.finrank_mono (schreierCell_mono σ τ i hi _ _ hab))
    (fun j => schreierCell_finrank_step σ τ hτ i hi j)
    (schreierCell_row_total σ τ hσ i hi)

/-- The **Schreier refinement permutation**: for each row $i$, `jumpCol` returns the unique
column $j$ where the refinement increases in dimension, giving the bijection between the
composition factors of $\sigma$ and those of $\tau$. -/
noncomputable def jumpCol (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) : Fin n :=
  (existsUnique_jump_col σ τ hσ hτ i hi).exists.choose

/-- Defining property: at column $j = $ `jumpCol`, the Schreier cell dimension jumps by exactly $1$. -/
theorem jumpCol_spec (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) =
    Module.finrank k ↥(schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩) + 1 :=
  (existsUnique_jump_col σ τ hσ hτ i hi).exists.choose_spec

/-- Uniqueness: any column where the Schreier cell dimension jumps must equal `jumpCol`. -/
theorem jumpCol_unique (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j : Fin n)
    (hj : Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) =
          Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1) :
    j = jumpCol σ τ hσ hτ i hi := by
  exact (existsUnique_jump_col σ τ hσ hτ i hi).unique hj (jumpCol_spec σ τ hσ hτ i hi)

/-- At the jump column, the Schreier cell strictly increases. -/
theorem schreierCell_lt_at_jumpCol (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ <
    schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ := by
  set jc := jumpCol σ τ hσ hτ i hi
  apply lt_of_le_of_ne
  · exact schreierCell_mono σ τ i hi ⟨jc.val, by omega⟩ ⟨jc.val + 1, by omega⟩
      (Fin.mk_le_mk.mpr (by omega))
  · intro heq
    have hspec := jumpCol_spec σ τ hσ hτ i hi
    rw [heq] at hspec
    omega

/-- Key non-containment: $V_i \cap W_{j+1}$ is not contained in $V_{i-1}$ at the jump column $j$,
ensuring existence of the Jordan-Hölder gap vector. -/
theorem vi_inter_wj_not_le_vim1 (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ¬(σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ≤
      σ.spaces ⟨i.val - 1, by omega⟩) := by
  intro hle
  have hlt := schreierCell_lt_at_jumpCol σ τ hσ hτ i hi

  have heq_sup : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ ⊔
        (σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) :=
    schreierCell_eq_sup σ τ i hi _

  have hsup_eq : σ.spaces ⟨i.val - 1, by omega⟩ ⊔
      (σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩) =
      σ.spaces ⟨i.val - 1, by omega⟩ := sup_eq_left.mpr hle

  have hcell_eq_vim1 : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ := by rw [heq_sup, hsup_eq]
  have hzero : schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ := schreierCell_zero σ τ i hi

  have hle_cell : schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ≤
      schreierCell σ τ i hi ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ := by
    rw [hcell_eq_vim1, ← hzero]
    exact schreierCell_mono σ τ i hi ⟨0, Nat.zero_lt_succ n⟩
      ⟨(jumpCol σ τ hσ hτ i hi).val, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
  exact absurd hle_cell (not_le_of_gt hlt)

/-- Existence of a Jordan-Hölder gap vector: a vector $v \in V_i \cap W_{j+1}$ with $v \notin V_{i-1}$. -/
theorem exists_jhGapVector (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ∃ v : Vec k n,
      v ∈ σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ ∧
      v ∉ σ.spaces ⟨i.val - 1, by omega⟩ := by
  have hle := vi_inter_wj_not_le_vim1 σ τ hσ hτ i hi
  rw [SetLike.not_le_iff_exists] at hle
  exact hle

/-- Choice of the **Jordan-Hölder gap vector** at row $i$: an explicit witness in
$V_i \cap W_{j+1} \setminus V_{i-1}$ where $j$ is the jump column. -/
noncomputable def jhGapVector (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) : Vec k n :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose

/-- The Jordan-Hölder gap vector lies in $V_i \cap W_{j+1}$. -/
theorem jhGapVector_mem_inf (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈
      σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose_spec.1

/-- The Jordan-Hölder gap vector does not lie in $V_{i-1}$. -/
theorem jhGapVector_not_mem_lower (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∉ σ.spaces ⟨i.val - 1, by omega⟩ :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose_spec.2

/-- The Jordan-Hölder gap vector lies in $V_i$. -/
theorem jhGapVector_mem_Vi (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈ σ.spaces i :=
  (Submodule.mem_inf.mp (jhGapVector_mem_inf σ τ hσ hτ i hi)).1

/-- The Jordan-Hölder gap vector lies in $W_{j+1}$, where $j$ is the jump column. -/
theorem jhGapVector_mem_Wj (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈
      τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ :=
  (Submodule.mem_inf.mp (jhGapVector_mem_inf σ τ hσ hτ i hi)).2

/-- The Jordan-Hölder gap vector is nonzero. -/
theorem jhGapVector_ne_zero (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ≠ 0 := by
  intro heq
  exact jhGapVector_not_mem_lower σ τ hσ hτ i hi
    (heq ▸ (σ.spaces ⟨i.val - 1, by omega⟩).zero_mem)

end GLnBuilding
