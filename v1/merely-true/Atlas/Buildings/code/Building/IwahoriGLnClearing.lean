/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Atlas.Buildings.code.Building.DiagBlockEmbed

set_option maxHeartbeats 6400000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section Clearing

variable {n : ℕ}

/-- Decomposition of a dot-product when row $i$ of $g$ is lower-triangular with $1$ on the
diagonal: $\sum_k g_{ik} h_k = h_i + \sum_{k < i} g_{ik} h_k$. -/
lemma sum_lower_row (g : Matrix (Fin n) (Fin n) C.k) (h : Fin n → C.k) (i : Fin n)
    (hdiag : g i i = 1) (hzero : ∀ k : Fin n, k.val > i.val → g i k = 0) :
    ∑ k, g i k * h k = h i + ∑ k ∈ Finset.univ.filter (fun k => k.val < i.val), g i k * h k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, one_mul]
  congr 1; symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ne_of_apply_ne Fin.val (by omega)
  · intro k hk1 hk2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk2
    rw [hzero k (by omega), zero_mul]

/-- Inverse of a lower unitriangular matrix vanishes strictly above the diagonal (recomputed
inside this file for the clearing-algorithm proofs). -/
lemma inv_lower_unip_above (g : GL (Fin n) C.k)
    (hdiag : ∀ i : Fin n, g.val i i = 1)
    (habove : ∀ i j : Fin n, i.val < j.val → g.val i j = 0)
    (i j : Fin n) (hij : i.val < j.val) : g⁻¹.val i j = 0 := by
  obtain ⟨m, hm⟩ := i
  change m < j.val at hij
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have hne : (⟨m, hm⟩ : Fin n) ≠ j := by intro h; simp [Fin.ext_iff] at h; omega
    have hentry : ∑ k, g.val ⟨m, hm⟩ k * g⁻¹.val k j = 0 := by
      have h : g.val * g⁻¹.val = 1 := by simp
      have := congr_fun (congr_fun h ⟨m, hm⟩) j
      simp only [Matrix.mul_apply, Matrix.one_apply, hne, ite_false] at this
      exact this
    have hdecomp := C.sum_lower_row g.val (fun k => g⁻¹.val k j) ⟨m, hm⟩ (hdiag _)
      (fun k hk => habove ⟨m, hm⟩ k hk)
    rw [hdecomp] at hentry
    have hsum_zero : ∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
        g.val ⟨m, hm⟩ x * g⁻¹.val x j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [ih k.val hk k.isLt (by omega : k.val < j.val), mul_zero]
    rw [hsum_zero, add_zero] at hentry
    exact hentry

/-- Diagonal entries of the inverse of a lower unitriangular matrix are $1$ (local recomputation). -/
lemma inv_lower_unip_diag (g : GL (Fin n) C.k)
    (hdiag : ∀ i : Fin n, g.val i i = 1)
    (habove : ∀ i j : Fin n, i.val < j.val → g.val i j = 0)
    (i : Fin n) : g⁻¹.val i i = 1 := by
  obtain ⟨m, hm⟩ := i
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have hentry : ∑ k, g.val ⟨m, hm⟩ k * g⁻¹.val k ⟨m, hm⟩ = 1 := by
      have h : g.val * g⁻¹.val = 1 := by simp
      have := congr_fun (congr_fun h ⟨m, hm⟩) ⟨m, hm⟩
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this
    have hdecomp := C.sum_lower_row g.val (fun k => g⁻¹.val k ⟨m, hm⟩) ⟨m, hm⟩ (hdiag _)
      (fun k hk => habove ⟨m, hm⟩ k hk)
    rw [hdecomp] at hentry
    have hsum_zero : ∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
        g.val ⟨m, hm⟩ x * g⁻¹.val x ⟨m, hm⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [C.inv_lower_unip_above g hdiag habove k ⟨m, hm⟩ hk, mul_zero]
    rw [hsum_zero, add_zero] at hentry
    exact hentry

/-- For a lower unitriangular Iwahori matrix $g$, the strictly-below-diagonal entries of $g^{-1}$
lie in the maximal ideal $\mathfrak m$. -/
lemma inv_lower_unip_below_in_maxideal (g : GL (Fin n) C.k)
    (hg_lower : g ∈ LowerUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n)
    (i j : Fin n) (hij : i.val > j.val) : C.isInMaxIdeal (g⁻¹.val i j) := by
  obtain ⟨hdiag_g, habove_g⟩ := hg_lower
  obtain ⟨hdiag_iw, habove_iw, hbelow_iw⟩ := hg_iwahori
  obtain ⟨m, hm⟩ := i
  change j.val < m at hij
  induction m using Nat.strongRecOn with
  | ind m ih =>

    have hne : (⟨m, hm⟩ : Fin n) ≠ j := by intro h; simp [Fin.ext_iff] at h; omega
    have hentry : ∑ k, g.val ⟨m, hm⟩ k * g⁻¹.val k j = 0 := by
      have h : g.val * g⁻¹.val = 1 := by simp
      have := congr_fun (congr_fun h ⟨m, hm⟩) j
      simp only [Matrix.mul_apply, Matrix.one_apply, hne, ite_false] at this
      exact this

    have hdecomp := C.sum_lower_row g.val (fun k => g⁻¹.val k j) ⟨m, hm⟩ (hdiag_g _)
      (fun k hk => habove_g ⟨m, hm⟩ k hk)
    rw [hdecomp] at hentry


    have hsum_in_m : C.isInMaxIdeal
        (∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g.val ⟨m, hm⟩ x * g⁻¹.val x j) := by
      apply C.isInMaxIdeal_finset_sum
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk


      have hg_mk_m : C.isInMaxIdeal (g.val ⟨m, hm⟩ k) := hbelow_iw ⟨m, hm⟩ k (by omega)


      have hginv_kj_o : C.isInO (g⁻¹.val k j) := by
        rcases lt_trichotomy k.val j.val with hlt | heq | hgt
        · rw [C.inv_lower_unip_above g hdiag_g habove_g k j hlt]; exact DVRClosure.isInO_zero
        · have : k = j := Fin.ext (by omega)
          rw [this, C.inv_lower_unip_diag g hdiag_g habove_g j]; exact DVRClosure.isInO_one
        · exact C.isInMaxIdeal_isInO (ih k.val hk k.isLt (by omega))
      exact DVRClosureGL2.isInMaxIdeal_mul_isInO hg_mk_m hginv_kj_o


    have heq : g⁻¹.val ⟨m, hm⟩ j =
        -(∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g.val ⟨m, hm⟩ x * g⁻¹.val x j) :=
      eq_neg_of_add_eq_zero_left hentry
    rw [heq]

    rw [show -∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g.val ⟨m, hm⟩ x * g⁻¹.val x j =
        (-1) * ∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g.val ⟨m, hm⟩ x * g⁻¹.val x j
      from by ring]
    exact C.isInO_mul_isInMaxIdeal (DVRClosure.isInO_neg DVRClosure.isInO_one) hsum_in_m

/-- The inverse of a lower unitriangular Iwahori matrix is again lower unitriangular and Iwahori:
the lower-unipotent Iwahori subgroup is closed under taking inverses. -/
theorem lower_unip_iwahori_inv_mem
    (g : GL (Fin n) C.k)
    (hg_lower : g ∈ LowerUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n) :
    g⁻¹ ∈ LowerUnipGLn C n ∧ g⁻¹ ∈ IwahoriGLn C n := by
  have hdiag_g := hg_lower.1
  have habove_g := hg_lower.2
  constructor
  ·
    exact ⟨C.inv_lower_unip_diag g hdiag_g habove_g,
           fun i j hij => C.inv_lower_unip_above g hdiag_g habove_g i j hij⟩
  ·
    refine ⟨?_, ?_, ?_⟩
    ·
      intro i
      rw [C.inv_lower_unip_diag g hdiag_g habove_g i]
      exact C.isUnitInO_one
    ·
      intro i j hij
      rw [C.inv_lower_unip_above g hdiag_g habove_g i j hij]
      exact DVRClosure.isInO_zero
    ·
      intro i j hij
      exact C.inv_lower_unip_below_in_maxideal g hg_lower hg_iwahori i j hij

/-- Decomposition of a dot-product when column $j$ of $g$ is upper-triangular with $1$ on the
diagonal: $\sum_k h_k g_{kj} = h_j + \sum_{k < j} h_k g_{kj}$. -/
lemma sum_upper_col (g : Matrix (Fin n) (Fin n) C.k) (h : Fin n → C.k) (j : Fin n)
    (hdiag : g j j = 1) (hzero : ∀ k : Fin n, k.val > j.val → g k j = 0) :
    ∑ k, h k * g k j = h j + ∑ k ∈ Finset.univ.filter (fun k => k.val < j.val), h k * g k j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag, mul_one]
  congr 1; symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ne_of_apply_ne Fin.val (by omega)
  · intro k hk1 hk2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk2
    rw [hzero k (by omega), mul_zero]

/-- Inverse of an upper unitriangular matrix vanishes strictly below the diagonal (recomputed
inside this file for the clearing-algorithm proofs). -/
lemma inv_upper_unip_below (g : GL (Fin n) C.k)
    (hdiag : ∀ i : Fin n, g.val i i = 1)
    (hbelow : ∀ i j : Fin n, i.val > j.val → g.val i j = 0)
    (i j : Fin n) (hij : i.val > j.val) : g⁻¹.val i j = 0 := by
  obtain ⟨m, hm⟩ := j
  change m < i.val at hij
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have hne : i ≠ (⟨m, hm⟩ : Fin n) := by intro h; simp [Fin.ext_iff] at h; omega
    have hentry : ∑ k, g⁻¹.val i k * g.val k ⟨m, hm⟩ = 0 := by
      have h : g⁻¹.val * g.val = 1 := by simp
      have := congr_fun (congr_fun h i) ⟨m, hm⟩
      simp only [Matrix.mul_apply, Matrix.one_apply, hne, ite_false] at this
      exact this
    have hdecomp := C.sum_upper_col g.val (fun k => g⁻¹.val i k) ⟨m, hm⟩ (hdiag _)
      (fun k hk => hbelow k ⟨m, hm⟩ hk)
    rw [hdecomp] at hentry
    have hsum_zero : ∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
        g⁻¹.val i x * g.val x ⟨m, hm⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [ih k.val hk k.isLt (by omega : i.val > k.val), zero_mul]
    rw [hsum_zero, add_zero] at hentry
    exact hentry

/-- Diagonal entries of the inverse of an upper unitriangular matrix are $1$ (local recomputation). -/
lemma inv_upper_unip_diag (g : GL (Fin n) C.k)
    (hdiag : ∀ i : Fin n, g.val i i = 1)
    (hbelow : ∀ i j : Fin n, i.val > j.val → g.val i j = 0)
    (i : Fin n) : g⁻¹.val i i = 1 := by
  obtain ⟨m, hm⟩ := i
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have hentry : ∑ k, g⁻¹.val ⟨m, hm⟩ k * g.val k ⟨m, hm⟩ = 1 := by
      have h : g⁻¹.val * g.val = 1 := by simp
      have := congr_fun (congr_fun h ⟨m, hm⟩) ⟨m, hm⟩
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this
    have hdecomp := C.sum_upper_col g.val (fun k => g⁻¹.val ⟨m, hm⟩ k) ⟨m, hm⟩ (hdiag _)
      (fun k hk => hbelow k ⟨m, hm⟩ hk)
    rw [hdecomp] at hentry
    have hsum_zero : ∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
        g⁻¹.val ⟨m, hm⟩ x * g.val x ⟨m, hm⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [C.inv_upper_unip_below g hdiag hbelow ⟨m, hm⟩ k hk, zero_mul]
    rw [hsum_zero, add_zero] at hentry
    exact hentry

/-- For an upper unitriangular Iwahori matrix $g$, the strictly-above-diagonal entries of $g^{-1}$
lie in the integers $\mathcal O$. -/
lemma inv_upper_unip_above_in_O (g : GL (Fin n) C.k)
    (hg_upper : g ∈ UpperUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n)
    (i j : Fin n) (hij : i.val < j.val) : C.isInO (g⁻¹.val i j) := by
  obtain ⟨hdiag_g, hbelow_g⟩ := hg_upper
  obtain ⟨hdiag_iw, habove_iw, hbelow_iw⟩ := hg_iwahori
  obtain ⟨m, hm⟩ := j
  change i.val < m at hij
  induction m using Nat.strongRecOn with
  | ind m ih =>

    have hne : i ≠ (⟨m, hm⟩ : Fin n) := by intro h; simp [Fin.ext_iff] at h; omega
    have hentry : ∑ k, g⁻¹.val i k * g.val k ⟨m, hm⟩ = 0 := by
      have h : g⁻¹.val * g.val = 1 := by simp
      have := congr_fun (congr_fun h i) ⟨m, hm⟩
      simp only [Matrix.mul_apply, Matrix.one_apply, hne, ite_false] at this
      exact this

    have hdecomp := C.sum_upper_col g.val (fun k => g⁻¹.val i k) ⟨m, hm⟩ (hdiag_g _)
      (fun k hk => hbelow_g k ⟨m, hm⟩ hk)
    rw [hdecomp] at hentry


    have hsum_in_O : C.isInO
        (∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g⁻¹.val i x * g.val x ⟨m, hm⟩) := by
      apply C.isInO_finset_sum
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk


      have hg_kj_O : C.isInO (g.val k ⟨m, hm⟩) := habove_iw k ⟨m, hm⟩ hk

      have hginv_ik_O : C.isInO (g⁻¹.val i k) := by
        rcases lt_trichotomy i.val k.val with hlt | heq | hgt
        ·
          exact ih k.val hk k.isLt hlt
        ·
          have : i = k := Fin.ext (by omega)
          rw [this, C.inv_upper_unip_diag g hdiag_g hbelow_g k]; exact DVRClosure.isInO_one
        ·
          rw [C.inv_upper_unip_below g hdiag_g hbelow_g i k hgt]; exact DVRClosure.isInO_zero
      exact DVRClosure.isInO_mul hginv_ik_O hg_kj_O

    have heq : g⁻¹.val i ⟨m, hm⟩ =
        -(∑ x ∈ Finset.univ.filter (fun k : Fin n => k.val < m), g⁻¹.val i x * g.val x ⟨m, hm⟩) :=
      eq_neg_of_add_eq_zero_left hentry
    rw [heq]
    exact DVRClosure.isInO_neg hsum_in_O

/-- The inverse of an upper unitriangular Iwahori matrix is again upper unitriangular and Iwahori:
the upper-unipotent Iwahori subgroup is closed under taking inverses. -/
theorem upper_unip_iwahori_inv_mem
    (g : GL (Fin n) C.k)
    (hg_upper : g ∈ UpperUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n) :
    g⁻¹ ∈ UpperUnipGLn C n ∧ g⁻¹ ∈ IwahoriGLn C n := by
  have hdiag_g := hg_upper.1
  have hbelow_g := hg_upper.2
  constructor
  ·
    exact ⟨C.inv_upper_unip_diag g hdiag_g hbelow_g,
           fun i j hij => C.inv_upper_unip_below g hdiag_g hbelow_g i j hij⟩
  ·
    refine ⟨?_, ?_, ?_⟩
    ·
      intro i
      rw [C.inv_upper_unip_diag g hdiag_g hbelow_g i]
      exact C.isUnitInO_one
    ·
      intro i j hij
      exact C.inv_upper_unip_above_in_O g hg_upper hg_iwahori i j hij
    ·
      intro i j hij
      rw [C.inv_upper_unip_below g hdiag_g hbelow_g i j hij]
      exact C.isInMaxIdeal_zero

/-- The product of two lower unitriangular Iwahori matrices is again lower unitriangular and
Iwahori: the lower-unipotent Iwahori subgroup is closed under multiplication. -/
theorem lower_unip_iwahori_mul_mem
    (g h : GL (Fin n) C.k)
    (hg_lower : g ∈ LowerUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n)
    (hh_lower : h ∈ LowerUnipGLn C n) (hh_iwahori : h ∈ IwahoriGLn C n) :
    g * h ∈ LowerUnipGLn C n ∧ g * h ∈ IwahoriGLn C n := by
  obtain ⟨hg_diag, hg_above⟩ := hg_lower
  obtain ⟨hh_diag, hh_above⟩ := hh_lower
  constructor
  ·
    constructor
    ·
      intro i
      have hmul : (g * h).val i i = ∑ k : Fin n, g.val i k * h.val k i := by
        show (g.val * h.val) i i = _; simp [Matrix.mul_apply]
      rw [hmul]
      have : ∑ k : Fin n, g.val i k * h.val k i = g.val i i * h.val i i := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hki) with hlt | hgt
          · simp [hh_above k i hlt]
          · simp [hg_above i k hgt]
        · intro h_abs; exact absurd (Finset.mem_univ i) h_abs
      rw [this, hg_diag i, hh_diag i, one_mul]
    ·
      intro i j hij
      have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
        show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
      rw [hmul]
      apply Finset.sum_eq_zero
      intro k _
      rcases le_or_gt k.val i.val with hki | hki
      ·
        simp [hh_above k j (by omega : k.val < j.val)]
      ·
        simp [hg_above i k hki]
  ·
    exact C.IwahoriGLn_mul_mem g h hg_iwahori hh_iwahori

/-- The product of two upper unitriangular Iwahori matrices is again upper unitriangular and
Iwahori: the upper-unipotent Iwahori subgroup is closed under multiplication. -/
theorem upper_unip_iwahori_mul_mem
    (g h : GL (Fin n) C.k)
    (hg_upper : g ∈ UpperUnipGLn C n) (hg_iwahori : g ∈ IwahoriGLn C n)
    (hh_upper : h ∈ UpperUnipGLn C n) (hh_iwahori : h ∈ IwahoriGLn C n) :
    g * h ∈ UpperUnipGLn C n ∧ g * h ∈ IwahoriGLn C n := by
  have hg_diag := hg_upper.1
  have hg_below := hg_upper.2
  have hh_diag := hh_upper.1
  have hh_below := hh_upper.2
  constructor
  ·
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    ·
      have hmul : (g * h).val i i = ∑ k : Fin n, g.val i k * h.val k i := by
        show (g.val * h.val) i i = _; simp [Matrix.mul_apply]
      rw [hmul]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · simp [hg_diag i, hh_diag i]
      · intro k _ hki
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hki) with hlt | hgt
        ·
          simp [hg_below i k hlt]
        ·
          simp [hh_below k i hgt]
    ·
      have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
        show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
      rw [hmul]
      apply Finset.sum_eq_zero
      intro k _
      rcases le_or_gt i.val k.val with hik | hik
      ·
        have hkj : k.val > j.val := by omega
        simp [hh_below k j hkj]
      ·
        simp [hg_below i k hik]
  ·
    exact IwahoriGLn_mul_mem C g h hg_iwahori hh_iwahori

/-- Inductive auxiliary for the first-column clearing step: there exists a lower unitriangular
Iwahori matrix $L$ such that $(L \cdot g)_{i, 0} = 0$ for all $0 < i \le m$ while preserving the
$(0, 0)$-entry of $g$. -/
theorem clear_first_column_aux
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1))
    (m : ℕ) (hm : m ≤ n) :
    ∃ (L : GL (Fin (n + 1)) C.k),
      L ∈ LowerUnipGLn C (n + 1) ∧
      L ∈ IwahoriGLn C (n + 1) ∧
      (∀ (i : Fin (n + 1)), 0 < i.val ∧ i.val ≤ m → (L * g).val i 0 = 0) ∧
      (L * g).val 0 0 = g.val 0 0 := by
  induction m with
  | zero =>
    refine ⟨1, ?_, ?_, ?_, ?_⟩
    ·
      constructor
      · intro i; simp [Units.val_one]
      · intro i j hij
        have hij' : i ≠ j := by intro h; subst h; omega
        simp [Units.val_one, one_apply_ne hij']
    ·
      refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
      · simp [Units.val_one]; exact C.isUnitInO_one
      · have hij' : i ≠ j := by intro h; subst h; omega
        simp [Units.val_one, one_apply_ne hij']; exact DVRClosure.isInO_zero
      · have hij' : i ≠ j := by intro h; subst h; omega
        simp [Units.val_one, one_apply_ne hij']; exact C.isInMaxIdeal_zero
    · intro i ⟨_, hi2⟩; omega
    · simp
  | succ m ih =>

    obtain ⟨L_m, hL_m_lower, hL_m_iwahori, hL_m_zeros, hL_m_diag⟩ :=
      ih (Nat.le_of_succ_le hm)


    set g' := L_m * g with hg'_def
    set idx := (⟨m + 1, by omega⟩ : Fin (n + 1)) with hidx
    have hidx_ne_zero : idx ≠ (0 : Fin (n + 1)) := by
      simp [hidx, Fin.ext_iff]
    set c := -(g.val 0 0)⁻¹ * g'.val idx 0 with hc_def

    set E := C.elimMatrix idx 0 hidx_ne_zero c with hE_def

    set L := E * L_m with hL_def
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    ·
      have hE_lower : E ∈ LowerUnipGLn C (n + 1) :=
        C.elim_matrix_lower_unitriangular idx 0 hidx_ne_zero (by simp [hidx]) c
      exact (C.lower_unip_iwahori_mul_mem E L_m hE_lower
        (C.elim_matrix_iwahori_lower idx 0 hidx_ne_zero (by simp [hidx]) c
          (by


            have hLg_iwahori := C.IwahoriGLn_mul_mem L_m g hL_m_iwahori hg
            have hg'_below : C.isInMaxIdeal (g'.val idx 0) := by
              exact hLg_iwahori.2.2 idx 0 (by simp [hidx])
            have hg00_unit := hg.1 0
            have hg00_inv_inO : C.isInO ((g.val 0 0)⁻¹) := by
              exact DVRClosure.isUnitInO_inv hg00_unit
            have hneg_inv_inO : C.isInO (-(g.val 0 0)⁻¹) := by
              exact DVRClosure.isInO_neg hg00_inv_inO
            exact C.isInO_mul_isInMaxIdeal hneg_inv_inO hg'_below))
        hL_m_lower hL_m_iwahori).1
    ·
      have hE_iwahori : E ∈ IwahoriGLn C (n + 1) :=
        C.elim_matrix_iwahori_lower idx 0 hidx_ne_zero (by simp [hidx]) c
          (by
            have hLg_iwahori := C.IwahoriGLn_mul_mem L_m g hL_m_iwahori hg
            have hg'_below : C.isInMaxIdeal (g'.val idx 0) := by
              exact hLg_iwahori.2.2 idx 0 (by simp [hidx])
            have hg00_unit := hg.1 0
            have hg00_inv_inO : C.isInO ((g.val 0 0)⁻¹) := by
              exact DVRClosure.isUnitInO_inv hg00_unit
            have hneg_inv_inO : C.isInO (-(g.val 0 0)⁻¹) := by
              exact DVRClosure.isInO_neg hg00_inv_inO
            exact C.isInO_mul_isInMaxIdeal hneg_inv_inO hg'_below)
      exact C.IwahoriGLn_mul_mem E L_m hE_iwahori hL_m_iwahori
    ·
      intro i ⟨hi_pos, hi_le⟩

      have hval_eq : (L * g).val = E.val * g'.val := by
        show (E * L_m * g).val = E.val * (L_m * g).val
        simp only [Units.val_mul, Matrix.mul_assoc]
      rcases Nat.lt_or_eq_of_le hi_le with hi_lt | hi_eq
      ·
        have hi_ne_idx : i ≠ idx := by
          intro h; subst h; simp [hidx] at hi_lt
        rw [show (L * g).val i 0 = (E.val * g'.val) i 0 from by rw [hval_eq]]
        rw [show E.val = transvection idx 0 c from C.elimMatrix_val idx 0 hidx_ne_zero c]
        rw [C.elim_matrix_mul_ne idx 0 c g'.val i 0 hi_ne_idx]
        exact hL_m_zeros i ⟨hi_pos, by omega⟩
      ·
        have hi_eq_idx : i = idx := by
          ext; simp [hidx]; omega
        subst hi_eq_idx
        rw [show (L * g).val idx 0 = (E.val * g'.val) idx 0 from by rw [hval_eq]]
        rw [show E.val = transvection idx 0 c from C.elimMatrix_val idx 0 hidx_ne_zero c]
        rw [C.elim_matrix_mul idx 0 c g'.val 0]


        rw [hc_def, hL_m_diag]

        have hg00_ne : g.val 0 0 ≠ 0 :=
          DVRClosureGL2.isUnitInO_ne_zero (hg.1 0)
        field_simp
        ring
    ·
      have hval_eq : (L * g).val = E.val * g'.val := by
        show (E * L_m * g).val = E.val * (L_m * g).val
        simp only [Units.val_mul, Matrix.mul_assoc]
      rw [show (L * g).val 0 0 = (E.val * g'.val) 0 0 from by rw [hval_eq]]
      rw [show E.val = transvection idx 0 c from C.elimMatrix_val idx 0 hidx_ne_zero c]
      rw [C.elim_matrix_mul_ne idx 0 c g'.val 0 0 (by simp [hidx, Fin.ext_iff])]
      exact hL_m_diag

/-- First-column clearing: for any Iwahori matrix $g$, there exists a lower unitriangular Iwahori
matrix $L$ such that $L \cdot g$ has zeros in every entry of the first column below the $(0,0)$
position, while preserving the $(0, 0)$-entry. -/
theorem clear_first_column (hn : n ≥ 1)
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1)) :
    ∃ (L : GL (Fin (n + 1)) C.k),
      L ∈ LowerUnipGLn C (n + 1) ∧
      L ∈ IwahoriGLn C (n + 1) ∧

      (∀ (i : Fin (n + 1)), i.val > 0 → (L * g).val i 0 = 0) ∧

      (L * g).val 0 0 = g.val 0 0 := by
  obtain ⟨L, hL_lower, hL_iwahori, hL_zeros, hL_diag⟩ :=
    C.clear_first_column_aux g hg n le_rfl
  exact ⟨L, hL_lower, hL_iwahori,
    fun i hi => hL_zeros i ⟨hi, by omega⟩, hL_diag⟩

/-- First-row clearing: given an Iwahori matrix $g$ whose first column is already cleared, there
exists an upper unitriangular Iwahori matrix $U$ such that $g \cdot U$ has zeros in the first row
to the right of the $(0,0)$ position, while preserving the first column and the $(0, 0)$-entry. -/
theorem clear_first_row (hn : n ≥ 1)
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1))
    (hcol : ∀ (i : Fin (n + 1)), i.val > 0 → g.val i 0 = 0) :
    ∃ (U : GL (Fin (n + 1)) C.k),
      U ∈ UpperUnipGLn C (n + 1) ∧
      U ∈ IwahoriGLn C (n + 1) ∧

      (∀ (j : Fin (n + 1)), j.val > 0 → (g * U).val 0 j = 0) ∧

      (∀ (i : Fin (n + 1)), i.val > 0 → (g * U).val i 0 = 0) ∧

      (g * U).val 0 0 = g.val 0 0 := by


  have hg00_unit : C.isUnitInO (g.val 0 0) := hg.1 0
  have hg00_ne : g.val 0 0 ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero hg00_unit

  suffices h : ∀ (m : ℕ) (_ : m ≤ n),
    ∃ (U : GL (Fin (n + 1)) C.k),
      U ∈ UpperUnipGLn C (n + 1) ∧
      U ∈ IwahoriGLn C (n + 1) ∧
      (∀ (j : Fin (n + 1)), 1 ≤ j.val → j.val ≤ m → (g * U).val 0 j = 0) ∧
      (∀ (i : Fin (n + 1)), i.val > 0 → (g * U).val i 0 = g.val i 0) ∧
      (g * U).val 0 0 = g.val 0 0 by
    obtain ⟨U, hU_upper, hU_iwahori, hU_cleared, hU_col0, hU_00⟩ := h n le_rfl
    exact ⟨U, hU_upper, hU_iwahori,
      fun j hj => hU_cleared j (by omega) (by omega),

      fun i hi => by rw [hU_col0 i hi]; exact hcol i hi,
      hU_00⟩
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨1, ?_, ?_, fun j hj1 hj0 => by omega, fun i hi => by simp [mul_one],
      by simp [mul_one]⟩
    ·
      constructor
      · intro i; simp [Units.val_one]
      · intro i j h
        simp [Units.val_one, Matrix.one_apply_ne (show i ≠ j from by omega)]
    ·
      refine ⟨fun i => ?_, fun i j h => ?_, fun i j h => ?_⟩
      · simp [Units.val_one]; exact C.isUnitInO_one
      · simp only [Units.val_one, Matrix.one_apply_ne (show i ≠ j from by omega)]
        exact DVRClosure.isInO_zero
      · simp only [Units.val_one, Matrix.one_apply_ne (show i ≠ j from by omega)]
        exact C.isInMaxIdeal_zero
  | succ m ih =>
    intro hm

    obtain ⟨U_prev, hUp_upper, hUp_iwahori, hUp_cleared, hUp_col0, hUp_00⟩ := ih (by omega)

    set j₀ : Fin (n + 1) := ⟨m + 1, by omega⟩ with hj₀_def
    have h0j₀ : (0 : Fin (n + 1)) ≠ j₀ := by simp [hj₀_def, Fin.ext_iff]

    set g' := g * U_prev with hg'_def

    set c := -((g.val 0 0)⁻¹ * g'.val 0 j₀) with hc_def

    set E := elimMatrix C 0 j₀ h0j₀ c with hE_def

    set U_new := U_prev * E with hU_new_def
    have hj₀_pos : (0 : Fin (n + 1)).val < j₀.val := by simp [hj₀_def]

    have hE_upper : E ∈ UpperUnipGLn C (n + 1) :=
      C.elim_matrix_upper_unitriangular 0 j₀ h0j₀ hj₀_pos c

    have hc_inO : C.isInO c := by
      apply DVRClosure.isInO_neg
      apply DVRClosure.isInO_mul
      · exact DVRClosure.isUnitInO_inv hg00_unit
      · exact C.iwahori_entry_isInO' g' (C.IwahoriGLn_mul_mem g U_prev hg hUp_iwahori) 0 j₀

    have hE_iwahori : E ∈ IwahoriGLn C (n + 1) :=
      C.elim_matrix_iwahori_upper 0 j₀ h0j₀ hj₀_pos c hc_inO

    have hval_eq : (g * U_new).val = g'.val * E.val := by
      simp only [hU_new_def, Units.val_mul, hg'_def, Matrix.mul_assoc]
    refine ⟨U_new, ?_, ?_, ?_, ?_, ?_⟩
    ·
      exact (C.upper_unip_iwahori_mul_mem U_prev E hUp_upper hUp_iwahori hE_upper hE_iwahori).1
    ·
      exact C.IwahoriGLn_mul_mem U_prev E hUp_iwahori hE_iwahori
    ·
      intro j hj1 hjm1

      have h1 : ∀ a b, (g * U_new).val a b = (g'.val * E.val) a b := by
        intro a b; exact congrFun (congrFun hval_eq a) b
      rcases eq_or_ne j j₀ with rfl | hne
      ·
        rw [h1]
        simp only [hE_def, elimMatrix_val]

        simp only [mul_transvection_apply_same]
        rw [hUp_00]
        simp only [hc_def]
        field_simp
        ring
      ·
        rw [h1]
        simp only [hE_def, elimMatrix_val]
        simp only [mul_transvection_apply_of_ne (hb := hne)]
        have hjm : j.val ≤ m := by
          simp only [hj₀_def, ne_eq, Fin.ext_iff] at hne; omega
        exact hUp_cleared j hj1 hjm
    ·
      intro i hi
      have h1 : (g * U_new).val i 0 = (g'.val * E.val) i 0 :=
        congrFun (congrFun hval_eq i) 0
      rw [h1]
      simp only [hE_def, elimMatrix_val]
      simp only [mul_transvection_apply_of_ne (hb := h0j₀)]
      exact hUp_col0 i hi
    ·
      have h1 : (g * U_new).val 0 0 = (g'.val * E.val) 0 0 :=
        congrFun (congrFun hval_eq 0) 0
      rw [h1]
      simp only [hE_def, elimMatrix_val]
      simp only [mul_transvection_apply_of_ne (hb := h0j₀)]
      exact hUp_00

/-- Extract the lower-right $n \times n$ block of a cleared $(n+1) \times (n+1)$ Iwahori matrix:
given that $g$ has zero first column and first row off the diagonal, the lower-right block is an
Iwahori element of $\mathrm{GL}_n(k)$. -/
theorem extract_lower_right_block (hn : n ≥ 1)
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1))
    (hcol : ∀ (i : Fin (n + 1)), i.val > 0 → g.val i 0 = 0)
    (hrow : ∀ (j : Fin (n + 1)), j.val > 0 → g.val 0 j = 0) :
    ∃ (D : GL (Fin n) C.k),
      D ∈ IwahoriGLn C n ∧

      (∀ (i j : Fin n), D.val i j =
        g.val ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩) := by

  let D_matrix : Matrix (Fin n) (Fin n) C.k := fun i j => g.val i.succ j.succ
  let D_inv : Matrix (Fin n) (Fin n) C.k := fun i j => g.inv i.succ j.succ

  have h_val_inv : D_matrix * D_inv = 1 := by
    ext i j
    simp only [D_matrix, D_inv, Matrix.mul_apply, Matrix.one_apply]
    have h_sum := congr_fun₂ g.val_inv i.succ j.succ
    simp only [Matrix.mul_apply, Matrix.one_apply] at h_sum
    rw [Fin.sum_univ_succ] at h_sum
    simp only [hcol i.succ (Fin.succ_pos i), zero_mul, zero_add, Fin.succ_inj] at h_sum
    exact h_sum

  have h_inv_val : D_inv * D_matrix = 1 := by
    ext i j
    simp only [D_matrix, D_inv, Matrix.mul_apply, Matrix.one_apply]
    have h_sum := congr_fun₂ g.inv_val i.succ j.succ
    simp only [Matrix.mul_apply, Matrix.one_apply] at h_sum
    rw [Fin.sum_univ_succ] at h_sum
    simp only [hrow j.succ (Fin.succ_pos j), mul_zero, zero_add, Fin.succ_inj] at h_sum
    exact h_sum

  let D : GL (Fin n) C.k := ⟨D_matrix, D_inv, h_val_inv, h_inv_val⟩
  refine ⟨D, ?_, fun i j => rfl⟩

  have hg_diag := hg.1
  have hg_above := hg.2.1
  have hg_below := hg.2.2
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i
    exact hg_diag i.succ
  ·
    intro i j hij
    exact hg_above i.succ j.succ (by simp only [Fin.val_succ]; omega)
  ·
    intro i j hij
    exact hg_below i.succ j.succ (by simp only [Fin.val_succ]; omega)

/-- Lift an $n \times n$ Iwahori decomposition of the lower-right block $D$ of a cleared
$(n + 1) \times (n + 1)$ Iwahori matrix $g$ back to an Iwahori decomposition of $g$ itself via the
block embedding. -/
theorem block_diag_decomp (hn : n ≥ 1)
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1))
    (hcol : ∀ (i : Fin (n + 1)), i.val > 0 → g.val i 0 = 0)
    (hrow : ∀ (j : Fin (n + 1)), j.val > 0 → g.val 0 j = 0)
    (D : GL (Fin n) C.k) (hD : D ∈ IwahoriGLn C n)
    (hD_entries : ∀ (i j : Fin n), D.val i j =
        g.val ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    (u'_n m_n u_n : GL (Fin n) C.k)
    (hu'_n : u'_n ∈ LowerUnipGLn C n ∩ IwahoriGLn C n)
    (hm_n : m_n ∈ DiagGLn C n ∩ IwahoriGLn C n)
    (hu_n : u_n ∈ UpperUnipGLn C n ∩ IwahoriGLn C n)
    (hD_eq : D = u'_n * m_n * u_n) :
    ∃ (u'_big m_big u_big : GL (Fin (n + 1)) C.k),
      u'_big ∈ LowerUnipGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      m_big ∈ DiagGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      u_big ∈ UpperUnipGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      g = u'_big * m_big * u_big := by

  have hg00_unit_o : C.isUnitInO (g.val 0 0) := hg.1 0
  have hg00_ne : g.val 0 0 ≠ 0 := DVRClosureGL2.isUnitInO_ne_zero hg00_unit_o
  let g₀₀ : C.kˣ := Units.mk0 (g.val 0 0) hg00_ne

  let u'_big := blockEmbedGL C u'_n
  let m_big := diagBlockEmbedGL C g₀₀ m_n
  let u_big := blockEmbedGL C u_n
  refine ⟨u'_big, m_big, u_big, ?_, ?_, ?_, ?_⟩
  ·
    exact ⟨C.block_embed_preserves_lower_unip u'_n hu'_n.1,
           C.block_embed_preserves_iwahori u'_n hu'_n.2⟩
  ·
    exact ⟨C.diagBlockEmbed_preserves_diag g₀₀ m_n hm_n.1,
           C.diagBlockEmbed_preserves_iwahori g₀₀ m_n
             (show C.isUnitInO g₀₀.val from hg00_unit_o) hm_n.2⟩
  ·
    exact ⟨C.block_embed_preserves_upper_unip u_n hu_n.1,
           C.block_embed_preserves_iwahori u_n hu_n.2⟩
  ·

    have hmul : u'_big * m_big * u_big = diagBlockEmbedGL C g₀₀ (u'_n * m_n * u_n) :=
      C.blockEmbed_diagBlockEmbed_mul g₀₀ u'_n m_n u_n

    rw [hmul, ← hD_eq]

    ext1
    ext i j
    rcases fin_succ_cases i with rfl | ⟨k, rfl⟩
    · rcases fin_succ_cases j with rfl | ⟨l, rfl⟩
      ·
        simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_zero]
        rfl
      ·
        simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_succ]
        exact hrow ⟨l.val + 1, Nat.add_lt_add_right l.isLt 1⟩ (Nat.succ_pos l.val)
    · rcases fin_succ_cases j with rfl | ⟨l, rfl⟩
      ·
        simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_zero]
        exact hcol ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩ (Nat.succ_pos k.val)
      ·
        simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact (hD_entries k l).symm

/-- Inductive step of the Iwahori decomposition: assuming existence of the decomposition for $n$,
derive existence for $n + 1$ by clearing the first row and column and applying the induction
hypothesis to the lower-right block. -/
theorem iwahori_inductive_step (hn : n ≥ 1)
    (g : GL (Fin (n + 1)) C.k) (hg : g ∈ IwahoriGLn C (n + 1))
    (ih : ∀ b ∈ IwahoriGLn C n,
      ∃ (triple : GL (Fin n) C.k × GL (Fin n) C.k × GL (Fin n) C.k),
        let (u', m, u) := triple
        u' ∈ LowerUnipGLn C n ∩ IwahoriGLn C n ∧
        m ∈ DiagGLn C n ∩ IwahoriGLn C n ∧
        u ∈ UpperUnipGLn C n ∩ IwahoriGLn C n ∧
        b = u' * m * u) :
    ∃ (triple : GL (Fin (n + 1)) C.k × GL (Fin (n + 1)) C.k ×
        GL (Fin (n + 1)) C.k),
      let (u', m, u) := triple
      u' ∈ LowerUnipGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      m ∈ DiagGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      u ∈ UpperUnipGLn C (n + 1) ∩ IwahoriGLn C (n + 1) ∧
      g = u' * m * u := by

  obtain ⟨L, hL_lower, hL_iwahori, hL_zeros, hL_diag_eq⟩ :=
    C.clear_first_column hn g hg


  have hLg_iwahori : L * g ∈ IwahoriGLn C (n + 1) :=
    C.IwahoriGLn_mul_mem L g hL_iwahori hg
  obtain ⟨U, hU_upper, hU_iwahori, hU_row_zeros, hU_col_zeros, hU_diag_eq⟩ :=
    C.clear_first_row hn (L * g) hLg_iwahori hL_zeros


  have hLgU_iwahori : L * g * U ∈ IwahoriGLn C (n + 1) :=
    C.IwahoriGLn_mul_mem (L * g) U hLg_iwahori hU_iwahori
  obtain ⟨D, hD_iwahori, hD_entries⟩ :=
    C.extract_lower_right_block hn (L * g * U) hLgU_iwahori hU_col_zeros hU_row_zeros

  obtain ⟨⟨u'_n, m_n, u_n⟩, hu'_n, hm_n, hu_n, hD_eq⟩ := ih D hD_iwahori

  obtain ⟨u'_mid, m_mid, u_mid, hu'_mid, hm_mid, hu_mid, hLgU_decomp⟩ :=
    C.block_diag_decomp hn (L * g * U) hLgU_iwahori hU_col_zeros hU_row_zeros
      D hD_iwahori hD_entries u'_n m_n u_n hu'_n hm_n hu_n hD_eq


  have hL_inv := C.lower_unip_iwahori_inv_mem L hL_lower hL_iwahori
  have hU_inv := C.upper_unip_iwahori_inv_mem U hU_upper hU_iwahori
  have h_lower_factor := C.lower_unip_iwahori_mul_mem L⁻¹ u'_mid
    hL_inv.1 hL_inv.2 hu'_mid.1 hu'_mid.2
  have h_upper_factor := C.upper_unip_iwahori_mul_mem u_mid U⁻¹
    hu_mid.1 hu_mid.2 hU_inv.1 hU_inv.2

  exact ⟨(L⁻¹ * u'_mid, m_mid, u_mid * U⁻¹),
    ⟨h_lower_factor.1, h_lower_factor.2⟩,
    hm_mid,
    ⟨h_upper_factor.1, h_upper_factor.2⟩,
    by rw [show g = L⁻¹ * (L * g * U) * U⁻¹ from by group, hLgU_decomp]; group⟩

end Clearing

end DVRContext
