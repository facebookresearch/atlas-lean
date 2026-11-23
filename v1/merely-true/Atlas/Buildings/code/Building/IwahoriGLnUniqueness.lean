/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnDefs

set_option maxHeartbeats 400000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section Helpers

variable {C}
variable {n : ℕ}

/-- Left multiplication by a diagonal matrix scales rows: $(d \cdot A)_{ij} = d_{ii} \cdot A_{ij}$. -/
lemma diag_mul_entry (d : GL (Fin n) C.k) (hd : d ∈ DiagGLn C n)
    (A : Matrix (Fin n) (Fin n) C.k) (i j : Fin n) :
    (d.val * A) i j = d.val i i * A i j := by
  simp only [mul_apply]
  rw [Finset.sum_eq_single i]
  · intro b _ hbi; simp [hd i b (Ne.symm hbi)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Right multiplication by a diagonal matrix scales columns:
$(A \cdot d)_{ij} = A_{ij} \cdot d_{jj}$. -/
lemma mul_diag_entry (A : Matrix (Fin n) (Fin n) C.k)
    (d : GL (Fin n) C.k) (hd : d ∈ DiagGLn C n) (i j : Fin n) :
    (A * d.val) i j = A i j * d.val j j := by
  simp only [mul_apply]
  rw [Finset.sum_eq_single j]
  · intro b _ hbj; simp [hd b j hbj]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- A diagonal matrix in $\mathrm{GL}_n$ has nonzero diagonal entries (else it would have a zero
row, contradicting invertibility). -/
lemma diag_entry_ne_zero (d : GL (Fin n) C.k) (hd : d ∈ DiagGLn C n) (i : Fin n) :
    d.val i i ≠ 0 := by
  have h1 : d.val * d⁻¹.val = 1 := by exact_mod_cast d.mul_inv
  have h3 : (d.val * d⁻¹.val) i i = 1 := by rw [h1]; simp
  rw [diag_mul_entry d hd] at h3
  intro heq; rw [heq, zero_mul] at h3; exact zero_ne_one h3

/-- The inverse of a diagonal matrix is diagonal. -/
lemma diag_inv_mem (d : GL (Fin n) C.k) (hd : d ∈ DiagGLn C n) :
    d⁻¹ ∈ DiagGLn C n := by
  intro i j hij
  have h1 : d.val * d⁻¹.val = 1 := by exact_mod_cast d.mul_inv
  have h2 : (d.val * d⁻¹.val) i j = 0 := by rw [h1]; simp [hij]
  rw [diag_mul_entry d hd] at h2
  exact (mul_eq_zero.mp h2).resolve_left (diag_entry_ne_zero d hd i)

/-- The diagonal entries of the inverse of a diagonal matrix are the inverses of the corresponding
entries: $(d^{-1})_{ii} = (d_{ii})^{-1}$. -/
lemma diag_inv_entry (d : GL (Fin n) C.k) (hd : d ∈ DiagGLn C n) (i : Fin n) :
    d⁻¹.val i i = (d.val i i)⁻¹ := by
  have h1 : d.val * d⁻¹.val = 1 := by exact_mod_cast d.mul_inv
  have h3 : (d.val * d⁻¹.val) i i = 1 := by rw [h1]; simp
  rw [diag_mul_entry d hd] at h3
  exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h3)

/-- Auxiliary induction on the descending distance $n - j$: for a lower unitriangular $L$, the
inverse $L^{-1}$ has zero strictly-above-diagonal entries. -/
lemma lower_unip_inv_above_aux (L : GL (Fin n) C.k) (hL : L ∈ LowerUnipGLn C n)
    (hIL : L⁻¹.val * L.val = 1) (d : ℕ) :
    ∀ j : Fin n, n - j.val ≤ d + 1 →
    ∀ i : Fin n, i.val < j.val → L⁻¹.val i j = 0 := by
  induction d with
  | zero =>
    intro j hj i hij
    have h_entry : (L⁻¹.val * L.val) i j = 0 := by
      rw [hIL]; simp [show i ≠ j from Fin.ne_of_val_ne (Nat.ne_of_lt hij)]
    rw [mul_apply, Finset.sum_eq_single j] at h_entry
    · simpa [hL.1 j] using h_entry
    · intro b _ hbj
      by_cases h : b.val < j.val
      · simp [hL.2 b j h]
      · exfalso; have := b.isLt; omega
    · intro h; exact absurd (Finset.mem_univ j) h
  | succ d ih =>
    intro j hj i hij
    have h_entry : (L⁻¹.val * L.val) i j = 0 := by
      rw [hIL]; simp [show i ≠ j from Fin.ne_of_val_ne (Nat.ne_of_lt hij)]
    rw [mul_apply, Finset.sum_eq_single j] at h_entry
    · simpa [hL.1 j] using h_entry
    · intro b _ hbj
      by_cases h : b.val < j.val
      · simp [hL.2 b j h]
      · simp [ih b (by omega) i (by omega)]
    · intro h; exact absurd (Finset.mem_univ j) h

/-- The inverse of a lower unitriangular matrix has zero strictly-above-diagonal entries. -/
lemma lower_unip_inv_above (L : GL (Fin n) C.k) (hL : L ∈ LowerUnipGLn C n)
    (i j : Fin n) (hij : i.val < j.val) : L⁻¹.val i j = 0 :=
  lower_unip_inv_above_aux L hL (by exact_mod_cast L.inv_mul) n j (by omega) i hij

/-- The diagonal entries of the inverse of a lower unitriangular matrix are $1$. -/
lemma lower_unip_inv_diag (L : GL (Fin n) C.k) (hL : L ∈ LowerUnipGLn C n)
    (i : Fin n) : L⁻¹.val i i = 1 := by
  have hIL : L⁻¹.val * L.val = 1 := by exact_mod_cast L.inv_mul
  have h_entry : (L⁻¹.val * L.val) i i = 1 := by rw [hIL]; simp
  rw [mul_apply, Finset.sum_eq_single i] at h_entry
  · simpa [hL.1 i] using h_entry
  · intro b _ hbi
    by_cases h : b.val < i.val
    · simp [hL.2 b i h]
    · simp [lower_unip_inv_above L hL i b (by omega)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The product of two lower unitriangular matrices has $1$ on the diagonal. -/
lemma lower_unip_mul_diag (L1 L2 : GL (Fin n) C.k)
    (hL1 : L1 ∈ LowerUnipGLn C n) (hL2 : L2 ∈ LowerUnipGLn C n)
    (i : Fin n) : (L1.val * L2.val) i i = 1 := by
  simp only [mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [hL1.1 i, hL2.1 i]
  · intro b _ hbi
    by_cases h : i.val < b.val
    · simp [hL1.2 i b h]
    · simp [hL2.2 b i (by omega)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The product of two lower unitriangular matrices has zero strictly-above-diagonal entries. -/
lemma lower_unip_mul_above (L1 L2 : GL (Fin n) C.k)
    (hL1 : L1 ∈ LowerUnipGLn C n) (hL2 : L2 ∈ LowerUnipGLn C n)
    (i j : Fin n) (hij : i.val < j.val) : (L1.val * L2.val) i j = 0 := by
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : i.val < k.val
  · simp [hL1.2 i k h]
  · simp [hL2.2 k j (by omega)]

/-- Auxiliary induction on the column index $j$: for an upper unitriangular $U$, the inverse
$U^{-1}$ has zero strictly-below-diagonal entries. -/
lemma upper_unip_inv_below_aux (U : GL (Fin n) C.k) (hU : U ∈ UpperUnipGLn C n)
    (hIU : U⁻¹.val * U.val = 1) (d : ℕ) :
    ∀ j : Fin n, j.val ≤ d →
    ∀ i : Fin n, i.val > j.val → U⁻¹.val i j = 0 := by
  induction d with
  | zero =>
    intro j hj i hij
    have h_entry : (U⁻¹.val * U.val) i j = 0 := by
      rw [hIU]; simp [show i ≠ j from Fin.ne_of_val_ne (by omega)]
    rw [mul_apply, Finset.sum_eq_single j] at h_entry
    · simpa [hU.1 j] using h_entry
    · intro b _ hbj
      by_cases h : b.val > j.val
      · simp [hU.2 b j h]
      · exfalso; omega
    · intro h; exact absurd (Finset.mem_univ j) h
  | succ d ih =>
    intro j hj i hij
    have h_entry : (U⁻¹.val * U.val) i j = 0 := by
      rw [hIU]; simp [show i ≠ j from Fin.ne_of_val_ne (by omega)]
    rw [mul_apply, Finset.sum_eq_single j] at h_entry
    · simpa [hU.1 j] using h_entry
    · intro b _ hbj
      by_cases h : b.val > j.val
      · simp [hU.2 b j h]
      · simp [ih b (by omega) i (by omega)]
    · intro h; exact absurd (Finset.mem_univ j) h

/-- The inverse of an upper unitriangular matrix has zero strictly-below-diagonal entries. -/
lemma upper_unip_inv_below (U : GL (Fin n) C.k) (hU : U ∈ UpperUnipGLn C n)
    (i j : Fin n) (hij : i.val > j.val) : U⁻¹.val i j = 0 :=
  upper_unip_inv_below_aux U hU (by exact_mod_cast U.inv_mul) n j (by omega) i hij

/-- The diagonal entries of the inverse of an upper unitriangular matrix are $1$. -/
lemma upper_unip_inv_diag (U : GL (Fin n) C.k) (hU : U ∈ UpperUnipGLn C n)
    (i : Fin n) : U⁻¹.val i i = 1 := by
  have hIU : U⁻¹.val * U.val = 1 := by exact_mod_cast U.inv_mul
  have h_entry : (U⁻¹.val * U.val) i i = 1 := by rw [hIU]; simp
  rw [mul_apply, Finset.sum_eq_single i] at h_entry
  · simpa [hU.1 i] using h_entry
  · intro b _ hbi
    by_cases h : b.val > i.val
    · simp [hU.2 b i h]
    · simp [upper_unip_inv_below U hU i b (by omega)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The product of two upper unitriangular matrices has $1$ on the diagonal. -/
lemma upper_unip_mul_diag (U1 U2 : GL (Fin n) C.k)
    (hU1 : U1 ∈ UpperUnipGLn C n) (hU2 : U2 ∈ UpperUnipGLn C n)
    (i : Fin n) : (U1.val * U2.val) i i = 1 := by
  simp only [mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [hU1.1 i, hU2.1 i]
  · intro b _ hbi
    by_cases h : i.val < b.val
    ·
      simp [hU2.2 b i h]
    ·
      simp [hU1.2 i b (by omega)]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The product of two upper unitriangular matrices has zero strictly-below-diagonal entries. -/
lemma upper_unip_mul_below (U1 U2 : GL (Fin n) C.k)
    (hU1 : U1 ∈ UpperUnipGLn C n) (hU2 : U2 ∈ UpperUnipGLn C n)
    (i j : Fin n) (hij : i.val > j.val) : (U1.val * U2.val) i j = 0 := by
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : k.val > j.val
  ·
    simp [hU2.2 k j h]
  ·
    simp [hU1.2 i k (by omega)]

end Helpers

section Uniqueness

variable {C}
variable {n : ℕ}

/-- Uniqueness of the Iwahori decomposition: if $u_\ell \cdot d \cdot u_u = v_\ell \cdot e \cdot v_u$
where both triples lie in the lower-unipotent / diagonal / upper-unipotent components of the Iwahori
subgroup, then $u_\ell = v_\ell$, $d = e$, and $u_u = v_u$. -/
theorem iwahori_decomp_unique
    (u_lo : GL (Fin n) C.k) (d_diag : GL (Fin n) C.k) (u_up : GL (Fin n) C.k)
    (v_lo : GL (Fin n) C.k) (e_diag : GL (Fin n) C.k) (v_up : GL (Fin n) C.k)
    (hu_lo : u_lo ∈ LowerUnipGLn C n ∩ IwahoriGLn C n)
    (hd : d_diag ∈ DiagGLn C n ∩ IwahoriGLn C n)
    (hu_up : u_up ∈ UpperUnipGLn C n ∩ IwahoriGLn C n)
    (hv_lo : v_lo ∈ LowerUnipGLn C n ∩ IwahoriGLn C n)
    (he : e_diag ∈ DiagGLn C n ∩ IwahoriGLn C n)
    (hv_up : v_up ∈ UpperUnipGLn C n ∩ IwahoriGLn C n)
    (heq : u_lo * d_diag * u_up = v_lo * e_diag * v_up) :
    u_lo = v_lo ∧ d_diag = e_diag ∧ u_up = v_up := by

  have hul : u_lo ∈ LowerUnipGLn C n := hu_lo.1
  have hdd : d_diag ∈ DiagGLn C n := hd.1
  have huu : u_up ∈ UpperUnipGLn C n := hu_up.1
  have hvl : v_lo ∈ LowerUnipGLn C n := hv_lo.1
  have hee : e_diag ∈ DiagGLn C n := he.1
  have hvu : v_up ∈ UpperUnipGLn C n := hv_up.1


  have hmul_left : v_lo⁻¹ * u_lo * d_diag * u_up = e_diag * v_up := by
    have := heq
    calc v_lo⁻¹ * u_lo * d_diag * u_up
        = v_lo⁻¹ * (u_lo * d_diag * u_up) := by group
      _ = v_lo⁻¹ * (v_lo * e_diag * v_up) := by rw [heq]
      _ = e_diag * v_up := by group
  have hmul_right : v_lo⁻¹ * u_lo * d_diag = e_diag * v_up * u_up⁻¹ := by
    calc v_lo⁻¹ * u_lo * d_diag
        = v_lo⁻¹ * u_lo * d_diag * u_up * u_up⁻¹ := by group
      _ = e_diag * v_up * u_up⁻¹ := by rw [hmul_left]; group
  have hLW : v_lo⁻¹ * u_lo = e_diag * (v_up * u_up⁻¹) * d_diag⁻¹ := by
    calc v_lo⁻¹ * u_lo
        = v_lo⁻¹ * u_lo * d_diag * d_diag⁻¹ := by group
      _ = e_diag * v_up * u_up⁻¹ * d_diag⁻¹ := by rw [hmul_right]; group
      _ = e_diag * (v_up * u_up⁻¹) * d_diag⁻¹ := by group


  have hentry : ∀ i j : Fin n,
      (v_lo⁻¹ * u_lo).val i j = (e_diag * (v_up * u_up⁻¹) * d_diag⁻¹).val i j := by
    intro i j
    have := congr_arg (·.val i j) hLW
    simpa using this


  have hLHS_val : (v_lo⁻¹ * u_lo).val = v_lo⁻¹.val * u_lo.val := Units.val_mul _ _


  have hd_eq_e : d_diag = e_diag := by

    ext1; ext i j

    by_cases hij : i = j
    · subst hij


      have hLHS_diag : (v_lo⁻¹ * u_lo).val i i = 1 := by
        rw [hLHS_val]
        exact lower_unip_mul_diag v_lo⁻¹ u_lo
          ⟨lower_unip_inv_diag v_lo hvl, lower_unip_inv_above v_lo hvl⟩ hul i


      have hW_diag : (v_up * u_up⁻¹).val i i = 1 := by
        show (v_up.val * u_up⁻¹.val) i i = 1
        exact upper_unip_mul_diag v_up u_up⁻¹ hvu
          ⟨upper_unip_inv_diag u_up huu, upper_unip_inv_below u_up huu⟩ i
      have hRHS_diag : (e_diag * (v_up * u_up⁻¹) * d_diag⁻¹).val i i =
          e_diag.val i i * (d_diag.val i i)⁻¹ := by
        show ((e_diag.val * (v_up * u_up⁻¹).val) * d_diag⁻¹.val) i i =
          e_diag.val i i * (d_diag.val i i)⁻¹
        rw [mul_diag_entry _ d_diag⁻¹ (diag_inv_mem d_diag hdd)]
        rw [diag_mul_entry e_diag hee]
        rw [hW_diag, mul_one, diag_inv_entry d_diag hdd]

      have h1 := hentry i i
      rw [hLHS_diag, hRHS_diag] at h1

      have hne : d_diag.val i i ≠ 0 := diag_entry_ne_zero d_diag hdd i
      field_simp at h1
      exact h1
    ·
      have hd_off := hdd i j hij
      have he_off := hee i j hij
      rw [he_off, hd_off]


  subst hd_eq_e


  have hLHS_is_one : v_lo⁻¹ * u_lo = 1 := by
    ext1; ext i j
    simp only [Units.val_one, one_apply]
    split_ifs with hij
    ·
      subst hij
      simp only [Units.val_mul]
      exact lower_unip_mul_diag v_lo⁻¹ u_lo
        ⟨lower_unip_inv_diag v_lo hvl, lower_unip_inv_above v_lo hvl⟩ hul i
    ·
      by_cases h : i.val < j.val
      ·
        simp only [Units.val_mul]
        exact lower_unip_mul_above v_lo⁻¹ u_lo
          ⟨lower_unip_inv_diag v_lo hvl, lower_unip_inv_above v_lo hvl⟩ hul i j h
      ·
        have hij_gt : i.val > j.val := by omega

        have hRHS_below : (d_diag * (v_up * u_up⁻¹) * d_diag⁻¹).val i j = 0 := by
          show ((d_diag.val * (v_up * u_up⁻¹).val) * d_diag⁻¹.val) i j = 0
          rw [mul_diag_entry _ d_diag⁻¹ (diag_inv_mem d_diag hdd)]
          rw [diag_mul_entry d_diag hdd]
          have hW_below : (v_up * u_up⁻¹).val i j = 0 := by
            show (v_up.val * u_up⁻¹.val) i j = 0
            exact upper_unip_mul_below v_up u_up⁻¹ hvu
              ⟨upper_unip_inv_diag u_up huu, upper_unip_inv_below u_up huu⟩ i j hij_gt
          rw [hW_below]; ring
        exact (hentry i j).trans hRHS_below

  have hu_lo_eq : u_lo = v_lo := by
    have := hLHS_is_one
    calc u_lo = v_lo * (v_lo⁻¹ * u_lo) := by group
      _ = v_lo * 1 := by rw [this]
      _ = v_lo := by group


  have hRHS_is_one : d_diag * (v_up * u_up⁻¹) * d_diag⁻¹ = 1 := by
    rw [← hLW, hLHS_is_one]
  have hW_is_one : v_up * u_up⁻¹ = 1 := by
    calc v_up * u_up⁻¹
        = d_diag⁻¹ * (d_diag * (v_up * u_up⁻¹) * d_diag⁻¹) * d_diag := by group
      _ = d_diag⁻¹ * 1 * d_diag := by rw [hRHS_is_one]
      _ = 1 := by group
  have hu_up_eq : u_up = v_up := (mul_inv_eq_one.mp hW_is_one).symm
  exact ⟨hu_lo_eq, rfl, hu_up_eq⟩

end Uniqueness

end DVRContext
