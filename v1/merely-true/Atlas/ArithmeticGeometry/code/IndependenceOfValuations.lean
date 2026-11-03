/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset

variable {F : Type*} [Field F]

lemma triangle_equality (v : AddValuation F (WithTop ℤ)) {x y : F}
    (h : v x ≠ v y) : v (x + y) = min (v x) (v y) :=
  AddValuation.map_add_of_distinct_val v h

lemma addval_ne_top (v : AddValuation F (WithTop ℤ)) {x : F} (hx : x ≠ 0) :
    v x ≠ ⊤ := by
  rwa [ne_eq, AddValuation.top_iff]

lemma ne_zero_of_val_coe {v : AddValuation F (WithTop ℤ)} {x : F} {a : ℤ}
    (h : v x = (a : WithTop ℤ)) : x ≠ 0 := by
  intro hx; subst hx; simp [AddValuation.map_zero] at h

lemma addval_mul_coe (v : AddValuation F (WithTop ℤ)) {x y : F} {a b : ℤ}
    (ha : v x = (a : WithTop ℤ)) (hb : v y = (b : WithTop ℤ)) :
    v (x * y) = ((a + b : ℤ) : WithTop ℤ) := by
  rw [v.map_mul, ha, hb, ← WithTop.coe_add]

lemma addval_inv_coe (v : AddValuation F (WithTop ℤ)) {x : F} {a : ℤ}
    (h : v x = (a : WithTop ℤ)) :
    v x⁻¹ = ((-a : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_inv, h]; norm_cast

lemma addval_npow_coe (v : AddValuation F (WithTop ℤ)) (n : ℕ) {x : F} {a : ℤ}
    (h : v x = (a : WithTop ℤ)) :
    v (x ^ n) = ((n : ℤ) * a : ℤ) := by
  induction n with
  | zero => simp [v.map_one]
  | succ n ih =>
    rw [pow_succ, v.map_mul, ih, h, ← WithTop.coe_add]
    congr 1; push_cast; ring

lemma addval_zpow_coe (v : AddValuation F (WithTop ℤ)) {x : F} {a : ℤ}
    (h : v x = (a : WithTop ℤ)) (n : ℤ) :
    v (x ^ n) = ((n * a : ℤ) : WithTop ℤ) := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [zpow_natCast]
    rw [addval_npow_coe v n h]
  · push_neg at hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -↑m := ⟨(-n).toNat, by omega⟩
    rw [zpow_neg, zpow_natCast, addval_inv_coe v (addval_npow_coe v m h)]
    norm_cast; ring


lemma addval_prod {n : ℕ} (v : AddValuation F (WithTop ℤ))
    (f : Fin n → F) : v (∏ j, f j) = ∑ j, v (f j) := by
  induction n with
  | zero => simp [v.map_one]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, v.map_mul, Fin.sum_univ_castSucc, ih]

lemma exists_nat_large_avoiding (a : ℤ) (ha : a < 0) (c : ℤ) (bad : Finset ℕ) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) * a < c ∧ N ∉ bad := by
  set M := bad.sup id + 1 with hM_def
  set K := max M (Int.toNat (c / a + 1) + 1) with hK_def
  refine ⟨K, ?_, ?_, ?_⟩
  · omega
  · have hK_large : (K : ℤ) ≥ c / a + 1 := by
      have : K ≥ Int.toNat (c / a + 1) + 1 := le_max_right M _
      have h1 : (Int.toNat (c / a + 1) : ℤ) ≥ c / a + 1 - 1 := by omega
      omega
    have h1 : (K : ℤ) * a ≤ (c / a + 1) * a :=
      mul_le_mul_of_nonpos_right hK_large (le_of_lt ha)
    have h2 : (c / a + 1) * a ≤ c / a * a + a := by ring_nf; omega
    have ha_ne : a ≠ 0 := ne_of_lt ha
    have h3 : c / a * a ≤ c := Int.ediv_mul_le c ha_ne
    linarith
  · intro hK_in
    have := Finset.le_sup hK_in (f := id)
    simp at this
    omega

lemma build_neg_element_from_seps (m : ℕ)
    (vlast : AddValuation F (WithTop ℤ))
    (vi : Fin m → AddValuation F (WithTop ℤ))
    (sep : Fin m → F)
    (hsep_ne : ∀ i, sep i ≠ 0)
    (hsep_last : ∀ i, (0 : WithTop ℤ) ≤ vlast (sep i))
    (hsep_neg : ∀ i, vi i (sep i) < 0) :
    ∃ s : F, s ≠ 0 ∧ (0 : WithTop ℤ) ≤ vlast s ∧ ∀ i, vi i s < 0 := by
  induction m with
  | zero => exact ⟨1, one_ne_zero, by simp [AddValuation.map_one], fun i => Fin.elim0 i⟩
  | succ n ih =>


    by_cases hn : n = 0
    ·
      subst hn
      exact ⟨sep 0, hsep_ne 0, hsep_last 0, fun i => by
        have : i = 0 := Fin.eq_zero i
        rw [this]; exact hsep_neg 0⟩
    ·
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have ih_result := ih (fun i => vi (Fin.castSucc i)) (fun i => sep (Fin.castSucc i))
        (fun i => hsep_ne _) (fun i => hsep_last _) (fun i => hsep_neg _)
      obtain ⟨s', hs'_ne, hs'_last, hs'_neg⟩ := ih_result


      by_cases hcase : vi (Fin.last n) s' < (0 : WithTop ℤ)
      · exact ⟨s', hs'_ne, hs'_last, fun i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · exact hcase
          · exact hs'_neg _⟩
      · push_neg at hcase


        set sep_n := sep (Fin.last n)
        have hsep_n_ne : sep_n ≠ 0 := hsep_ne _
        have hsep_n_last : (0 : WithTop ℤ) ≤ vlast sep_n := hsep_last _
        have hsep_n_neg : vi (Fin.last n) sep_n < 0 := hsep_neg _

        have hs'_ne_top_n : vi (Fin.last n) s' ≠ ⊤ := addval_ne_top _ hs'_ne
        set α := (vi (Fin.last n) s').untop hs'_ne_top_n
        have hα_spec : vi (Fin.last n) s' = (α : WithTop ℤ) := (WithTop.coe_untop _ _).symm
        have hα_nn : 0 ≤ α := by
          rw [hα_spec, ← WithTop.coe_zero, WithTop.coe_le_coe] at hcase; exact hcase
        have hsn_ne_top : vi (Fin.last n) sep_n ≠ ⊤ := addval_ne_top _ hsep_n_ne
        set β := (vi (Fin.last n) sep_n).untop hsn_ne_top
        have hβ_spec : vi (Fin.last n) sep_n = (β : WithTop ℤ) := (WithTop.coe_untop _ _).symm
        have hβ_neg : β < 0 := by
          rw [hβ_spec, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hsep_n_neg; exact hsep_n_neg

        have hs'_vals : ∀ i : Fin n, ∃ γi : ℤ, vi (Fin.castSucc i) s' = (γi : WithTop ℤ) ∧ γi < 0 := by
          intro i
          have hne := addval_ne_top (vi (Fin.castSucc i)) hs'_ne
          refine ⟨(vi (Fin.castSucc i) s').untop hne, (WithTop.coe_untop _ _).symm, ?_⟩
          have h := hs'_neg i
          rw [(WithTop.coe_untop _ hne).symm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h
          exact h
        choose γ hγ_spec hγ_neg using hs'_vals

        have hsn_vals : ∀ i : Fin n, ∃ δi : ℤ, vi (Fin.castSucc i) sep_n = (δi : WithTop ℤ) := by
          intro i
          exact ⟨_, (WithTop.coe_untop _ (addval_ne_top (vi (Fin.castSucc i)) hsep_n_ne)).symm⟩
        choose δ hδ_spec using hsn_vals

        set bad_eq : Finset ℕ := Finset.univ.biUnion (fun i : Fin n =>
          if hdi : δ i ≠ 0 ∧ (δ i ∣ γ i) then {(γ i / δ i).toNat} else ∅) with hbad_eq_def


        set bound := min (α + 1) ((Finset.univ.inf' ⟨⟨0, hn_pos⟩, mem_univ _⟩ (fun i => γ i)) - 1)
        obtain ⟨N, hN_pos, hN_bound, hN_good⟩ := exists_nat_large_avoiding β hβ_neg bound bad_eq
        have hNβ : (N : ℤ) * β < α + 1 := lt_of_lt_of_le hN_bound (min_le_left _ _)
        have hNβ_lt_γ : ∀ i : Fin n, (N : ℤ) * β < γ i := by
          intro i
          have h1 : bound ≤ (Finset.univ.inf' ⟨⟨0, hn_pos⟩, mem_univ _⟩ (fun i => γ i)) - 1 :=
            min_le_right _ _
          have h2 := Finset.inf'_le (fun i => γ i) (mem_univ i)
          linarith

        have hN_neq : ∀ i : Fin n, γ i ≠ (N : ℤ) * δ i := by
          intro i habs
          by_cases hdi_zero : δ i = 0
          · rw [hdi_zero, mul_zero] at habs; linarith [hγ_neg i]
          · have hdi_dvd : δ i ∣ γ i := ⟨N, by linarith⟩
            have hN_in : N ∈ bad_eq := by
              rw [hbad_eq_def]
              apply Finset.mem_biUnion.mpr
              refine ⟨i, mem_univ _, ?_⟩
              have hcond : δ i ≠ 0 ∧ (δ i ∣ γ i) := ⟨hdi_zero, hdi_dvd⟩
              simp only [dif_pos hcond, Finset.mem_singleton]
              rw [habs, Int.mul_ediv_cancel (↑N) hdi_zero]
              omega
            exact hN_good hN_in


        have hsep_nN_val : vi (Fin.last n) (sep_n ^ N) = ((N : ℤ) * β : ℤ) :=
          addval_npow_coe _ N hβ_spec
        have hsep_nN_ne : sep_n ^ N ≠ 0 := pow_ne_zero N hsep_n_ne

        set s := s' + sep_n ^ N
        refine ⟨s, ?_, ?_, ?_⟩
        ·
          intro hs0
          have htop : vi (Fin.last n) s = ⊤ := by rw [hs0, AddValuation.map_zero]
          have hne_vals : vi (Fin.last n) s' ≠ vi (Fin.last n) (sep_n ^ N) := by
            rw [hα_spec, hsep_nN_val, ne_eq, WithTop.coe_eq_coe]; nlinarith
          rw [show s = s' + sep_n ^ N from rfl, triangle_equality _ hne_vals,
              hα_spec, hsep_nN_val] at htop
          simp at htop
        ·
          have hvlast_sN : (0 : WithTop ℤ) ≤ vlast (sep_n ^ N) := by
            have : vlast (sep_n ^ N) = ((N : ℤ) * ((vlast sep_n).untop (addval_ne_top vlast hsep_n_ne)) : ℤ) :=
              addval_npow_coe vlast N (WithTop.coe_untop _ _).symm
            rw [this, ← WithTop.coe_zero, WithTop.coe_le_coe]
            apply mul_nonneg (by omega : (0 : ℤ) ≤ N)
            have h0 : (0 : WithTop ℤ) ≤ ↑((vlast sep_n).untop (addval_ne_top vlast hsep_n_ne)) := by
              rw [WithTop.coe_untop]; exact hsep_n_last
            exact_mod_cast h0
          calc (0 : WithTop ℤ) ≤ min (vlast s') (vlast (sep_n ^ N)) :=
                le_min hs'_last hvlast_sN
            _ ≤ vlast (s' + sep_n ^ N) := (AddValuation.map_add vlast s' (sep_n ^ N))
        ·
          intro j
          refine Fin.lastCases ?_ (fun i => ?_) j

          · have hne_vals : vi (Fin.last n) s' ≠ vi (Fin.last n) (sep_n ^ N) := by
              rw [hα_spec, hsep_nN_val, ne_eq, WithTop.coe_eq_coe]; nlinarith
            rw [show s = s' + sep_n ^ N from rfl, triangle_equality _ hne_vals,
                hα_spec, hsep_nN_val]
            rw [min_comm, min_eq_left]
            · change ((↑N * β : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
              rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
              nlinarith [hβ_neg, hN_pos]
            · rw [WithTop.coe_le_coe]; linarith [hNβ]

          · have hsepN_i : vi (Fin.castSucc i) (sep_n ^ N) = ((N : ℤ) * δ i : ℤ) :=
              addval_npow_coe _ N (hδ_spec i)

            have hvals_ne : vi (Fin.castSucc i) s' ≠ vi (Fin.castSucc i) (sep_n ^ N) := by
              rw [hγ_spec i, hsepN_i, ne_eq, WithTop.coe_eq_coe]
              exact hN_neq i
            rw [show s = s' + sep_n ^ N from rfl,
                triangle_equality _ hvals_ne, hγ_spec i, hsepN_i]
            exact_mod_cast min_lt_of_left_lt (hγ_neg i)

lemma val_prod_zpow_kronecker {m : ℕ} (v : AddValuation F (WithTop ℤ))
    (t' : Fin m → F) (c : Fin m → ℤ) (i : Fin m)
    (ht'_ne : ∀ j, t' j ≠ 0)
    (ht' : ∀ j, v (t' j) = ↑(if i = j then (1 : ℤ) else 0)) :
    v (∏ j : Fin m, (t' j) ^ (-(c j))) = ((-c i : ℤ) : WithTop ℤ) := by
  rw [addval_prod]
  have hj : ∀ j, v ((t' j) ^ (-(c j))) = ((-(c j) * if i = j then 1 else 0 : ℤ) : WithTop ℤ) :=
    fun j => addval_zpow_coe v (ht' j) (-(c j))
  simp_rw [hj, mul_ite, mul_one, mul_zero]
  rw [show (∑ x : Fin m, (↑(if i = x then -c x else (0 : ℤ)) : WithTop ℤ)) =
      ↑(∑ x : Fin m, (if i = x then -c x else 0)) from by rw [WithTop.coe_sum]]
  congr 1
  simp [Finset.mem_univ]

lemma construct_tn (m : ℕ)
    (v : Fin (m + 1) → AddValuation F (WithTop ℤ))
    (hv_surj : ∀ i, ∃ u, v i u = (1 : ℤ))
    (hv_incomp : ∀ i j, i ≠ j → ¬(∀ x, (0 : WithTop ℤ) ≤ v i x → (0 : WithTop ℤ) ≤ v j x))
    (t' : Fin m → F)
    (ht' : ∀ i j : Fin m, v (Fin.castSucc i) (t' j) = ↑(if i = j then (1 : ℤ) else 0)) :
    ∃ tn : F,
      v (Fin.last m) tn = (1 : ℤ) ∧
      ∀ i : Fin m, v (Fin.castSucc i) tn = (0 : ℤ) := by
  let vlast := v (Fin.last m)
  obtain ⟨u, hu⟩ := hv_surj (Fin.last m)
  have hu_ne : u ≠ 0 := ne_zero_of_val_coe hu
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨u, hu, fun i => Fin.elim0 i⟩
  have hsep : ∀ i : Fin m, ∃ si : F, si ≠ 0 ∧
      (0 : WithTop ℤ) ≤ vlast si ∧ v (Fin.castSucc i) si < 0 := by
    intro i
    have h := hv_incomp (Fin.last m) (Fin.castSucc i)
      ((Fin.castSucc_lt_last i).ne')
    push_neg at h
    obtain ⟨x, hx_last, hx_i⟩ := h
    exact ⟨x, by intro hx0; rw [hx0, AddValuation.map_zero] at hx_i; simp at hx_i,
      hx_last, hx_i⟩
  choose sep hsep_ne hsep_last hsep_neg using hsep
  obtain ⟨s, hs_ne, hs_last, hs_neg⟩ := build_neg_element_from_seps m vlast
    (fun i => v (Fin.castSucc i)) sep hsep_ne hsep_last hsep_neg
  have hs_ne_top : vlast s ≠ ⊤ := addval_ne_top vlast hs_ne
  set cs := (vlast s).untop hs_ne_top with hcs_def
  have hcs_spec : vlast s = (cs : WithTop ℤ) := (WithTop.coe_untop _ _).symm
  have hcs_nonneg : 0 ≤ cs := by
    rw [hcs_spec, ← WithTop.coe_zero, WithTop.coe_le_coe] at hs_last; exact hs_last
  have hsi_int : ∀ i : Fin m, ∃ ai : ℤ, v (Fin.castSucc i) s = ↑ai ∧ ai ≤ -1 := by
    intro i
    have hne := addval_ne_top (v (Fin.castSucc i)) hs_ne
    refine ⟨(v (Fin.castSucc i) s).untop hne, (WithTop.coe_untop _ _).symm, ?_⟩
    have h := hs_neg i
    rw [(WithTop.coe_untop _ hne).symm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h; omega
  have hui_int : ∀ i : Fin m, ∃ bi : ℤ, v (Fin.castSucc i) u = ↑bi := by
    intro i; exact ⟨_, (WithTop.coe_untop _ (addval_ne_top _ hu_ne)).symm⟩
  choose ai hai_spec hai_le using hsi_int
  choose bi hbi_spec using hui_int

  have ⟨t, ht_ne, ht_last, ht_neg⟩ : ∃ t : F, t ≠ 0 ∧
      vlast t = (1 : ℤ) ∧ ∀ i : Fin m, v (Fin.castSucc i) t < 0 := by
    rcases eq_or_lt_of_le hcs_nonneg with hcs0 | hcs_pos
    ·
      have hcs_eq : cs = 0 := by omega
      set N := (Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m => (bi j).toNat)) + 1
      have hN_gt_bi : ∀ i : Fin m, bi i < (N : ℤ) := by
        intro i
        have h1 : bi i ≤ ((bi i).toNat : ℤ) := by omega
        have h2 := Finset.le_sup' (fun j : Fin m => (bi j).toNat) (Finset.mem_univ i)
        omega
      set t := u * s ^ N
      refine ⟨t, mul_ne_zero hu_ne (pow_ne_zero N hs_ne), ?_, fun i => ?_⟩
      · rw [addval_mul_coe vlast hu (addval_npow_coe vlast N hcs_spec)]
        simp [hcs_eq]
      · rw [addval_mul_coe (v (Fin.castSucc i)) (hbi_spec i)
            (addval_npow_coe (v (Fin.castSucc i)) N (hai_spec i))]
        show ((bi i + (N : ℤ) * ai i : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
        rw [← WithTop.coe_zero, WithTop.coe_lt_coe]
        have : (N : ℤ) * ai i ≤ (N : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (hai_le i) (by omega)
        linarith [hN_gt_bi i]
    ·
      let bad : Finset ℕ := ({0, 1} : Finset ℕ) ∪ Finset.univ.biUnion (fun i : Fin m =>
        if h : ai i ≠ 0 ∧ (ai i) ∣ (bi i) ∧ 0 < (bi i) / (ai i)
        then {((bi i) / (ai i)).toNat} else ∅)
      set bound := (Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun i : Fin m => (-bi i).toNat)) with hbound_def
      obtain ⟨N, hN_pos, hN_bound, hN_good⟩ :=
        exists_nat_large_avoiding (-1) (by omega) (-(bound : ℤ) - 1) bad
      have hN_ge2 : 2 ≤ N := by
        by_contra h
        push_neg at h
        omega
      have hN_gt_neg_bi : ∀ i : Fin m, -(bi i) < (N : ℤ) := by
        intro i
        have h1 : -(bi i) ≤ (((-bi i).toNat : ℕ) : ℤ) := by omega
        have h2 := Finset.le_sup' (fun j : Fin m => (-bi j).toNat) (Finset.mem_univ i)
        have : (bound : ℤ) ≥ ((-bi i).toNat : ℤ) := by exact_mod_cast h2
        omega
      set t := s ^ N + u
      have hvlast_sN : vlast (s ^ N) = ((N : ℤ) * cs : ℤ) := addval_npow_coe vlast N hcs_spec
      have hNcs_gt1 : 1 < (N : ℤ) * cs := by nlinarith
      have hvlast_ne : vlast (s ^ N) ≠ vlast u := by
        rw [hvlast_sN, hu]; simp only [ne_eq, WithTop.coe_eq_coe]; omega
      have hvlast_t : vlast t = (1 : ℤ) := by
        rw [show t = s ^ N + u from rfl, triangle_equality vlast hvlast_ne,
            hvlast_sN, hu, min_eq_right]; rw [WithTop.coe_le_coe]; omega
      refine ⟨t, ne_zero_of_val_coe hvlast_t, hvlast_t, fun i => ?_⟩
      have hvi_sN : v (Fin.castSucc i) (s ^ N) = ((N : ℤ) * ai i : ℤ) :=
        addval_npow_coe (v (Fin.castSucc i)) N (hai_spec i)
      have hN_ai_lt_bi : (N : ℤ) * ai i < bi i := by
        have : (N : ℤ) * ai i ≤ (N : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (hai_le i) (by omega)
        linarith [hN_gt_neg_bi i]
      have hvi_ne : v (Fin.castSucc i) (s ^ N) ≠ v (Fin.castSucc i) u := by
        rw [hvi_sN, hbi_spec i]; simp only [ne_eq, WithTop.coe_eq_coe]; omega
      rw [show t = s ^ N + u from rfl, triangle_equality (v (Fin.castSucc i)) hvi_ne,
          hvi_sN, hbi_spec i, min_eq_left]
      · show ((↑N * ai i : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
        rw [← WithTop.coe_zero, WithTop.coe_lt_coe]; nlinarith [hai_le i]
      · rw [WithTop.coe_le_coe]; omega

  have ht_int : ∀ i : Fin m, ∃ ci : ℤ, v (Fin.castSucc i) t = ↑ci ∧ ci < 0 := by
    intro i; have hne := addval_ne_top (v (Fin.castSucc i)) ht_ne
    refine ⟨(v (Fin.castSucc i) t).untop hne, (WithTop.coe_untop _ _).symm, ?_⟩
    have h := ht_neg i
    rw [(WithTop.coe_untop _ hne).symm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h; exact h
  choose ci hci_spec hci_neg using ht_int
  have ht'_ne : ∀ j : Fin m, t' j ≠ 0 := by
    intro j hj
    have := ht' j j; simp at this
    rw [hj, AddValuation.map_zero] at this; simp at this
  set w := t * ∏ j : Fin m, (t' j) ^ (-(ci j))
  have hw_vi : ∀ i : Fin m, v (Fin.castSucc i) w = (0 : ℤ) := by
    intro i
    have hprod : v (Fin.castSucc i) (∏ j : Fin m, (t' j) ^ (-(ci j))) =
        ((-ci i : ℤ) : WithTop ℤ) :=
      val_prod_zpow_kronecker (v (Fin.castSucc i)) t' ci i ht'_ne (fun j => ht' i j)
    rw [show w = t * ∏ j : Fin m, (t' j) ^ (-(ci j)) from rfl,
        addval_mul_coe (v (Fin.castSucc i)) (hci_spec i) hprod]
    norm_cast; omega
  have hw_ne : w ≠ 0 := by
    intro hw0; have := hw_vi ⟨0, hm⟩
    rw [hw0, AddValuation.map_zero] at this; simp at this
  have hw_ne_top : vlast w ≠ ⊤ := addval_ne_top vlast hw_ne
  set d := (vlast w).untop hw_ne_top
  have hd_spec : vlast w = (d : WithTop ℤ) := (WithTop.coe_untop _ _).symm

  set w' := if d < 0 then w⁻¹ else w
  have hw'_vi : ∀ i : Fin m, v (Fin.castSucc i) w' = (0 : ℤ) := by
    intro i; simp only [w']; split_ifs with hd_neg
    · rw [addval_inv_coe (v (Fin.castSucc i)) (hw_vi i)]; simp
    · exact hw_vi i
  have hw'_ne : w' ≠ 0 := by
    simp only [w']; split_ifs with h
    · exact inv_ne_zero hw_ne
    · exact hw_ne
  set d' := if d < 0 then -d else d
  have hd'_ge : 0 ≤ d' := by simp only [d']; split_ifs with h <;> omega
  have hd'_spec : vlast w' = (d' : WithTop ℤ) := by
    simp only [w', d']; split_ifs with hd_neg
    · exact addval_inv_coe vlast hd_spec
    · exact hd_spec

  have ht_inv_last : vlast t⁻¹ = ((-1 : ℤ) : WithTop ℤ) := addval_inv_coe vlast ht_last
  have ht_inv_vi : ∀ i : Fin m, v (Fin.castSucc i) t⁻¹ = ((-ci i : ℤ) : WithTop ℤ) :=
    fun i => addval_inv_coe (v (Fin.castSucc i)) (hci_spec i)
  set z := w' + t⁻¹
  have hz_vi : ∀ i : Fin m, v (Fin.castSucc i) z = (0 : ℤ) := by
    intro i
    have hci := hci_neg i
    have hne : v (Fin.castSucc i) w' ≠ v (Fin.castSucc i) t⁻¹ := by
      rw [hw'_vi i, ht_inv_vi i]; simp only [ne_eq, WithTop.coe_eq_coe]; omega
    rw [show z = w' + t⁻¹ from rfl, triangle_equality (v (Fin.castSucc i)) hne,
        hw'_vi i, ht_inv_vi i, min_eq_left]; rw [WithTop.coe_le_coe]; omega
  have hz_last : vlast z = ((-1 : ℤ) : WithTop ℤ) := by
    have hne : vlast w' ≠ vlast t⁻¹ := by
      rw [hd'_spec, ht_inv_last]; simp only [ne_eq, WithTop.coe_eq_coe]; omega
    rw [show z = w' + t⁻¹ from rfl, triangle_equality vlast hne,
        hd'_spec, ht_inv_last, min_eq_right]; rw [WithTop.coe_le_coe]; omega
  have hz_ne : z ≠ 0 := ne_zero_of_val_coe hz_last
  exact ⟨z⁻¹, addval_inv_coe vlast hz_last, fun i => addval_inv_coe (v (Fin.castSucc i)) (hz_vi i)⟩

theorem independence_of_valuations (n : ℕ)
    (v : Fin n → AddValuation F (WithTop ℤ))
    (hv_surj : ∀ i, ∃ u, v i u = (1 : ℤ))
    (hv_incomp : ∀ i j, i ≠ j → ¬(∀ x, (0 : WithTop ℤ) ≤ v i x → (0 : WithTop ℤ) ≤ v j x)) :
    ∃ t : Fin n → F, ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0) := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ m ih =>

    have hv'_surj : ∀ i : Fin m, ∃ u, v (Fin.castSucc i) u = (1 : ℤ) :=
      fun i => hv_surj (Fin.castSucc i)
    have hv'_incomp : ∀ i j : Fin m, i ≠ j →
        ¬(∀ x, (0 : WithTop ℤ) ≤ v (Fin.castSucc i) x →
                (0 : WithTop ℤ) ≤ v (Fin.castSucc j) x) := by
      intro i j hij
      exact hv_incomp _ _ (by intro h; exact hij (Fin.castSucc_injective m h))
    obtain ⟨t', ht'⟩ := ih (fun i => v (Fin.castSucc i)) hv'_surj hv'_incomp

    obtain ⟨tn, htn_last, htn_zero⟩ := construct_tn m v hv_surj hv_incomp t' ht'


    have ht'_ne : ∀ j : Fin m, t' j ≠ 0 := by
      intro j hj
      have := ht' j j; simp at this
      rw [hj, AddValuation.map_zero] at this; simp at this
    have htn_ne : tn ≠ 0 := ne_zero_of_val_coe htn_last

    set vlast := v (Fin.last m)
    have ht'_vlast_int : ∀ j : Fin m, ∃ ej : ℤ, vlast (t' j) = (ej : WithTop ℤ) := by
      intro j; exact ⟨_, (WithTop.coe_untop _ (addval_ne_top vlast (ht'_ne j))).symm⟩
    choose ej hej_spec using ht'_vlast_int

    set t'' := fun j : Fin m => t' j * tn ^ (-(ej j))

    have ht''_castSucc : ∀ i j : Fin m,
        v (Fin.castSucc i) (t'' j) = ↑(if i = j then (1 : ℤ) else 0) := by
      intro i j
      simp only [t'']
      rw [addval_mul_coe (v (Fin.castSucc i)) (ht' i j)
          (addval_zpow_coe (v (Fin.castSucc i)) (htn_zero i) (-(ej j)))]
      simp
    have ht''_last : ∀ j : Fin m, vlast (t'' j) = (0 : ℤ) := by
      intro j
      simp only [t'']
      rw [addval_mul_coe vlast (hej_spec j) (addval_zpow_coe vlast htn_last (-(ej j)))]
      simp

    refine ⟨fun k => Fin.lastCases tn t'' k, fun i k => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) k

    · simp only [Fin.lastCases_last]
      refine Fin.lastCases ?_ (fun j => ?_) i
      ·
        simp only [ite_true]; exact htn_last
      · rw [if_neg (Fin.castSucc_lt_last j).ne, htn_zero j]

    · simp only [Fin.lastCases_castSucc]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [if_neg (Fin.castSucc_lt_last j).ne.symm, ht''_last j]
      · simp_rw [Fin.castSucc_inj]
        exact ht''_castSucc i' j
