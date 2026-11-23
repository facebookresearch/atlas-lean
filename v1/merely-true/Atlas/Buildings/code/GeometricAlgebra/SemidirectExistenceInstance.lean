/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.SemidirectExistence

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Main inductive construction of the semidirect decomposition `p = d ∘ u` for a flag
stabilizer: starting from any automorphism `q` that preserves the flag `G`, peel off the
smallest level `W = G.spaces 0` and its opposite `W' = G'.spaces (G'.len - 1)`, decompose
the action on the block `W ⊕ W'`, recurse on the truncated flags `H, H'`, and reassemble
the decomposition. Proceeds by termination on `G.len`. -/
theorem semidirect_existence_compl [FiniteDimensional k V]
    (G G' : Flag k V)
    (hlen_eq : G.len = G'.len)
    (hcompl : ∀ (h : G.len = G'.len) (i : Fin G.len),
      G.spaces i ⊔ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊤ ∧
      G.spaces i ⊓ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊥)
    (hlen_pos : 0 < G.len)
    (hcov : G.spaces ⟨G.len - 1, by omega⟩ = ⊤)
    (q : V ≃ₗ[k] V)
    (hq : ∀ j : Fin G.len, (G.spaces j).map q.toLinearMap = G.spaces j) :
    ∃ (d u : V ≃ₗ[k] V),
      (∀ j : Fin G.len, (G.spaces j).map d.toLinearMap = G.spaces j) ∧
      (∀ j : Fin G'.len, (G'.spaces j).map d.toLinearMap = G'.spaces j) ∧
      (∀ j : Fin G.len, (G.spaces j).map u.toLinearMap = G.spaces j) ∧
      (∀ j : Fin G.len, ∀ v ∈ G.spaces j,
        u.toLinearMap v - v ∈
          if h : (j : ℕ) = 0 then (⊥ : Submodule k V)
          else G.spaces ⟨j.val - 1, by omega⟩) ∧
      q.toLinearMap = d.toLinearMap.comp u.toLinearMap := by

  by_cases hlen1 : G.len = 1
  · have hlen'1 : G'.len = 1 := by omega
    have hG0_top : G.spaces ⟨0, by omega⟩ = ⊤ := by
      convert hcov using 2; apply Fin.ext; simp; omega
    have hG'0_bot : G'.spaces ⟨0, by omega⟩ = ⊥ := by
      obtain ⟨_, hinf⟩ := hcompl hlen_eq ⟨0, by omega⟩
      have hfin : (⟨G'.len - 1 - 0, by omega⟩ : Fin G'.len) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp; omega
      rw [hG0_top, hfin] at hinf
      rwa [top_inf_eq] at hinf
    refine ⟨q, LinearEquiv.refl k V, hq, ?_, ?_, ?_, ?_⟩
    · intro j; have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hj, hG'0_bot]; exact Submodule.map_bot _
    · intro j; simp [LinearEquiv.refl_toLinearMap, Submodule.map_id]
    · intro j v _; have hj : (j : ℕ) = 0 := by omega
      simp [dif_pos hj]
    · simp [LinearMap.comp_id]

  · push_neg at hlen1
    have hlen2 : 2 ≤ G.len := by omega

    have hcompl_0 : IsCompl (G.spaces ⟨0, by omega⟩)
        (G'.spaces ⟨G'.len - 1 - 0, by omega⟩) := by
      obtain ⟨hsup, hinf⟩ := hcompl hlen_eq ⟨0, by omega⟩
      exact IsCompl.mk (disjoint_iff.mpr hinf) (codisjoint_iff.mpr hsup)
    set W := G.spaces ⟨0, by omega⟩
    set W' := G'.spaces ⟨G'.len - 1 - 0, by omega⟩
    have hqW : W.map q.toLinearMap = W := hq ⟨0, by omega⟩

    obtain ⟨d₀, u₀, hd₀W, hd₀W', hu₀W, hu₀_unip, hd₀_comp, hd₀_eq_q⟩ :=
      block_diagonal_decomp W W' hcompl_0 q hqW

    have hW_le : ∀ (i : Fin G.len), W ≤ G.spaces i := by
      intro ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0; exact le_refl _
      · exact le_of_lt (G.strictMono (Fin.mk_lt_mk.mpr (by omega)))

    have hu₀_id_on_W : ∀ w ∈ W, u₀ w = w := by
      intro w hw
      have h1 : d₀ (u₀ w) = q w := by
        have : q.toLinearMap w = (d₀.toLinearMap.comp u₀.toLinearMap) w := by rw [← hd₀_comp]
        simp at this; exact this.symm
      have h2 : d₀ w = q w := hd₀_eq_q w hw
      exact d₀.injective (h1.trans h2.symm)

    have hu₀_preserves : ∀ (i : Fin G.len),
        (G.spaces i).map u₀.toLinearMap = G.spaces i :=
      fun i => preserves_of_unipotent_le (G.spaces i) W u₀ hu₀_unip (hW_le i)

    have hd₀_preserves : ∀ (i : Fin G.len),
        (G.spaces i).map d₀.toLinearMap = G.spaces i := by
      intro i; have h1 := hq i
      rw [hd₀_comp, Submodule.map_comp, hu₀_preserves i] at h1; exact h1

    have hG_ge1 : 1 ≤ G.len := by omega
    have hG'_ge1 : 1 ≤ G'.len := by omega
    set H := G.truncateStart hG_ge1
    set H' := G'.truncate hG'_ge1
    have hH_len : H.len = G.len - 1 := rfl
    have hH'_len : H'.len = G'.len - 1 := rfl
    have hHH'_len : H.len = H'.len := by simp [hH_len, hH'_len, hlen_eq]
    have hH_cov : H.spaces ⟨H.len - 1, by omega⟩ = ⊤ := by
      simp only [H, Flag.truncateStart_spaces]
      convert hcov using 2; apply Fin.ext; simp; omega

    have hHH'_compl : ∀ (hle' : H.len = H'.len) (i : Fin H.len),
        H.spaces i ⊔ H'.spaces ⟨H'.len - 1 - i.val, by omega⟩ = ⊤ ∧
        H.spaces i ⊓ H'.spaces ⟨H'.len - 1 - i.val, by omega⟩ = ⊥ := by
      intro _ ⟨i, hi⟩
      simp only [H, Flag.truncateStart_spaces, H', Flag.truncate_spaces, hH_len] at hi ⊢
      have key := hcompl hlen_eq ⟨i + 1, by omega⟩
      simp only at key
      constructor
      · convert key.1 using 2; congr 1; apply Fin.ext; simp; omega
      · convert key.2 using 2; congr 1; apply Fin.ext; simp; omega

    have hd₀_H : ∀ j : Fin H.len,
        (H.spaces j).map d₀.toLinearMap = H.spaces j := by
      intro ⟨j, hj⟩
      simp only [H, Flag.truncateStart_spaces, hH_len] at hj ⊢
      exact hd₀_preserves ⟨j + 1, by omega⟩

    have hH_pos : 0 < H.len := by omega
    have := semidirect_existence_compl H H' hHH'_len hHH'_compl hH_pos hH_cov d₀ hd₀_H
    obtain ⟨d₁, u₁, hd₁_H, hd₁_H', hu₁_H, hu₁_unip', hd₀_eq⟩ := this

    have hu₁_id_on_H0 : ∀ v ∈ H.spaces ⟨0, by omega⟩, u₁ v = v := by
      intro v hv
      have := hu₁_unip' ⟨0, by omega⟩ v hv
      simp at this; rwa [sub_eq_zero] at this
    have hu₁_id_on_W : ∀ w ∈ W, u₁ w = w := by
      intro w hw; apply hu₁_id_on_H0
      show w ∈ G.spaces ⟨0 + 1, by omega⟩
      exact hW_le ⟨1, by omega⟩ hw

    have hu₁_W : W.map u₁.toLinearMap = W := by
      ext x; simp only [Submodule.mem_map]; constructor
      · rintro ⟨v, hv, rfl⟩
        rw [show u₁.toLinearMap v = u₁ v from rfl, hu₁_id_on_W v hv]; exact hv
      · intro hx; exact ⟨x, hx, show u₁.toLinearMap x = x from hu₁_id_on_W x hx⟩

    have hd₁_W : W.map d₁.toLinearMap = W := by
      have h1 := hd₀_preserves ⟨0, by omega⟩
      rw [hd₀_eq, Submodule.map_comp, hu₁_W] at h1; exact h1


    obtain ⟨d₂, u₂, hd₂W, hd₂W', hu₂W, hu₂_unip, hd₁_comp, hd₂_eq_d₁⟩ :=
      block_diagonal_decomp W W' hcompl_0 d₁ hd₁_W

    have hu₂_id_on_W : ∀ w ∈ W, u₂ w = w := by
      intro w hw
      have h1 : d₂ (u₂ w) = d₁ w := by
        have : d₁.toLinearMap w = (d₂.toLinearMap.comp u₂.toLinearMap) w := by rw [← hd₁_comp]
        simp at this; exact this.symm
      have h2 : d₂ w = d₁ w := hd₂_eq_d₁ w hw
      exact d₂.injective (h1.trans h2.symm)

    have hu₂_preserves : ∀ (i : Fin G.len),
        (G.spaces i).map u₂.toLinearMap = G.spaces i :=
      fun i => preserves_of_unipotent_le (G.spaces i) W u₂ hu₂_unip (hW_le i)

    have hd₂_preserves_G : ∀ (i : Fin G.len),
        (G.spaces i).map d₂.toLinearMap = G.spaces i := by
      intro i

      have hd₁_pres_i : (G.spaces i).map d₁.toLinearMap = G.spaces i := by
        by_cases hi : i.val = 0
        · rw [show i = (⟨0, by omega⟩ : Fin G.len) from Fin.ext (by omega)]; exact hd₁_W
        · have hj : i.val - 1 < H.len := by omega
          have := hd₁_H ⟨i.val - 1, hj⟩
          simp only [H, Flag.truncateStart_spaces] at this
          convert this using 2 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
      rw [hd₁_comp, Submodule.map_comp, hu₂_preserves i] at hd₁_pres_i
      exact hd₁_pres_i


    have hd₂_fwd_sub_W' : ∀ (S : Submodule k V), S ≤ W' →
        S.map d₁.toLinearMap = S → ∀ v ∈ S, d₂ v ∈ S := by
      intro S hSW' hd₁S v hv
      have hvW' : v ∈ W' := hSW' hv
      have hc : u₂ v - v ∈ W := hu₂_unip v

      have hd₁v : d₁ v = d₂ (u₂ v) := by
        have : d₁.toLinearMap v = (d₂.toLinearMap.comp u₂.toLinearMap) v := by rw [← hd₁_comp]
        simpa using this

      have hd₂v_W' : d₂ v ∈ W' := by
        have := Submodule.mem_map_of_mem (f := d₂.toLinearMap) hvW'; rwa [hd₂W'] at this

      have hd₂c_W : d₂ (u₂ v - v) ∈ W := by
        have := Submodule.mem_map_of_mem (f := d₂.toLinearMap) hc; rwa [hd₂W] at this

      have hdecomp : d₂ (u₂ v) = d₂ v + d₂ (u₂ v - v) := by
        rw [show u₂ v = v + (u₂ v - v) from by abel]; simp [map_add]

      have hd₁v_S : d₁ v ∈ S := by
        have := Submodule.mem_map_of_mem (f := d₁.toLinearMap) hv; rwa [hd₁S] at this

      have hd₂c_W' : d₂ (u₂ v - v) ∈ W' := by
        have : d₂ (u₂ v - v) = d₁ v - d₂ v := by rw [hd₁v, hdecomp]; abel
        rw [this]; exact W'.sub_mem (hSW' hd₁v_S) hd₂v_W'

      have hd₂c_zero : d₂ (u₂ v - v) = 0 := by
        have := Submodule.mem_inf.mpr ⟨hd₂c_W, hd₂c_W'⟩
        rwa [hcompl_0.inf_eq_bot, Submodule.mem_bot] at this

      have : d₂ (u₂ v) = d₂ v := by rw [hdecomp, hd₂c_zero, add_zero]

      have heq : d₁ v = d₂ v := hd₁v.trans this
      rwa [← heq]

    have hd₂_bwd_sub_W' : ∀ (S : Submodule k V), S ≤ W' →
        S.map d₁.toLinearMap = S → ∀ w ∈ S, d₂.symm w ∈ S := by
      intro S hSW' hd₁S w hw
      have hwW' : w ∈ W' := hSW' hw

      have hd₁_symm_S : S.map d₁.symm.toLinearMap = S :=
        (Submodule.map_symm_eq_iff d₁).mpr hd₁S

      have hd₂sw_W' : d₂.symm w ∈ W' := by
        have := Submodule.mem_map_of_mem (f := d₂.symm.toLinearMap) hwW'
        rwa [(Submodule.map_symm_eq_iff d₂).mpr hd₂W'] at this

      have hu₂_symm_unip : ∀ v : V, u₂.symm v - v ∈ W := by
        intro v
        have h2 : u₂ (u₂.symm v) - u₂.symm v ∈ W := hu₂_unip (u₂.symm v)
        rw [u₂.apply_symm_apply] at h2
        have : -(v - u₂.symm v) ∈ W := W.neg_mem h2
        rwa [neg_sub] at this


      have hd₁_symm_eq : d₁.symm w = u₂.symm (d₂.symm w) := by
        apply d₁.injective
        rw [d₁.apply_symm_apply]

        have : d₁.toLinearMap (u₂.symm (d₂.symm w)) =
            (d₂.toLinearMap.comp u₂.toLinearMap) (u₂.symm (d₂.symm w)) := by rw [← hd₁_comp]
        simp [LinearMap.comp_apply] at this
        exact this.symm

      have hd₁sw_S : d₁.symm w ∈ S := by
        have := Submodule.mem_map_of_mem (f := d₁.symm.toLinearMap) hw
        rwa [hd₁_symm_S] at this

      have hd₁sw_W' : d₁.symm w ∈ W' := hSW' hd₁sw_S

      have hc_W : u₂.symm (d₂.symm w) - d₂.symm w ∈ W := hu₂_symm_unip (d₂.symm w)

      rw [← hd₁_symm_eq] at hc_W


      have hc_W' : d₁.symm w - d₂.symm w ∈ W' := W'.sub_mem hd₁sw_W' hd₂sw_W'

      have hc_zero : d₁.symm w - d₂.symm w = 0 := by
        have := Submodule.mem_inf.mpr ⟨hc_W, hc_W'⟩
        rwa [hcompl_0.inf_eq_bot, Submodule.mem_bot] at this

      have : d₂.symm w = d₁.symm w := by
        have := sub_eq_zero.mp hc_zero; exact this.symm
      rw [this]; exact hd₁sw_S

    have hd₂_preserves_G' : ∀ (j : Fin G'.len),
        (G'.spaces j).map d₂.toLinearMap = G'.spaces j := by
      intro j
      by_cases hj : j.val < G'.len - 1
      ·
        have hd₁_pres : (G'.spaces j).map d₁.toLinearMap = G'.spaces j := by
          have := hd₁_H' ⟨j.val, by omega⟩
          simp only [H', Flag.truncate_spaces] at this
          convert this using 2
        have hle_W' : G'.spaces j ≤ W' := by
          have : j < (⟨G'.len - 1 - 0, by omega⟩ : Fin G'.len) := Fin.mk_lt_mk.mpr (by omega)
          exact le_of_lt (G'.strictMono this)
        exact map_eq_of_forall_mem _ _
          (hd₂_fwd_sub_W' _ hle_W' hd₁_pres)
          (hd₂_bwd_sub_W' _ hle_W' hd₁_pres)

      ·
        have hj_eq : j = ⟨G'.len - 1 - 0, by omega⟩ := by
          ext; simp; omega
        rw [hj_eq]; exact hd₂W'

    set u := (u₀.trans u₁).trans u₂ with hu_def
    refine ⟨d₂, u, hd₂_preserves_G, hd₂_preserves_G', ?_, ?_, ?_⟩
    ·
      intro i
      change (G.spaces i).map (u₂.toLinearMap.comp (u₁.toLinearMap.comp u₀.toLinearMap)) = G.spaces i
      rw [Submodule.map_comp, Submodule.map_comp, hu₀_preserves i]

      have hu₁_pres : (G.spaces i).map u₁.toLinearMap = G.spaces i := by
        by_cases hi : i.val = 0
        · rw [show i = (⟨0, by omega⟩ : Fin G.len) from Fin.ext (by omega)]; exact hu₁_W
        · have hj : i.val - 1 < H.len := by omega
          have := hu₁_H ⟨i.val - 1, hj⟩
          simp only [H, Flag.truncateStart_spaces] at this
          convert this using 2 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
      rw [hu₁_pres]; exact hu₂_preserves i
    ·
      intro i v hv
      show u₂ (u₁ (u₀ v)) - v ∈ _
      have heq : u₂ (u₁ (u₀ v)) - v =
          (u₂ (u₁ (u₀ v)) - u₁ (u₀ v)) + (u₁ (u₀ v) - u₀ v) + (u₀ v - v) := by abel
      rw [heq]
      split_ifs with hi
      ·
        rw [show i = (⟨0, by omega⟩ : Fin G.len) from Fin.ext (by omega)] at hv
        rw [hu₀_id_on_W v hv, hu₁_id_on_W v hv, hu₂_id_on_W v hv]; simp
      ·
        have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi

        have h_u₀ : u₀ v - v ∈ G.spaces ⟨i.val - 1, by omega⟩ :=
          hW_le ⟨i.val - 1, by omega⟩ (hu₀_unip v)

        have hu₀v_in : u₀ v ∈ (G.spaces i : Set V) := by
          have : (G.spaces i).map u₀.toLinearMap = G.spaces i := hu₀_preserves i
          rw [← this]; exact ⟨v, hv, rfl⟩
        have h_u₁ : u₁ (u₀ v) - u₀ v ∈ G.spaces ⟨i.val - 1, by omega⟩ := by
          have hu₀v_in_H : u₀ v ∈ H.spaces ⟨i.val - 1, by omega⟩ := by
            show u₀ v ∈ G.spaces ⟨i.val - 1 + 1, by omega⟩
            have : (⟨i.val - 1 + 1, by omega⟩ : Fin G.len) = i := Fin.ext (by simp; omega)
            rw [this]; exact hu₀v_in
          have h := hu₁_unip' ⟨i.val - 1, by omega⟩ (u₀ v) hu₀v_in_H
          by_cases hi1 : i.val - 1 = 0
          · simp [hi1] at h; rw [sub_eq_zero] at h; rw [h]; simp
          · simp [hi1] at h
            have hH_eq : H.spaces ⟨(i.val - 1) - 1, by omega⟩ =
                G.spaces ⟨(i.val - 1) - 1 + 1, by omega⟩ := by
              simp [H, Flag.truncateStart_spaces]
            rw [hH_eq] at h
            have hfin_eq : (⟨(i.val - 1) - 1 + 1, by omega⟩ : Fin G.len) =
                ⟨i.val - 1, by omega⟩ := Fin.ext (by simp; omega)
            rwa [hfin_eq] at h

        have h_u₂ : u₂ (u₁ (u₀ v)) - u₁ (u₀ v) ∈ G.spaces ⟨i.val - 1, by omega⟩ :=
          hW_le ⟨i.val - 1, by omega⟩ (hu₂_unip (u₁ (u₀ v)))
        exact (G.spaces ⟨i.val - 1, by omega⟩).add_mem
          ((G.spaces ⟨i.val - 1, by omega⟩).add_mem h_u₂ h_u₁) h_u₀
    ·
      ext v
      show q v = d₂ (u₂ (u₁ (u₀ v)))

      have hd₁_val : ∀ x, d₁ x = d₂ (u₂ x) := by
        intro x
        have : d₁.toLinearMap x = (d₂.toLinearMap.comp u₂.toLinearMap) x := by rw [← hd₁_comp]
        simpa using this

      have hd₀_val : ∀ x, d₀ x = d₁ (u₁ x) := by
        intro x
        have : d₀.toLinearMap x = (d₁.toLinearMap.comp u₁.toLinearMap) x := by rw [← hd₀_eq]
        simpa using this

      have hq_val : q v = d₀ (u₀ v) := by
        have : q.toLinearMap v = (d₀.toLinearMap.comp u₀.toLinearMap) v := by rw [← hd₀_comp]
        simpa using this
      rw [hq_val, hd₀_val, hd₁_val]
  termination_by G.len

/-- Strong-induction wrapper around `semidirect_existence_compl` that establishes the
`SemidirectExistenceProperty` for any finite-dimensional `V`: the parabolic stabilizer of
a flag admits the Levi-unipotent semidirect decomposition `p = d ∘ u`. -/
instance [FiniteDimensional k V] : SemidirectExistenceProperty k V where
  exists_decomp_linear := by
    intro F F' hopp hlen_pos hcov p hp

    suffices hmain : ∀ (n : ℕ) (F F' : Flag k V),
        Flag.isOppositeFlag F F' →
        F.len = n → (hlen_pos' : 0 < F.len) →
        F.spaces ⟨F.len - 1, by omega⟩ = ⊤ →
        ∀ (p : V ≃ₗ[k] V),
        (∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) →
        ∃ (d u : V ≃ₗ[k] V),
          (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
          (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
          (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
          (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
            u.toLinearMap v - v ∈
              if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
              else F.spaces ⟨i.val - 1, by omega⟩) ∧
          p.toLinearMap = d.toLinearMap.comp u.toLinearMap by
      exact hmain F.len F F' hopp rfl hlen_pos hcov p hp
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih_strong =>
      intro F F' hopp hlen_n hlen_pos hcov p hp
      by_cases hn1 : n ≤ 1
      · exact semidirect_existence_len_one F F' hopp (by omega) hcov p hp
      · push_neg at hn1
        apply semidirect_existence_inductive_step F F' hopp (by omega) hcov p hp
        intro G G' hGG'_len hGG'_compl hG_lt hG_pos hG_cov q hq
        exact semidirect_existence_compl G G' hGG'_len hGG'_compl hG_pos hG_cov q hq

end GeometricAlgebra
