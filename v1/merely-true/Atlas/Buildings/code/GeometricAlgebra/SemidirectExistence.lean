/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- If `F'` is an opposite flag to `F`, then for each level `i` the space `F.spaces i`
and the matching level `F'.spaces (F'.len - 1 - i)` of `F'` are complementary. -/
lemma isCompl_of_isOppositeFlag
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (i : Fin F.len) :
    IsCompl (F.spaces i) (F'.spaces ⟨F'.len - 1 - i.val, by have := hopp.1; omega⟩) := by
  obtain ⟨hlen, _, hcompl⟩ := hopp
  obtain ⟨hsup, hinf⟩ := hcompl hlen i
  exact IsCompl.mk (disjoint_iff.mpr hinf) (codisjoint_iff.mpr hsup)

/-- If the top level of `F` is all of `V` and `F'` is opposite to `F`, then the bottom
level of `F'` is the zero subspace. -/
lemma opposite_top_is_bot
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤) :
    F'.spaces ⟨0, by have := hopp.1; omega⟩ = ⊥ := by

  have hcompl := isCompl_of_isOppositeFlag F F' hopp ⟨F.len - 1, by omega⟩


  have hfin : (⟨F'.len - 1 - (⟨F.len - 1, by omega⟩ : Fin F.len).val, by have := hopp.1; omega⟩ : Fin F'.len) =
    ⟨0, by have := hopp.1; omega⟩ := Fin.ext (by simp; have := hopp.1; omega)
  rw [hfin] at hcompl
  rw [hcov] at hcompl
  exact eq_bot_of_isCompl_top hcompl.symm

/-- Base case of the semidirect existence theorem: for a length-one flag (with the
unique level equal to `V`), the trivial factorization `p = p ∘ id` works. -/
theorem semidirect_existence_len_one
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen1 : F.len = 1) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (p : V ≃ₗ[k] V)
    (hp : ∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) :
    ∃ (d u : V ≃ₗ[k] V),
      (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
      (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
        u.toLinearMap v - v ∈
          if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
          else F.spaces ⟨i.val - 1, by omega⟩) ∧
      p.toLinearMap = d.toLinearMap.comp u.toLinearMap := by

  refine ⟨p, LinearEquiv.refl k V, hp, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    have hlen' : F'.len = 1 := by have := hopp.1; omega

    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hi]


    have hbot := opposite_top_is_bot F F' hopp (by omega) hcov

    rw [show (⟨0, by omega⟩ : Fin F'.len) = ⟨0, by have := hopp.1; omega⟩ from
      Fin.ext (by omega)]
    rw [hbot]
    exact Submodule.map_bot _
  ·
    intro i
    simp [LinearEquiv.refl_toLinearMap, Submodule.map_id]
  ·
    intro i v _
    have hi : (i : ℕ) = 0 := by omega
    simp [hi, sub_self]
  ·
    simp [LinearMap.comp_id]

/-- A submodule `W` is preserved by a linear equivalence `e` iff `e` maps `W` into
itself and `e.symm` maps `W` into itself. -/
lemma map_eq_of_forall_mem (W : Submodule k V) (e : V ≃ₗ[k] V)
    (h1 : ∀ w ∈ W, e w ∈ W) (h2 : ∀ w ∈ W, e.symm w ∈ W) :
    W.map e.toLinearMap = W := by
  ext x; simp only [Submodule.mem_map]
  exact ⟨fun ⟨w, hw, he⟩ => he ▸ h1 w hw, fun hx => ⟨e.symm x, h2 x hx, by simp⟩⟩

/-- Block-diagonal decomposition: given a `p`-stable subspace `W` with complement `W'`,
factor `p = d₀ ∘ u₀` where `d₀` is block-diagonal (stabilizes both `W` and `W'` and agrees
with `p` on `W`) and `u₀` is "unipotent" along `W` (i.e. `u₀ v - v ∈ W` for every `v`).
The block-diagonal part `d₀` is constructed via the projection `W' →ₗ W'` induced by `p`. -/
theorem block_diagonal_decomp
    [FiniteDimensional k V]
    (W W' : Submodule k V) (hc : IsCompl W W')
    (p : V ≃ₗ[k] V)
    (hpW : W.map p.toLinearMap = W) :
    ∃ (d₀ u₀ : V ≃ₗ[k] V),
      (W.map d₀.toLinearMap = W) ∧
      (W'.map d₀.toLinearMap = W') ∧
      (W.map u₀.toLinearMap = W) ∧
      (∀ v : V, u₀.toLinearMap v - v ∈ W) ∧
      p.toLinearMap = d₀.toLinearMap.comp u₀.toLinearMap ∧
      (∀ w ∈ W, d₀ w = p w) := by

  let πW' := Submodule.linearProjOfIsCompl W' W hc.symm

  let D : W' →ₗ[k] W' := πW'.comp (p.toLinearMap.comp W'.subtype)

  have hD_inj : Function.Injective D := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hD_sub : D (⟨x, hx⟩ - ⟨y, hy⟩) = 0 := by simp [map_sub, h]
    change πW' (p (x - y)) = 0 at hD_sub
    rw [Submodule.linearProjOfIsCompl_apply_eq_zero_iff] at hD_sub
    have hxy_W : x - y ∈ W := by
      have hWsymm : W.map p.symm.toLinearMap = W := (Submodule.map_symm_eq_iff p).mpr hpW
      have : p.symm (p (x - y)) ∈ W.map p.symm.toLinearMap := Submodule.mem_map_of_mem hD_sub
      rwa [hWsymm, LinearEquiv.symm_apply_apply] at this
    exact Subtype.ext (sub_eq_zero.mp ((Submodule.mem_bot k).mp
      (hc.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨hxy_W, W'.sub_mem hx hy⟩)))

  have hD_bij : Function.Bijective D :=
    ⟨hD_inj, LinearMap.injective_iff_surjective.mp hD_inj⟩

  let D_equiv : W' ≃ₗ[k] W' := LinearEquiv.ofBijective D hD_bij
  let p_W : W ≃ₗ[k] W := p.ofSubmodules W W hpW
  let decomp := Submodule.prodEquivOfIsCompl W W' hc

  let d₀ : V ≃ₗ[k] V := decomp.symm.trans ((p_W.prodCongr D_equiv).trans decomp)

  let u₀ : V ≃ₗ[k] V := p.trans d₀.symm

  have hd₀_W_fwd : ∀ w ∈ W, d₀ w ∈ W := by
    intro w hw
    show decomp ((p_W.prodCongr D_equiv) (decomp.symm w)) ∈ W
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W W' hc ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl']; simp
  have hd₀_W_bwd : ∀ w ∈ W, d₀.symm w ∈ W := by
    intro w hw
    show decomp ((p_W.prodCongr D_equiv).symm (decomp.symm w)) ∈ W
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W W' hc ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl']; simp

  have hd₀_W'_fwd : ∀ w ∈ W', d₀ w ∈ W' := by
    intro w hw
    show decomp ((p_W.prodCongr D_equiv) (decomp.symm w)) ∈ W'
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W W' hc ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl']; simp
  have hd₀_W'_bwd : ∀ w ∈ W', d₀.symm w ∈ W' := by
    intro w hw
    show decomp ((p_W.prodCongr D_equiv).symm (decomp.symm w)) ∈ W'
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W W' hc ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl']; simp

  have h_diff_in_W : ∀ v : V, p v - d₀ v ∈ W := by
    intro v
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff (hc.symm)]
    simp only [map_sub]

    have hpv : πW' (p v) = D (πW' v) := by
      have hv : v = ↑((Submodule.linearProjOfIsCompl W W' hc) v) + ↑(πW' v) := by
        have h := decomp.apply_symm_apply v
        rw [Submodule.prodEquivOfIsCompl_symm_apply] at h
        rw [Submodule.coe_prodEquivOfIsCompl'] at h; exact h.symm
      conv_lhs => rw [hv]; simp only [map_add]
      have hp_in_W : p ↑((Submodule.linearProjOfIsCompl W W' hc) v) ∈ W := by
        have : p ↑((Submodule.linearProjOfIsCompl W W' hc) v) ∈ W.map p.toLinearMap :=
          Submodule.mem_map_of_mem ((Submodule.linearProjOfIsCompl W W' hc) v).2
        rwa [hpW] at this
      rw [(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).mpr hp_in_W]
      simp only [zero_add]; rfl

    have hd₀v : πW' (d₀ v) = D_equiv (πW' v) := by
      show πW' (decomp ((p_W.prodCongr D_equiv) (decomp.symm v))) = D_equiv (πW' v)
      rw [Submodule.prodEquivOfIsCompl_symm_apply]
      simp only [LinearEquiv.prodCongr_apply]
      rw [Submodule.coe_prodEquivOfIsCompl']
      simp only [map_add]
      rw [Submodule.linearProjOfIsCompl_apply_right hc.symm
        (p_W ((Submodule.linearProjOfIsCompl W W' hc) v))]
      rw [Submodule.linearProjOfIsCompl_apply_left hc.symm (D_equiv (πW' v))]
      simp

    rw [hpv, hd₀v, show (D_equiv (πW' v) : W') = D (πW' v) from
      LinearEquiv.ofBijective_apply D (πW' v), sub_self]

  have hd₀_eq_p_on_W : ∀ w ∈ W, d₀ w = p w := by
    intro w hw
    show decomp ((p_W.prodCongr D_equiv) (decomp.symm w)) = p w
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W W' hc ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp only [Submodule.coe_zero, add_zero]
    rfl

  refine ⟨d₀, u₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact map_eq_of_forall_mem W d₀ hd₀_W_fwd hd₀_W_bwd
  ·
    exact map_eq_of_forall_mem W' d₀ hd₀_W'_fwd hd₀_W'_bwd
  ·
    apply map_eq_of_forall_mem
    · intro w hw
      show d₀.symm (p w) ∈ W
      have : p w ∈ W := by
        have := Submodule.mem_map_of_mem (f := p.toLinearMap) hw; rwa [hpW] at this
      exact hd₀_W_bwd _ this
    · intro w hw
      show (p.trans d₀.symm).symm w ∈ W
      simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
      have hd₀w : d₀ w ∈ W := hd₀_W_fwd _ hw
      have hWsymm : W.map p.symm.toLinearMap = W := (Submodule.map_symm_eq_iff p).mpr hpW
      have : p.symm (d₀ w) ∈ W.map p.symm.toLinearMap := Submodule.mem_map_of_mem hd₀w
      rwa [hWsymm] at this
  ·
    intro v
    show d₀.symm (p v) - v ∈ W
    have : d₀.symm (p v) - v = d₀.symm (p v - d₀ v) := by
      simp [map_sub, LinearEquiv.symm_apply_apply]
    rw [this]
    exact hd₀_W_bwd _ (h_diff_in_W v)
  ·
    ext v
    show p v = d₀ (u₀ v)
    change p v = d₀ (d₀.symm (p v))
    simp
  ·
    exact hd₀_eq_p_on_W

/-- A "unipotent" linear equivalence (one whose deviation from the identity lies
in `W`) preserves every submodule `S` containing `W`. -/
lemma preserves_of_unipotent_le (S W : Submodule k V) (e : V ≃ₗ[k] V)
    (hunip : ∀ v : V, e.toLinearMap v - v ∈ W) (hle : W ≤ S) :
    S.map e.toLinearMap = S := by
  apply map_eq_of_forall_mem
  · intro v hv
    have : e v = v + (e v - v) := by abel
    rw [this]; exact S.add_mem hv (hle (hunip v))
  · intro w hw
    have key : w - e.symm w ∈ W := by
      have h1 : e (e.symm w) = w := e.apply_symm_apply w
      have h2 : e (e.symm w) - e.symm w ∈ W := hunip (e.symm w)
      rwa [h1] at h2
    have : e.symm w = w - (w - e.symm w) := by abel
    rw [this]; exact S.sub_mem hw (hle key)

/-- Inductive step of the semidirect existence theorem: given the IH for shorter
flags, factor a stabilizer of `F` as `p = d ∘ u` where `d` preserves both `F`
and the opposite flag `F'`, and `u` is unipotent along the flag. -/
theorem semidirect_existence_inductive_step
    [FiniteDimensional k V]
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 2 ≤ F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (p : V ≃ₗ[k] V)
    (hp : ∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i)
    (ih : ∀ (G G' : Flag k V),
      G.len = G'.len →
      (∀ (hlen_eq : G.len = G'.len) (i : Fin G.len),
        G.spaces i ⊔ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊤ ∧
        G.spaces i ⊓ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊥) →
      G.len < F.len → (hGpos : 0 < G.len) →

      G.spaces ⟨G.len - 1, by omega⟩ = ⊤ →
      ∀ (q : V ≃ₗ[k] V),
      (∀ j : Fin G.len, (G.spaces j).map q.toLinearMap = G.spaces j) →
      ∃ (d u : V ≃ₗ[k] V),
        (∀ j : Fin G.len, (G.spaces j).map d.toLinearMap = G.spaces j) ∧
        (∀ j : Fin G'.len, (G'.spaces j).map d.toLinearMap = G'.spaces j) ∧
        (∀ j : Fin G.len, (G.spaces j).map u.toLinearMap = G.spaces j) ∧
        (∀ j : Fin G.len, ∀ v ∈ G.spaces j,
          u.toLinearMap v - v ∈
            if _ : (j : ℕ) = 0 then (⊥ : Submodule k V)
            else G.spaces ⟨j.val - 1, by omega⟩) ∧
        q.toLinearMap = d.toLinearMap.comp u.toLinearMap) :
    ∃ (d u : V ≃ₗ[k] V),
      (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
      (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
        u.toLinearMap v - v ∈
          if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
          else F.spaces ⟨i.val - 1, by omega⟩) ∧
      p.toLinearMap = d.toLinearMap.comp u.toLinearMap := by

  set n := F.len with hn_def
  have hlen_eq : F.len = F'.len := hopp.1

  set W := F.spaces ⟨0, by omega⟩ with hW_def
  set W'_idx : Fin F'.len := ⟨F'.len - 1 - 0, by omega⟩
  set W' := F'.spaces W'_idx with hW'_def
  have hcompl : IsCompl W W' :=
    isCompl_of_isOppositeFlag F F' hopp ⟨0, by omega⟩

  have hpW : W.map p.toLinearMap = W := hp ⟨0, by omega⟩

  obtain ⟨d₀, u₀, hd₀W, hd₀W', hu₀W, hu₀_unip, hcomp, hd₀_eq_p⟩ :=
    block_diagonal_decomp W W' hcompl p hpW


  have hW_le : ∀ (i : Fin n), W ≤ F.spaces i := by
    intro ⟨i, hi⟩
    by_cases h0 : i = 0
    · subst h0; exact le_refl _
    · exact le_of_lt (F.strictMono (Fin.mk_lt_mk.mpr (by omega)))

  have hu₀_id_on_W : ∀ w ∈ W, u₀ w = w := by
    intro w hw


    have h1 : d₀ (u₀ w) = p w := by
      have : p.toLinearMap w = (d₀.toLinearMap.comp u₀.toLinearMap) w := by rw [← hcomp]
      simp at this; exact this.symm
    have h2 : d₀ w = p w := hd₀_eq_p w hw
    exact d₀.injective (h1.trans h2.symm)

  have hu₀_preserves : ∀ (i : Fin n), (F.spaces i).map u₀.toLinearMap = F.spaces i := by
    intro i; exact preserves_of_unipotent_le (F.spaces i) W u₀ hu₀_unip (hW_le i)

  have hd₀_preserves : ∀ (i : Fin n), (F.spaces i).map d₀.toLinearMap = F.spaces i := by
    intro i
    have h1 := hp i
    rw [hcomp, Submodule.map_comp, hu₀_preserves i] at h1
    exact h1

  have hF_ge1 : 1 ≤ F.len := by omega
  have hF'_ge1 : 1 ≤ F'.len := by omega
  set G := F.truncateStart hF_ge1
  set G' := F'.truncate hF'_ge1

  have hG_len : G.len = n - 1 := rfl

  have hG'_len : G'.len = n - 1 := by show F'.len - 1 = F.len - 1; omega

  have hGG'_len : G.len = G'.len := by simp [hG_len, hG'_len]

  have hG_cov : G.spaces ⟨G.len - 1, by omega⟩ = ⊤ := by
    simp only [G, Flag.truncateStart_spaces]
    convert hcov using 2
    apply Fin.ext; simp; omega

  have hGG'_compl : ∀ (hlen' : G.len = G'.len) (i : Fin G.len),
      G.spaces i ⊔ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊤ ∧
      G.spaces i ⊓ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊥ := by
    intro _ ⟨i, hi⟩
    simp only [G, Flag.truncateStart_spaces, G', Flag.truncate_spaces, hG_len] at hi ⊢
    obtain ⟨_, _, horiginal⟩ := hopp
    have key := horiginal hlen_eq ⟨i + 1, by omega⟩
    simp only at key
    constructor
    · convert key.1 using 2; congr 1; apply Fin.ext; simp; omega
    · convert key.2 using 2; congr 1; apply Fin.ext; simp; omega

  have hd₀_G : ∀ j : Fin G.len, (G.spaces j).map d₀.toLinearMap = G.spaces j := by
    intro ⟨j, hj⟩
    simp only [G, Flag.truncateStart_spaces, hG_len] at hj ⊢
    exact hd₀_preserves ⟨j + 1, by omega⟩

  have hG_pos : 0 < G.len := by omega
  have hG_lt : G.len < F.len := by omega
  obtain ⟨d₁, u₁, hd₁_G, hd₁_G', hu₁_G, hu₁_unip, hd₀_comp⟩ :=
    ih G G' hGG'_len hGG'_compl hG_lt hG_pos hG_cov d₀ hd₀_G

  have hu₁_id_on_G0 : ∀ v ∈ G.spaces ⟨0, by omega⟩, u₁ v = v := by
    intro v hv
    have := hu₁_unip ⟨0, by omega⟩ v hv
    simp at this; rwa [sub_eq_zero] at this
  have hu₁_id_on_W : ∀ w ∈ W, u₁ w = w := by
    intro w hw
    apply hu₁_id_on_G0
    show w ∈ F.spaces ⟨0 + 1, by omega⟩
    exact hW_le ⟨1, by omega⟩ hw

  have hu₁_W : W.map u₁.toLinearMap = W := by
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [show u₁.toLinearMap v = u₁ v from rfl, hu₁_id_on_W v hv]; exact hv
    · intro hx; exact ⟨x, hx, show u₁.toLinearMap x = x from hu₁_id_on_W x hx⟩

  have hd₁_W : W.map d₁.toLinearMap = W := by
    have h1 := hd₀_preserves ⟨0, by omega⟩

    rw [hd₀_comp, Submodule.map_comp, hu₁_W] at h1
    exact h1


  set u := u₀.trans u₁ with hu_def
  refine ⟨d₁, u, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    by_cases hi : i.val = 0
    · rw [show i = (⟨0, by omega⟩ : Fin F.len) from Fin.ext (by omega)]
      exact hd₁_W
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hj : i.val - 1 < G.len := by omega
      have := hd₁_G ⟨i.val - 1, hj⟩
      simp only [G, Flag.truncateStart_spaces] at this
      convert this using 2 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
  ·
    intro i
    by_cases hi : i.val < F'.len - 1
    ·
      have := hd₁_G' ⟨i.val, by omega⟩
      simp only [G', Flag.truncate_spaces] at this
      convert this using 2
    ·
      have hi_eq : i.val = F'.len - 1 := by omega
      have htop : F'.spaces i = ⊤ := by
        have hsame := hopp.2.1
        obtain ⟨_, hdim⟩ := hsame
        have h1 : Module.finrank k ↥(F.spaces ⟨n - 1, by omega⟩) =
            Module.finrank k ↥(F'.spaces ⟨n - 1, by omega⟩) :=
          hdim hlen_eq ⟨n - 1, by omega⟩
        rw [hcov, finrank_top] at h1
        have hi_fin : i = ⟨n - 1, by omega⟩ := by
          apply Fin.ext; simp [hi_eq]; omega
        rw [hi_fin]
        exact Submodule.eq_top_of_finrank_eq h1.symm

      rw [htop, Submodule.map_top, LinearMap.range_eq_top.mpr d₁.surjective]
  ·
    intro i

    change (F.spaces i).map (u₁.toLinearMap.comp u₀.toLinearMap) = F.spaces i
    rw [Submodule.map_comp, hu₀_preserves i]

    by_cases hi : i.val = 0
    · rw [show i = (⟨0, by omega⟩ : Fin F.len) from Fin.ext (by omega)]; exact hu₁_W
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hj : i.val - 1 < G.len := by omega
      have := hu₁_G ⟨i.val - 1, hj⟩
      simp only [G, Flag.truncateStart_spaces] at this
      convert this using 2 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
  ·
    intro i v hv

    show u₁ (u₀ v) - v ∈ _
    have heq : u₁ (u₀ v) - v = (u₁ (u₀ v) - u₀ v) + (u₀ v - v) := by abel
    rw [heq]
    split_ifs with hi
    ·


      rw [show i = (⟨0, by omega⟩ : Fin F.len) from Fin.ext (by omega)] at hv
      rw [hu₀_id_on_W v hv, hu₁_id_on_W v hv]
      simp
    ·
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi

      have h_u₀ : u₀ v - v ∈ F.spaces ⟨i.val - 1, by omega⟩ :=
        hW_le ⟨i.val - 1, by omega⟩ (hu₀_unip v)

      have hu₀v_in : u₀ v ∈ (F.spaces i : Set V) := by
        have : (F.spaces i).map u₀.toLinearMap = F.spaces i := hu₀_preserves i
        rw [← this]; exact ⟨v, hv, rfl⟩

      have hu₀v_in_G : u₀ v ∈ G.spaces ⟨i.val - 1, by omega⟩ := by
        show u₀ v ∈ F.spaces ⟨i.val - 1 + 1, by omega⟩
        have : (⟨↑i - 1 + 1, by omega⟩ : Fin F.len) = i := Fin.ext (by simp; omega)
        rw [this]; exact hu₀v_in
      have h_u₁ : u₁ (u₀ v) - u₀ v ∈ F.spaces ⟨i.val - 1, by omega⟩ := by
        have h := hu₁_unip ⟨i.val - 1, by omega⟩ (u₀ v) hu₀v_in_G
        by_cases hi1 : i.val - 1 = 0
        · simp [hi1] at h; rw [sub_eq_zero] at h; rw [h]; simp
        · simp [hi1] at h

          show u₁ (u₀ v) - u₀ v ∈ F.spaces ⟨i.val - 1, by omega⟩
          have hG_eq : G.spaces ⟨(i.val - 1) - 1, by omega⟩ = F.spaces ⟨(i.val - 1) - 1 + 1, by omega⟩ := by
            simp [G, Flag.truncateStart_spaces]
          rw [hG_eq] at h
          have hfin_eq : (⟨(i.val - 1) - 1 + 1, by omega⟩ : Fin F.len) = ⟨i.val - 1, by omega⟩ :=
            Fin.ext (by simp; omega)
          rwa [hfin_eq] at h

      exact (F.spaces ⟨i.val - 1, by omega⟩).add_mem h_u₁ h_u₀
  ·
    ext v
    show p v = d₁ (u₁ (u₀ v))

    have hd₀_val : ∀ x, d₀ x = d₁ (u₁ x) := by
      intro x
      have : d₀.toLinearMap x = (d₁.toLinearMap.comp u₁.toLinearMap) x := by rw [← hd₀_comp]
      simpa [LinearMap.comp_apply] using this
    rw [← hd₀_val]

    have : p.toLinearMap v = (d₀.toLinearMap.comp u₀.toLinearMap) v := by rw [← hcomp]
    simpa [LinearMap.comp_apply] using this

end GeometricAlgebra
