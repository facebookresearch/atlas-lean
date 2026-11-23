/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- Any two subspaces of the same finite dimension are related by a global
linear automorphism mapping one onto the other. -/
lemma submodule_map_of_finrank_eq {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M]
    (W₁ W₂ : Submodule k M) (hdim : Module.finrank k W₁ = Module.finrank k W₂) :
    ∃ e : M ≃ₗ[k] M, W₁.map e.toLinearMap = W₂ := by
  obtain ⟨W₁', hc₁⟩ := Submodule.exists_isCompl W₁
  obtain ⟨W₂', hc₂⟩ := Submodule.exists_isCompl W₂
  have hdim' : Module.finrank k W₁' = Module.finrank k W₂' := by
    linarith [Submodule.finrank_add_eq_of_isCompl hc₁, Submodule.finrank_add_eq_of_isCompl hc₂]
  let f := LinearEquiv.ofFinrankEq W₁ W₂ hdim
  let g := LinearEquiv.ofFinrankEq W₁' W₂' hdim'
  let e := (Submodule.prodEquivOfIsCompl W₁ W₁' hc₁).symm.trans
    ((f.prodCongr g).trans (Submodule.prodEquivOfIsCompl W₂ W₂' hc₂))
  refine ⟨e, ?_⟩
  ext v; simp only [Submodule.mem_map]; constructor
  · rintro ⟨w, hw, rfl⟩; show e w ∈ W₂
    simp only [e, LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W₁ W₁' hc₁ ⟨w, hw⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' W₂ W₂' hc₂]
    simp only [Submodule.coe_zero, add_zero]; exact (f ⟨w, hw⟩).property
  · intro hv; refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩; show e.symm v ∈ W₁
    simp only [e, LinearEquiv.symm_trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W₂ W₂' hc₂ ⟨v, hv⟩]
    simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, map_zero]
    change (Submodule.prodEquivOfIsCompl W₁ W₁' hc₁) (f.symm ⟨v, hv⟩, 0) ∈ W₁
    rw [Submodule.coe_prodEquivOfIsCompl' W₁ W₁' hc₁]
    simp only [Submodule.coe_zero, add_zero]; exact (f.symm ⟨v, hv⟩).property


/-- Given a common subspace `W ≤ U₁`, `W ≤ U₂` with `U₁` and `U₂` of equal
dimension, there is a linear automorphism fixing `W` pointwise that sends `U₁`
onto `U₂`. -/
lemma adjustment_equiv [FiniteDimensional k V] (W U₁ U₂ : Submodule k V)
    (hle₁ : W ≤ U₁) (hle₂ : W ≤ U₂)
    (hdim : Module.finrank k U₁ = Module.finrank k U₂) :
    ∃ e : V ≃ₗ[k] V, (∀ w ∈ W, e w = w) ∧ U₁.map e.toLinearMap = U₂ := by
  obtain ⟨C, hWC⟩ := Submodule.exists_isCompl W

  have hdimP : Module.finrank k (U₁.comap C.subtype) =
      Module.finrank k (U₂.comap C.subtype) := by
    have hPfr : ∀ U : Submodule k V, Module.finrank k (U.comap C.subtype) =
        Module.finrank k (C ⊓ U : Submodule k V) := fun U => by
      rw [← Submodule.map_comap_subtype C U]
      exact (Submodule.finrank_map_subtype_eq C (U.comap C.subtype)).symm
    have hfr : ∀ U : Submodule k V, W ≤ U →
        Module.finrank k W + Module.finrank k (C ⊓ U : Submodule k V) =
        Module.finrank k U := fun U hle => by
      have hmod : W ⊔ (C ⊓ U) = U := by
        calc W ⊔ (C ⊓ U) = (W ⊔ C) ⊓ U := (sup_inf_assoc_of_le C hle).symm
          _ = ⊤ ⊓ U := by rw [hWC.sup_eq_top]
          _ = U := top_inf_eq U
      have hbot : W ⊓ (C ⊓ U) = ⊥ := by
        calc W ⊓ (C ⊓ U) = (W ⊓ C) ⊓ U := by rw [inf_assoc]
          _ = ⊥ ⊓ U := by rw [hWC.inf_eq_bot]
          _ = ⊥ := bot_inf_eq U
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (C ⊓ U)
      rw [hmod, hbot] at h; simp at h; linarith
    rw [hPfr U₁, hPfr U₂]; linarith [hfr U₁ hle₁, hfr U₂ hle₂]
  obtain ⟨f_C, hf_C⟩ := submodule_map_of_finrank_eq (U₁.comap C.subtype)
    (U₂.comap C.subtype) hdimP
  let decomp := Submodule.prodEquivOfIsCompl W C hWC
  let e := decomp.symm.trans (((LinearEquiv.refl k ↥W).prodCongr f_C).trans decomp)

  have comap_mem : ∀ (U : Submodule k V) (_ : W ≤ U) (v : V) (_ : v ∈ U),
      (decomp.symm v).2 ∈ U.comap C.subtype := by
    intro U hle v hv


    show ((decomp.symm v).2 : V) ∈ U
    have h_eq : ((decomp.symm v).1 : V) + ((decomp.symm v).2 : V) = v := by
      have := decomp.apply_symm_apply v
      rw [Submodule.coe_prodEquivOfIsCompl' W C hWC] at this; exact this
    have hc_eq : ((decomp.symm v).2 : V) = v - ((decomp.symm v).1 : V) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h_eq
    rw [hc_eq]; exact U.sub_mem hv (hle (decomp.symm v).1.property)
  refine ⟨e, ?_, ?_⟩

  · intro w hw; show e w = w
    simp only [e, LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W C hWC ⟨w, hw⟩]
    simp [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' W C hWC]; simp [add_zero]

  · ext v; simp only [Submodule.mem_map]; constructor
    · rintro ⟨u, hu, rfl⟩; show e u ∈ U₂
      simp only [e, LinearEquiv.trans_apply]
      change decomp (((LinearEquiv.refl k ↥W).prodCongr f_C) (decomp.symm u)) ∈ U₂
      simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
      rw [Submodule.coe_prodEquivOfIsCompl' W C hWC]
      apply U₂.add_mem (hle₂ (decomp.symm u).1.property)


      show (f_C (decomp.symm u).2 : V) ∈ U₂
      have : f_C (decomp.symm u).2 ∈ U₂.comap C.subtype := by
        rw [← hf_C]; exact Submodule.mem_map_of_mem (comap_mem U₁ hle₁ u hu)
      exact this
    · intro hv; refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      show e.symm v ∈ U₁
      have hesymm : e.symm v =
          decomp ((LinearEquiv.refl k ↥W).prodCongr f_C.symm (decomp.symm v)) := by
        simp only [e, LinearEquiv.symm_trans_apply, LinearEquiv.prodCongr_symm,
                   LinearEquiv.symm_symm, LinearEquiv.refl_symm]
      rw [hesymm]
      simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
      rw [Submodule.coe_prodEquivOfIsCompl' W C hWC]
      apply U₁.add_mem (hle₁ (decomp.symm v).1.property)
      show (f_C.symm (decomp.symm v).2 : V) ∈ U₁
      have hfc_P₁ : f_C.symm (decomp.symm v).2 ∈ U₁.comap C.subtype := by
        have hc_P₂ := comap_mem U₂ hle₂ v hv
        rw [← hf_C] at hc_P₂
        obtain ⟨x, hx, hxeq⟩ := Submodule.mem_map.mp hc_P₂
        rwa [show f_C.symm (decomp.symm v).2 = x from by rw [← hxeq]; simp]
      exact hfc_P₁


/-- If `e` fixes every element of `W` pointwise, then `e` also fixes every
subspace `S ≤ W` setwise: `S.map e = S`. -/
lemma map_eq_of_pointwise_fix (S W : Submodule k V) (e : V ≃ₗ[k] V)
    (hfix : ∀ w ∈ W, e w = w) (hle : S ≤ W) : S.map e.toLinearMap = S := by
  ext v; simp only [Submodule.mem_map]; constructor
  · rintro ⟨u, hu, rfl⟩
    have : e u = u := hfix u (hle hu)
    simp only [LinearEquiv.coe_coe] at this ⊢; rw [this]; exact hu
  · intro hv; refine ⟨v, hv, ?_⟩
    have : e v = v := hfix v (hle hv)
    simp only [LinearEquiv.coe_coe]; exact this

/-- Mapping a submodule under a composition of linear equivalences agrees with
applying the maps successively. -/
lemma map_trans_eq (S : Submodule k V) (e₁ e₂ : V ≃ₗ[k] V) :
    S.map (e₁.trans e₂).toLinearMap = (S.map e₁.toLinearMap).map e₂.toLinearMap := by
  rw [LinearEquiv.coe_trans]; exact S.map_comp e₁.toLinearMap e₂.toLinearMap


/-- Inductive helper: two strictly ascending sequences of subspaces of the same
length, with matching dimensions stage by stage, are related by a single linear
automorphism that sends each `spaces₁ i` onto `spaces₂ i`. -/
lemma flag_equiv_aux [FiniteDimensional k V] :
    ∀ (n : ℕ) (spaces₁ spaces₂ : Fin n → Submodule k V)
    (_ : StrictMono spaces₁) (_ : StrictMono spaces₂)
    (_ : ∀ i : Fin n, Module.finrank k (spaces₁ i) = Module.finrank k (spaces₂ i)),
    ∃ e : V ≃ₗ[k] V, ∀ i : Fin n, (spaces₁ i).map e.toLinearMap = spaces₂ i := by
  intro n; induction n with
  | zero => intro _ _ _ _ _; exact ⟨LinearEquiv.refl k V, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro spaces₁ spaces₂ hm₁ hm₂ hdims

    obtain ⟨e₁, he₁⟩ := ih (spaces₁ ∘ Fin.castSucc) (spaces₂ ∘ Fin.castSucc)
      (fun a b hab => hm₁ (Fin.castSucc_lt_castSucc_iff.mpr hab))
      (fun a b hab => hm₂ (Fin.castSucc_lt_castSucc_iff.mpr hab))
      (fun i => hdims (Fin.castSucc i))

    let U₁ := (spaces₁ (Fin.last n)).map e₁.toLinearMap
    let U₂ := spaces₂ (Fin.last n)
    have hdim_U : Module.finrank k U₁ = Module.finrank k U₂ := by
      simp only [U₁]; rw [LinearEquiv.finrank_map_eq]; exact hdims (Fin.last n)

    by_cases hn : n = 0
    ·
      subst hn
      obtain ⟨e₂, _, he₂_map⟩ := adjustment_equiv ⊥ U₁ U₂ bot_le bot_le hdim_U
      refine ⟨e₁.trans e₂, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      ·
        rw [map_trans_eq]; exact he₂_map
      ·
        exact Fin.elim0 j
    ·
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      subst hm
      let W := spaces₂ (Fin.castSucc (Fin.last m))

      have hW_le_U₂ : W ≤ U₂ :=
        le_of_lt (hm₂ (Fin.castSucc_lt_last (Fin.last m)))

      have hW_eq : W = ((spaces₁ ∘ Fin.castSucc) (Fin.last m)).map e₁.toLinearMap :=
        (he₁ (Fin.last m)).symm

      have hW_le_U₁ : W ≤ U₁ := by
        rw [hW_eq]; apply Submodule.map_mono
        exact le_of_lt (hm₁ (Fin.castSucc_lt_last (Fin.last m)))
      obtain ⟨e₂, hfix, he₂_map⟩ := adjustment_equiv W U₁ U₂ hW_le_U₁ hW_le_U₂ hdim_U
      refine ⟨e₁.trans e₂, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      ·
        rw [map_trans_eq]; exact he₂_map
      ·
        have he₁j := he₁ j; simp only [Function.comp_apply] at he₁j
        rw [map_trans_eq, he₁j]


        apply map_eq_of_pointwise_fix _ W e₂ hfix

        rcases (Fin.le_last j).lt_or_eq with hj | hj
        · exact le_of_lt (hm₂ (Fin.castSucc_lt_castSucc_iff.mpr hj))
        · rw [hj]


/-- Two flags of the same type (same length and same dimensions at each stage)
are `GL(V)`-equivalent: there is a single linear automorphism that sends each
subspace of one flag to the corresponding subspace of the other. -/
theorem flag_equiv_of_sameType (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ →
      ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len),
        ∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen) := by
  intro F₁ F₂ ⟨hlen, hdims⟩
  have hdims' : ∀ i : Fin F₁.len,
      Module.finrank k (F₁.spaces i) = Module.finrank k (F₂.spaces (i.cast hlen)) :=
    fun i => hdims hlen i
  let spaces₂' : Fin F₁.len → Submodule k V := fun i => F₂.spaces (i.cast hlen)
  have hm₂' : StrictMono spaces₂' := fun a b hab =>
    F₂.strictMono (by exact hab)
  obtain ⟨e, he⟩ := flag_equiv_aux F₁.len F₁.spaces spaces₂' F₁.strictMono hm₂' hdims'
  exact ⟨e, hlen, he⟩


/-- The `FlagEquivalenceProperty` instance: over any field, on a
finite-dimensional vector space, flags of the same type are `GL(V)`-equivalent. -/
instance instFlagEquivalenceProperty [FiniteDimensional k V] :
    FlagEquivalenceProperty k V where
  equiv_linear := flag_equiv_of_sameType k V

end GeometricAlgebra
