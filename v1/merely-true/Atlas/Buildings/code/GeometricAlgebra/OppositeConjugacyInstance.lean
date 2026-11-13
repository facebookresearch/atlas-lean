/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- Two complements `C₁` and `C₂` to the same subspace `W` are linearly isomorphic,
via the composition of inclusion `C₁ ↪ V` with the linear projection `V ↠ C₂`
along `W`. -/
noncomputable def complIsomOfIsCompl (W C₁ C₂ : Submodule k V)
    (hc₁ : IsCompl W C₁) (hc₂ : IsCompl W C₂) : C₁ ≃ₗ[k] C₂ := by
  let π₂ := Submodule.linearProjOfIsCompl C₂ W hc₂.symm
  let φ : C₁ →ₗ[k] C₂ := π₂.comp C₁.subtype
  have hinj : Function.Injective φ := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply] at h
    have hxy : π₂ x = π₂ y := by exact_mod_cast h
    have hd : π₂ (x - y) = 0 := by simp [map_sub, hxy]
    have hker : x - y ∈ W := by
      rwa [Submodule.linearProjOfIsCompl_apply_eq_zero_iff] at hd
    have hC₁ : x - y ∈ C₁ := C₁.sub_mem hx hy
    have hbot : x - y ∈ (W ⊓ C₁ : Submodule k V) := Submodule.mem_inf.mpr ⟨hker, hC₁⟩
    rw [hc₁.inf_eq_bot, Submodule.mem_bot] at hbot
    ext; exact sub_eq_zero.mp hbot
  have hsurj : Function.Surjective φ := by
    intro ⟨c₂, hc₂_mem⟩
    let decomp := Submodule.prodEquivOfIsCompl W C₁ hc₁
    let pair := decomp.symm c₂
    have hpair : (pair.1 : V) + (pair.2 : V) = c₂ := by
      have := decomp.apply_symm_apply c₂
      rw [Submodule.coe_prodEquivOfIsCompl' W C₁ hc₁] at this; exact this
    use pair.2
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]
    have hval : (pair.2 : V) = c₂ - (pair.1 : V) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hpair
    rw [hval, map_sub]
    have π₂_c₂ : π₂ c₂ = ⟨c₂, hc₂_mem⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc₂.symm ⟨c₂, hc₂_mem⟩
    have π₂_w : π₂ (pair.1 : V) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hc₂.symm ⟨(pair.1 : V), pair.1.property⟩
    rw [π₂_c₂, π₂_w, sub_zero]
  exact LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- The linear automorphism of `V` that fixes `W` pointwise and sends the
complement `C₁` to the complement `C₂` via `complIsomOfIsCompl`. -/
noncomputable def swapComplement (W C₁ C₂ : Submodule k V)
    (hc₁ : IsCompl W C₁) (hc₂ : IsCompl W C₂) : V ≃ₗ[k] V :=
  let φ := complIsomOfIsCompl W C₁ C₂ hc₁ hc₂
  let decomp₁ := Submodule.prodEquivOfIsCompl W C₁ hc₁
  let decomp₂ := Submodule.prodEquivOfIsCompl W C₂ hc₂
  decomp₁.symm.trans (((LinearEquiv.refl k ↥W).prodCongr φ).trans decomp₂)

/-- The `swapComplement` automorphism fixes every vector of `W` pointwise. -/
lemma swapComplement_fix_W (W C₁ C₂ : Submodule k V)
    (hc₁ : IsCompl W C₁) (hc₂ : IsCompl W C₂)
    (w : V) (hw : w ∈ W) : swapComplement W C₁ C₂ hc₁ hc₂ w = w := by
  simp only [swapComplement, LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left W C₁ hc₁ ⟨w, hw⟩]
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero]
  rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂]
  simp [add_zero]

/-- The `swapComplement` automorphism maps the complement `C₁` onto the
complement `C₂`. -/
lemma swapComplement_map_C (W C₁ C₂ : Submodule k V)
    (hc₁ : IsCompl W C₁) (hc₂ : IsCompl W C₂) :
    C₁.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = C₂ := by
  ext v; simp only [Submodule.mem_map]; constructor
  · rintro ⟨c, hc, rfl⟩
    show swapComplement W C₁ C₂ hc₁ hc₂ c ∈ C₂
    simp only [swapComplement, LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W C₁ hc₁ ⟨c, hc⟩]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂]
    simp only [Submodule.coe_zero, zero_add]
    exact (complIsomOfIsCompl W C₁ C₂ hc₁ hc₂ ⟨c, hc⟩).property
  · intro hv
    let e := swapComplement W C₁ C₂ hc₁ hc₂
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    simp only [e, swapComplement, LinearEquiv.symm_trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W C₂ hc₂ ⟨v, hv⟩]
    simp only [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, map_zero]
    rw [LinearEquiv.symm_symm]
    rw [Submodule.coe_prodEquivOfIsCompl' W C₁ hc₁]
    simp only [Submodule.coe_zero, zero_add]
    exact ((complIsomOfIsCompl W C₁ C₂ hc₁ hc₂).symm ⟨v, hv⟩).property

/-- Any subspace `S` contained in `W` is preserved by the `swapComplement`
automorphism (since it acts as the identity on `W`). -/
lemma swapComplement_preserves_sub (W C₁ C₂ S : Submodule k V)
    (hc₁ : IsCompl W C₁) (hc₂ : IsCompl W C₂) (hle : S ≤ W) :
    S.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = S :=
  map_eq_of_pointwise_fix S W (swapComplement W C₁ C₂ hc₁ hc₂)
    (swapComplement_fix_W W C₁ C₂ hc₁ hc₂) hle


/-- Hypothesis bundling the composition step needed for the conjugacy-of-opposite
flags theorem: given a flag `F` and two opposite flags `F'₁, F'₂`, there exists a
linear automorphism preserving `F` and mapping `F'₁` to `F'₂`. -/
structure OppositeConjugacyCompositionHyp (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] where
  compose_swaps : ∀ (F F'₁ F'₂ : Flag k V),
    Flag.isOppositeFlag F F'₁ →
    Flag.isOppositeFlag F F'₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen))

/-- The conjugacy theorem for opposite flags: given the composition hypothesis,
any two flags opposite to `F` are conjugate by a linear automorphism that fixes
the spaces of `F`. -/
theorem opposite_systems_conjugacy_theorem (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hyp : OppositeConjugacyCompositionHyp k V)
    (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁)
    (h₂ : Flag.isOppositeFlag F F'₂) :
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen)) :=
  hyp.compose_swaps F F'₁ F'₂ h₁ h₂

/-- Bundles `opposite_systems_conjugacy_theorem` as an instance of the
`OppositeSystemsConjugacyProperty` typeclass. -/
def instOppositeSystemsConjugacyProperty' [FiniteDimensional k V]
    (hyp : OppositeConjugacyCompositionHyp k V) :
    OppositeSystemsConjugacyProperty k V where
  conjugate_linear := fun F F'₁ F'₂ h₁ h₂ =>
    opposite_systems_conjugacy_theorem k V hyp F F'₁ F'₂ h₁ h₂

end GeometricAlgebra
