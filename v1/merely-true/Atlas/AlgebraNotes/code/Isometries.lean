/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped EuclideanSpace

noncomputable section

namespace Isometries

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def linearDet (f : Plane ≃ᵃⁱ[ℝ] Plane) : ℝ :=
  LinearMap.det (f.linear.toLinearMap)

def IsTranslation (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ v : Plane, ∀ x : Plane, f x = v +ᵥ x

def IsRotation (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ p : Plane, f p = p ∧ linearDet f = 1 ∧ ¬IsTranslation f

def IsReflection (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ L : AffineSubspace ℝ Plane,
    Module.finrank ℝ L.direction = 1 ∧
    (∀ x : Plane, x ∈ L → f x = x) ∧
    linearDet f = -1

def IsGlideReflection (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  linearDet f = -1 ∧
    ∃ (L : AffineSubspace ℝ Plane),
      Module.finrank ℝ L.direction = 1 ∧
        ∃ (v : Plane), v ∈ L.direction ∧ v ≠ 0 ∧
          ∀ x ∈ L, (f x : Plane) = v +ᵥ x

lemma affine_decomp_aux (f : Plane ≃ᵃⁱ[ℝ] Plane) (x : Plane) :
    (f x : Plane) = f.linearIsometryEquiv x + f 0 :=
  congr_fun f.toAffineIsometry.toAffineMap.decomp x

set_option maxHeartbeats 2000000 in
theorem plane_isometry_classification (f : Plane ≃ᵃⁱ[ℝ] Plane) :
    IsTranslation f ∨ IsRotation f ∨ IsReflection f ∨ IsGlideReflection f := by
  classical
  set A := (f.linearIsometryEquiv.toLinearEquiv : Plane →ₗ[ℝ] Plane)
  set bONB := EuclideanSpace.basisFun (Fin 2) ℝ
  set bas := bONB.toBasis
  set M := (LinearMap.toMatrix bas bas) A
  have hMorth : M.transpose * M = 1 := by
    have hmem := f.linearIsometryEquiv.toMatrix_mem_unitaryGroup bONB bONB
    rw [Matrix.mem_unitaryGroup_iff] at hmem; change M * star M = 1 at hmem
    have hstar : star M = M.transpose := by
      ext i j; simp [Matrix.star_apply, star_trivial, Matrix.transpose_apply]
    rw [hstar] at hmem; rwa [Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)] at hmem
  have h00 : M 0 0 ^ 2 + M 1 0 ^ 2 = 1 := by
    have := congr_fun (congr_fun hMorth 0) 0
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at this; nlinarith
  have h11 : M 0 1 ^ 2 + M 1 1 ^ 2 = 1 := by
    have := congr_fun (congr_fun hMorth 1) 1
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at this; nlinarith
  have h01 : M 0 0 * M 0 1 + M 1 0 * M 1 1 = 0 := by
    have := congr_fun (congr_fun hMorth 0) 1
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at this; linarith
  have hdet_or : linearDet f = 1 ∨ linearDet f = -1 := by
    suffices M.det = 1 ∨ M.det = -1 by
      have h : linearDet f = M.det := by
        unfold linearDet; exact (LinearMap.det_toMatrix bas A).symm
      rw [h]; exact this
    have h := OrthonormalBasis.det_to_matrix_orthonormalBasis_real bONB
      (bONB.map f.linearIsometryEquiv)
    rw [Module.Basis.det_apply] at h
    have heq : bas.toMatrix ⇑(bONB.map f.linearIsometryEquiv) = M := by
      ext i j
      simp [Module.Basis.toMatrix, OrthonormalBasis.map_apply,
        OrthonormalBasis.coe_toBasis, LinearMap.toMatrix_apply, M, A, bas]
    rw [← heq]; exact h
  rcases hdet_or with hdet1 | hdet_neg1
  ·
    by_cases hlin : ∀ x : Plane, f.linearIsometryEquiv x = x
    · left
      exact ⟨f 0, fun x => by
        have h := affine_decomp_aux f x; rw [hlin x] at h
        show f x = f 0 + x; rw [h, add_comm]⟩
    · right; left
      have hdetM1 : M.det = 1 := by
        have : linearDet f = M.det := by unfold linearDet; exact (LinearMap.det_toMatrix bas A).symm
        linarith
      have hsurj : Function.Surjective (LinearMap.id (M := Plane) (R := ℝ) - A) := by
        apply LinearMap.surjective_of_injective; rw [← LinearMap.ker_eq_bot]
        by_contra hker; push_neg at hker
        rw [← @LinearMap.det_eq_zero_iff_ker_ne_bot ℝ _ Plane _ _ _ _ _ _] at hker
        have hdet_zero : (1 - M).det = 0 := by
          have h1 := (LinearMap.det_toMatrix bas (LinearMap.id - A)).symm
          have hms : (LinearMap.toMatrix bas bas) (LinearMap.id - A) = 1 - M := by
            have := map_sub (LinearMap.toMatrix bas bas).toLinearMap LinearMap.id A
            simp only [LinearEquiv.coe_toLinearMap] at this; rw [this]; congr 1; ext i j; simp
          rw [h1, hms] at hker; exact hker
        have htr' : M 0 0 + M 1 1 = 2 := by
          have : (1 - M).det = 2 - (M 0 0 + M 1 1) := by
            simp [Matrix.det_fin_two]; rw [Matrix.det_fin_two] at hdetM1; ring_nf; linarith
          linarith
        have hM00 : M 0 0 = 1 := by nlinarith
        have hM11 : M 1 1 = 1 := by linarith
        have hM10 : M 1 0 = 0 := by nlinarith
        have hM01 : M 0 1 = 0 := by nlinarith
        have hMI : M = 1 := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> linarith
        have htoM_id : (LinearMap.toMatrix bas bas) (LinearMap.id : Plane →ₗ[ℝ] Plane) = 1 := by
          ext i j; simp
        have hAid : A = LinearMap.id := (LinearMap.toMatrix bas bas).injective
          (hMI.trans htoM_id.symm)
        exact hlin (fun x => by
          have : A x = LinearMap.id x := congr_fun (congrArg DFunLike.coe hAid) x
          simpa using this)
      obtain ⟨p, hp⟩ := hsurj (f 0)
      simp only [LinearMap.sub_apply, LinearMap.id_apply] at hp
      refine ⟨p, ?_, hdet1, ?_⟩
      · exact (affine_decomp_aux f p).trans (by
          have h : (f 0 : Plane) = p - f.linearIsometryEquiv p := hp.symm
          rw [h]; abel)
      · intro ⟨v, hv⟩; apply hlin; intro x
        have h0 : (f 0 : Plane) = v := by have := hv 0; simpa using this
        have h3 := affine_decomp_aux f x; rw [h0] at h3
        have h4 : (f x : Plane) = v + x := hv x
        have heq : f.linearIsometryEquiv x + v = v + x := by rw [← h3, h4]
        exact add_right_cancel (heq.trans (add_comm v x))
  ·
    have hdetM_neg1 : M.det = -1 := by
      have : linearDet f = M.det := by unfold linearDet; exact (LinearMap.det_toMatrix bas A).symm
      linarith
    have htr : M 0 0 + M 1 1 = 0 := by
      nlinarith [sq_nonneg (M 0 0 + M 1 1), sq_nonneg (M 0 0 - M 1 1),
                 sq_nonneg (M 0 0 * M 0 1 - M 1 0 * M 1 1),
                 Matrix.det_fin_two M ▸ hdetM_neg1]
    have hker_ne_bot : LinearMap.ker (LinearMap.id - A) ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, (LinearMap.det_toMatrix bas _).symm]
      have hms : (LinearMap.toMatrix bas bas) (LinearMap.id - A) = 1 - M := by
        have := map_sub (LinearMap.toMatrix bas bas).toLinearMap LinearMap.id A
        simp only [LinearEquiv.coe_toLinearMap] at this; rw [this]; congr 1; ext i j; simp
      rw [hms]; simp [Matrix.det_fin_two]; rw [Matrix.det_fin_two] at hdetM_neg1; linarith
    rw [ne_eq, Submodule.eq_bot_iff] at hker_ne_bot; push_neg at hker_ne_bot
    obtain ⟨e₁, he₁_mem, he₁_ne⟩ := hker_ne_bot
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at he₁_mem

    have hMM : M * M = 1 := by
      have hd : M 1 1 = -(M 0 0) := by linarith
      have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -1 := by
        rw [← Matrix.det_fin_two]; exact hdetM_neg1
      have h10 : M 1 0 = M 0 1 := by nlinarith [h00, h11, sq_nonneg (M 0 0), sq_nonneg (M 1 0), sq_nonneg (M 0 1)]
      have hMsymm : M = M.transpose := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply] <;> linarith
      calc M * M = M * M.transpose := by rw [← hMsymm]
        _ = 1 := by rwa [Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)] at hMorth
    have hA_sq : ∀ x : Plane, A (A x) = x := by
      intro x
      have hAA : A.comp A = LinearMap.id := by
        apply (LinearMap.toMatrix bas bas).injective
        have h1 : (LinearMap.toMatrix bas bas) (A.comp A) = M * M := by
          rw [LinearMap.toMatrix_comp bas bas bas]
        have h2 : (LinearMap.toMatrix bas bas) (LinearMap.id : Plane →ₗ[ℝ] Plane) = 1 := by
          ext i j; simp
        rw [h1, h2, hMM]
      exact congr_fun (congrArg DFunLike.coe hAA) x
    set b : Plane := f 0
    set bplus : Plane := (1/2 : ℝ) • (b + A b)
    set L := AffineSubspace.mk' ((1/2 : ℝ) • b) (Submodule.span ℝ {e₁})
    have hfinrank_L : Module.finrank ℝ L.direction = 1 := by
      rw [AffineSubspace.direction_mk']; exact finrank_span_singleton he₁_ne
    have hf_on_L : ∀ x ∈ L, (f x : Plane) = bplus + x := by
      intro x hx; rw [AffineSubspace.mem_mk'] at hx
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx
      have hx_eq : x = (1/2 : ℝ) • b + s • e₁ := by
        have h := (sub_eq_iff_eq_add.mp hs.symm); rw [h, add_comm]
      rw [hx_eq, affine_decomp_aux]
      show A ((1/2 : ℝ) • b + s • e₁) + b = bplus + ((1/2 : ℝ) • b + s • e₁)
      have h1 : A ((1/2 : ℝ) • b + s • e₁) = (1/2 : ℝ) • A b + s • e₁ := by
        rw [map_add, map_smul, LinearMap.map_smul, ← he₁_mem]
      rw [h1]; module
    have hA_bplus : A bplus = bplus := by
      show A ((1/2 : ℝ) • (b + A b)) = (1/2 : ℝ) • (b + A b)
      rw [map_smul, map_add, hA_sq b]; congr 1; abel
    have hker_dim_le_1 : Module.finrank ℝ (LinearMap.ker (LinearMap.id - A)) ≤ 1 := by
      by_contra h_gt; push_neg at h_gt
      have hdim : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
      have hker_eq_top : LinearMap.ker (LinearMap.id - A) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by
          have := Submodule.finrank_le (LinearMap.ker (LinearMap.id - A)); omega)
      have hA_eq_id : A = LinearMap.id := by
        have hh : ∀ x : Plane, A x = x := by
          intro x
          have hx : x ∈ LinearMap.ker (LinearMap.id - A) := hker_eq_top ▸ Submodule.mem_top
          rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
          exact hx.symm
        exact LinearMap.ext hh
      have : linearDet f = 1 := by
        unfold linearDet
        have : (f.linear.toLinearMap : Plane →ₗ[ℝ] Plane) = LinearMap.id := hA_eq_id
        rw [this]; simp
      linarith
    have hker_dim_eq_1 : Module.finrank ℝ (LinearMap.ker (LinearMap.id - A)) = 1 := by
      have he₁_in_ker : e₁ ∈ LinearMap.ker (LinearMap.id - A) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        exact he₁_mem
      have hge : 0 < Module.finrank ℝ (LinearMap.ker (LinearMap.id - A)) := by
        have : Nontrivial (LinearMap.ker (LinearMap.id - A)) := by
          exact ⟨⟨⟨e₁, he₁_in_ker⟩, 0, fun h => he₁_ne (congr_arg Subtype.val h)⟩⟩
        exact Module.finrank_pos
      omega
    have hker_eq_span : LinearMap.ker (LinearMap.id - A) = Submodule.span ℝ {e₁} := by
      have he₁_in : e₁ ∈ LinearMap.ker (LinearMap.id - A) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        exact he₁_mem
      exact (Submodule.eq_of_le_of_finrank_le
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr he₁_in))
        (by rw [finrank_span_singleton he₁_ne, hker_dim_eq_1])).symm
    have hbplus_mem : bplus ∈ Submodule.span ℝ ({e₁} : Set Plane) := by
      rw [← hker_eq_span, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hA_bplus.symm
    by_cases hbplus_zero : bplus = 0
    · right; right; left
      refine ⟨L, hfinrank_L, ?_, hdet_neg1⟩
      intro x hx; have := hf_on_L x hx; rw [hbplus_zero] at this; simpa using this
    · right; right; right
      have hdir : L.direction = Submodule.span ℝ {e₁} :=
        AffineSubspace.direction_mk' ((1/2 : ℝ) • b) (Submodule.span ℝ {e₁})
      exact ⟨hdet_neg1, L, hfinrank_L, bplus, hdir ▸ hbplus_mem, hbplus_zero, hf_on_L⟩

theorem isometry_map_zero_isLinearMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Isometry f) (hf0 : f 0 = 0) :
    IsLinearMap ℝ f := by

  let φ := hf.affineIsometryOfStrictConvexSpace

  have hlin : ∀ x, f x = φ.toAffineMap.linear x := by
    intro x
    have key := congr_fun φ.toAffineMap.decomp x
    simp only [Pi.add_apply] at key
    change f x = φ.toAffineMap.linear x
    have h2 : (φ.toAffineMap : EuclideanSpace ℝ (Fin n) → _) 0 = f 0 := rfl
    rw [h2, hf0, add_zero] at key
    exact key
  exact { map_add := by
            intro x y
            rw [hlin x, hlin y, hlin (x + y), map_add]
          map_smul := by
            intro c x
            rw [hlin x, hlin (c • x), map_smul] }

end Isometries
