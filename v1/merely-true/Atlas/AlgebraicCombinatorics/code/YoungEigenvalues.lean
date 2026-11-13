/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.YoungTableaux
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

set_option autoImplicit false

noncomputable section

namespace YoungEigenvalues

noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma p_mono (n : ℕ) : p n ≤ p (n + 1) := by
  unfold p

  let f : Nat.Partition n → Nat.Partition (n + 1) :=
    fun μ => ⟨1 ::ₘ μ.parts,
      fun {i} hi => by
        rw [Multiset.mem_cons] at hi
        rcases hi with rfl | h
        · omega
        · exact μ.parts_pos h,
      by simp [μ.parts_sum, add_comm]⟩
  apply Fintype.card_le_of_injective f
  intro μ₁ μ₂ h
  have heq : μ₁.parts = μ₂.parts := by
    have := congr_arg Nat.Partition.parts h
    simp only [f] at this
    exact (Multiset.cons_inj_right 1).mp this
  exact Nat.Partition.ext heq

lemma p_le_p {a b : ℕ} (h : a ≤ b) : p a ≤ p b := by
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (p_mono _)

def kerDimDiff (s : ℕ) : ℕ :=
  if s = 0 then p 0 else p s - p (s - 1)

@[simp] lemma kerDimDiff_zero : kerDimDiff 0 = p 0 := by simp [kerDimDiff]

lemma kerDimDiff_pos {s : ℕ} (hs : 1 ≤ s) : kerDimDiff s = p s - p (s - 1) := by
  simp only [kerDimDiff, if_neg (by omega : ¬ s = 0)]

lemma kerDimDiff_sum_eq (n : ℕ) (hn : 1 ≤ n) :
    (Finset.range n).sum kerDimDiff = p (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction m with
  | zero => simp [kerDimDiff]
  | succ k ih =>
    simp only [Nat.succ_sub_one] at ih ⊢
    rw [Finset.sum_range_succ, ih, kerDimDiff_pos (by omega : 1 ≤ k + 1)]
    simp only [Nat.succ_sub_one, Nat.add_sub_cancel]
    exact Nat.add_sub_cancel' (p_mono k)

noncomputable def adjOp₂ {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁) :
    Module.End ℝ (V₁ × V₂) where
  toFun p := (D p.2, U p.1)
  map_add' p q := by simp [map_add]
  map_smul' r p := by simp [map_smul]

noncomputable def eigenspace_adjOp₂_equiv_DU
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
    (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁)
    (μ : ℝ) (hμ : μ ≠ 0) (s : ℝ) (hμs : μ * μ = s) :
    (adjOp₂ U D).eigenspace μ ≃ₗ[ℝ] Module.End.eigenspace (D.comp U) s :=
  LinearEquiv.ofLinear
    { toFun := fun ⟨⟨a, b⟩, hab⟩ => ⟨a, by
        rw [Module.End.mem_eigenspace_iff, LinearMap.comp_apply]
        have h := Module.End.mem_eigenspace_iff.mp hab
        have hDb : D b = μ • a := congr_arg Prod.fst h
        have hUa : U a = μ • b := congr_arg Prod.snd h
        rw [hUa, map_smul, hDb, smul_smul, hμs]⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
    { toFun := fun ⟨a, ha⟩ => ⟨(a, μ⁻¹ • U a), by
        rw [Module.End.mem_eigenspace_iff]
        have hDUa : D (U a) = s • a := Module.End.mem_eigenspace_iff.mp ha
        show adjOp₂ U D (a, μ⁻¹ • U a) = μ • (a, μ⁻¹ • U a)
        simp only [adjOp₂, LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk]
        ext
        · simp only [LinearMap.map_smul, hDUa, smul_smul]
          congr 1; rw [← hμs]; field_simp
        · simp only [smul_smul, mul_inv_cancel₀ hμ, one_smul]⟩
      map_add' := fun ⟨a₁, _⟩ ⟨a₂, _⟩ => by
        apply Subtype.ext; simp [smul_add, map_add]
      map_smul' := fun r ⟨a, _⟩ => by
        apply Subtype.ext; simp [smul_comm r, map_smul] }
    (by ext1 ⟨a, ha⟩; exact Subtype.ext rfl)
    (by ext1 ⟨⟨a, b⟩, hab⟩; apply Subtype.ext
        have hUa : U a = μ • b := congr_arg Prod.snd (Module.End.mem_eigenspace_iff.mp hab)
        show (a, μ⁻¹ • U a) = (a, b)
        rw [hUa, smul_smul, inv_mul_cancel₀ hμ, one_smul])

lemma eigenspace_id_add_eq {W : Type*} [AddCommGroup W] [Module ℝ W]
    (G : Module.End ℝ W) (s : ℝ) :
    Module.End.eigenspace (LinearMap.id + G) s =
      Module.End.eigenspace G (s - 1) := by
  ext w
  simp only [Module.End.mem_eigenspace_iff, LinearMap.add_apply, LinearMap.id_apply]
  constructor
  · intro h
    calc G w = w + G w - w := by abel
      _ = s • w - w := by rw [h]
      _ = (s - 1) • w := by rw [sub_smul, one_smul]
  · intro h
    calc w + G w = w + (s - 1) • w := by rw [h]
      _ = w + (s • w - w) := by rw [sub_smul, one_smul]
      _ = s • w := by abel

noncomputable def eigenspace_comp_comm_nonzero_equiv
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]
    (A : W₁ →ₗ[ℝ] W₂) (B : W₂ →ₗ[ℝ] W₁) (μ : ℝ) (hμ : μ ≠ 0) :
    Module.End.eigenspace (B.comp A) μ ≃ₗ[ℝ]
      Module.End.eigenspace (A.comp B) μ :=
  LinearEquiv.ofLinear
    { toFun := fun ⟨w, hw⟩ => ⟨A w, by
        rw [Module.End.mem_eigenspace_iff]
        have hBAw : B (A w) = μ • w := by
          rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hw
        show (A.comp B) (A w) = μ • A w
        rw [LinearMap.comp_apply, hBAw, map_smul]⟩
      map_add' := fun _ _ => Subtype.ext (map_add A _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul A _ _) }
    { toFun := fun ⟨v, hv⟩ => ⟨μ⁻¹ • B v, by
        rw [Module.End.mem_eigenspace_iff]
        have hABv : A (B v) = μ • v := by
          rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hv
        show (B.comp A) (μ⁻¹ • B v) = μ • (μ⁻¹ • B v)
        rw [LinearMap.comp_apply, map_smul, map_smul, hABv, map_smul,
            smul_smul, smul_smul, inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ]⟩
      map_add' := fun ⟨a₁, _⟩ ⟨a₂, _⟩ => by
        apply Subtype.ext; show μ⁻¹ • B (a₁ + a₂) = μ⁻¹ • B a₁ + μ⁻¹ • B a₂
        rw [map_add, smul_add]
      map_smul' := fun r ⟨a, _⟩ => by
        apply Subtype.ext; show μ⁻¹ • B (r • a) = r • (μ⁻¹ • B a)
        rw [map_smul, smul_comm] }
    (by
      ext1 ⟨v, hv⟩; apply Subtype.ext
      show A (μ⁻¹ • B v) = v
      have hABv : A (B v) = μ • v := by
        rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hv
      rw [map_smul, hABv, smul_smul, inv_mul_cancel₀ hμ, one_smul])
    (by
      ext1 ⟨w, hw⟩; apply Subtype.ext
      show μ⁻¹ • B (A w) = w
      have hBAw : B (A w) = μ • w := by
        rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hw
      rw [hBAw, smul_smul, inv_mul_cancel₀ hμ, one_smul])

lemma DU_eigenspace_dim_from_commutation (j : ℕ) (hj : 2 ≤ j)
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
    (hdim1 : Module.finrank ℝ V₁ = p (j - 1))
    (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁)
    {V₀ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
    (U_prev : V₀ →ₗ[ℝ] V₁) (D_prev : V₁ →ₗ[ℝ] V₀)
    (hcomm : ∀ w : V₁, D (U w) = w + U_prev (D_prev w))
    (hdim0 : Module.finrank ℝ V₀ = p (j - 2))
    (hU_prev_inj : Function.Injective U_prev)
    (hD_prev_surj : Function.Surjective D_prev)


    (hDpUp_eig : ∀ t : ℕ, 1 ≤ t → t ≤ j - 1 →
      Module.finrank ℝ ↥(Module.End.eigenspace (D_prev.comp U_prev) (↑t : ℝ)) =
        kerDimDiff ((j - 1) - t)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥(Module.End.eigenspace (D.comp U) (↑s : ℝ)) =
        kerDimDiff (j - s) := by
  intro s hs hsj

  have hDU_eq : D.comp U = LinearMap.id + U_prev.comp D_prev := by
    ext w; simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, hcomm w]

  have h_shift : Module.End.eigenspace (D.comp U) (↑s : ℝ) =
      Module.End.eigenspace (U_prev.comp D_prev) ((↑s : ℝ) - 1) := by
    rw [hDU_eq]; exact eigenspace_id_add_eq (U_prev.comp D_prev) (↑s : ℝ)
  conv_lhs => rw [h_shift]
  by_cases hs1 : s = 1
  ·
    subst hs1
    have : (↑(1 : ℕ) : ℝ) - 1 = 0 := by norm_num
    rw [this, Module.End.eigenspace_zero]

    have hker : LinearMap.ker (U_prev.comp D_prev) = LinearMap.ker D_prev :=
      LinearMap.ker_comp_of_ker_eq_bot D_prev (LinearMap.ker_eq_bot_of_injective hU_prev_inj)
    conv_lhs => rw [hker]

    have hrnk := D_prev.finrank_range_add_finrank_ker
    have hrange : LinearMap.range D_prev = ⊤ := LinearMap.range_eq_top.mpr hD_prev_surj
    rw [hrange, finrank_top] at hrnk
    rw [hdim0, hdim1] at hrnk
    show Module.finrank ℝ ↥(LinearMap.ker D_prev) = kerDimDiff (j - 1)
    rw [kerDimDiff_pos (by omega)]
    have hjj : j - 1 - 1 = j - 2 := by omega
    rw [hjj]; omega

  ·
    have hs2 : 2 ≤ s := by omega
    have hsm1_pos : (0 : ℝ) < ↑s - 1 := by
      have : (1 : ℕ) < s := by omega
      have : (1 : ℝ) < ↑s := by exact_mod_cast this
      linarith
    have hsm1_ne : (↑s : ℝ) - 1 ≠ 0 := ne_of_gt hsm1_pos

    rw [(eigenspace_comp_comm_nonzero_equiv D_prev U_prev ((↑s : ℝ) - 1) hsm1_ne).finrank_eq]

    have hsm1_nat : (↑s : ℝ) - 1 = (↑(s - 1) : ℝ) := by
      have h1s : 1 ≤ s := by omega
      rw [Nat.cast_sub h1s]; simp
    rw [hsm1_nat]
    rw [hDpUp_eig (s - 1) (by omega) (by omega)]
    have h1 : j - 1 - (s - 1) = j - s := by omega
    rw [h1]

theorem abstract_eigenvalue_multiplicities (j : ℕ) (hj : 2 ≤ j)
    (V₁ V₂ : Type*) [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
    (hdim1 : Module.finrank ℝ V₁ = p (j - 1))
    (hdim2 : Module.finrank ℝ V₂ = p j)
    (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁)
    (hU_inj : Function.Injective U)
    (hD_surj : Function.Surjective D)
    {V₀ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
    (U_prev : V₀ →ₗ[ℝ] V₁) (D_prev : V₁ →ₗ[ℝ] V₀)
    (hcomm : ∀ w : V₁, D (U w) = w + U_prev (D_prev w))
    (hdim0 : Module.finrank ℝ V₀ = p (j - 2))
    (hU_prev_inj : Function.Injective U_prev)
    (hD_prev_surj : Function.Surjective D_prev)
    (hDpUp_eig : ∀ t : ℕ, 1 ≤ t → t ≤ j - 1 →
      Module.finrank ℝ ↥(Module.End.eigenspace (D_prev.comp U_prev) (↑t : ℝ)) =
        kerDimDiff ((j - 1) - t)) :


    Module.finrank ℝ ↥((adjOp₂ U D).eigenspace 0) = p j - p (j - 1) ∧

    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ U D).eigenspace (Real.sqrt ↑s)) =
        kerDimDiff (j - s)) ∧

    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ U D).eigenspace (-(Real.sqrt ↑s))) =
        kerDimDiff (j - s)) ∧

    (p j - p (j - 1) + 2 * (Finset.range j).sum kerDimDiff = p (j - 1) + p j) := by

  have hDU_eig : ∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥(Module.End.eigenspace (D.comp U) (↑s : ℝ)) =
        kerDimDiff (j - s) :=
    DU_eigenspace_dim_from_commutation j hj hdim1 U D U_prev D_prev
      hcomm hdim0 hU_prev_inj hD_prev_surj hDpUp_eig
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Module.End.eigenspace_zero]
    have mem_ker_adj : ∀ (a : V₁) (b : V₂),
        (a, b) ∈ LinearMap.ker (adjOp₂ U D) ↔ D b = 0 ∧ U a = 0 := by
      intro a b
      simp only [LinearMap.mem_ker, adjOp₂, LinearMap.coe_mk, AddHom.coe_mk]
      constructor
      · intro h; exact ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩
      · intro ⟨h1, h2⟩; exact Prod.ext h1 h2
    let fwd : LinearMap.ker D →ₗ[ℝ] LinearMap.ker (adjOp₂ U D) :=
      { toFun := fun x => ⟨(0, x.1), (mem_ker_adj 0 x.1).mpr ⟨LinearMap.mem_ker.mp x.2, map_zero U⟩⟩
        map_add' := fun x y => by
          apply Subtype.ext
          show (0, x.1 + y.1) = ((0 : V₁) + 0, x.1 + y.1)
          simp
        map_smul' := fun r x => by
          apply Subtype.ext
          show (0, r • x.1) = (r • (0 : V₁), r • x.1)
          simp }
    let bwd : LinearMap.ker (adjOp₂ U D) →ₗ[ℝ] LinearMap.ker D :=
      { toFun := fun x => ⟨x.1.2, LinearMap.mem_ker.mpr ((mem_ker_adj x.1.1 x.1.2).mp x.2).1⟩
        map_add' := fun x y => Subtype.ext rfl
        map_smul' := fun r x => Subtype.ext rfl }
    have equiv : LinearMap.ker (adjOp₂ U D) ≃ₗ[ℝ] LinearMap.ker D :=
      LinearEquiv.ofLinear bwd fwd
        (by ext1 x; exact Subtype.ext rfl)
        (by ext1 ⟨⟨a, b⟩, hab⟩
            have hUa : U a = 0 := ((mem_ker_adj a b).mp hab).2
            have ha : a = 0 := hU_inj (by rw [hUa, map_zero])
            subst ha
            rfl)
    rw [equiv.finrank_eq]
    have hrnk := D.finrank_range_add_finrank_ker
    have hrange : LinearMap.range D = ⊤ := LinearMap.range_eq_top.mpr hD_surj
    rw [hrange, finrank_top] at hrnk
    rw [hdim1, hdim2] at hrnk
    omega
  ·
    intro s hs hsj
    have hsqrt_ne : Real.sqrt ↑s ≠ 0 :=
      ne_of_gt (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (by omega)))
    rw [(eigenspace_adjOp₂_equiv_DU U D (Real.sqrt ↑s) hsqrt_ne ↑s
      (Real.mul_self_sqrt (Nat.cast_nonneg s))).finrank_eq]
    exact hDU_eig s hs hsj
  ·
    intro s hs hsj
    have hsqrt_ne : Real.sqrt ↑s ≠ 0 :=
      ne_of_gt (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (by omega)))
    rw [(eigenspace_adjOp₂_equiv_DU U D (-(Real.sqrt ↑s)) (neg_ne_zero.mpr hsqrt_ne) ↑s
      (by rw [neg_mul_neg]; exact Real.mul_self_sqrt (Nat.cast_nonneg s))).finrank_eq]
    exact hDU_eig s hs hsj
  ·
    rw [kerDimDiff_sum_eq j (by omega)]
    have : p (j - 1) ≤ p j := p_le_p (by omega)
    omega

abbrev PartitionSpace (j : ℕ) := Nat.Partition j →₀ ℝ

lemma finrank_partitionSpace (j : ℕ) :
    Module.finrank ℝ (PartitionSpace j) = p j := by
  change Module.finrank ℝ (Nat.Partition j →₀ ℝ) = Fintype.card (Nat.Partition j)
  rw [LinearEquiv.finrank_eq (Finsupp.linearEquivFunOnFinite ℝ ℝ (Nat.Partition j)),
      Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_self,
      smul_eq_mul, mul_one, Finset.card_univ]

theorem young_lattice_eigenvalue_multiplicities (j : ℕ) (hj : 2 ≤ j)
    (U : PartitionSpace (j - 1) →ₗ[ℝ] PartitionSpace j)
    (D : PartitionSpace j →ₗ[ℝ] PartitionSpace (j - 1))
    (hU_inj : Function.Injective U)
    (hD_surj : Function.Surjective D)
    (U_prev : PartitionSpace (j - 2) →ₗ[ℝ] PartitionSpace (j - 1))
    (D_prev : PartitionSpace (j - 1) →ₗ[ℝ] PartitionSpace (j - 2))
    (hcomm : ∀ w, D (U w) = w + U_prev (D_prev w))
    (hU_prev_inj : Function.Injective U_prev)
    (hD_prev_surj : Function.Surjective D_prev)
    (hDpUp_eig : ∀ t : ℕ, 1 ≤ t → t ≤ j - 1 →
      Module.finrank ℝ ↥(Module.End.eigenspace (D_prev.comp U_prev) (↑t : ℝ)) =
        kerDimDiff ((j - 1) - t)) :
    Module.finrank ℝ ↥((adjOp₂ U D).eigenspace 0) = p j - p (j - 1) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ U D).eigenspace (Real.sqrt ↑s)) =
        kerDimDiff (j - s)) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ U D).eigenspace (-(Real.sqrt ↑s))) =
        kerDimDiff (j - s)) ∧
    (p j - p (j - 1) + 2 * (Finset.range j).sum kerDimDiff = p (j - 1) + p j) :=
  abstract_eigenvalue_multiplicities j hj
    (PartitionSpace (j - 1)) (PartitionSpace j)
    (finrank_partitionSpace (j - 1)) (finrank_partitionSpace j)
    U D hU_inj hD_surj
    U_prev D_prev hcomm
    (finrank_partitionSpace (j - 2))
    hU_prev_inj hD_prev_surj hDpUp_eig

structure YoungLatticeOps (i : ℕ) where
  U : PartitionSpace i →ₗ[ℝ] PartitionSpace (i + 1)
  D : PartitionSpace (i + 1) →ₗ[ℝ] PartitionSpace i
  hU_inj : Function.Injective U
  hD_surj : Function.Surjective D

structure YoungLatticeFamily where
  ops : (i : ℕ) → YoungLatticeOps i
  hcomm : ∀ (i : ℕ) (w : PartitionSpace (i + 1)),
    (ops (i + 1)).D ((ops (i + 1)).U w) = w + (ops i).U ((ops i).D w)
  hbase : (ops 0).D.comp (ops 0).U = LinearMap.id

lemma eigenspace_dim_of_id (F : YoungLatticeFamily) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 1 →
      Module.finrank ℝ ↥(Module.End.eigenspace
        ((F.ops 0).D.comp (F.ops 0).U) (↑s : ℝ)) = kerDimDiff (1 - s) := by
  intro s hs1 hs2
  have hs_eq : s = 1 := by omega
  subst hs_eq
  simp only [Nat.sub_self, kerDimDiff_zero]
  rw [F.hbase]
  have h1eq : (↑(1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
  rw [h1eq]
  have : Module.End.eigenspace (LinearMap.id : Module.End ℝ (PartitionSpace 0)) (1 : ℝ) = ⊤ := by
    ext w
    simp only [Module.End.mem_eigenspace_iff, LinearMap.id_apply, one_smul, Submodule.mem_top,
               iff_true]
  rw [this, finrank_top, finrank_partitionSpace]

lemma DU_eigenspace_dim_induction (F : YoungLatticeFamily) :
    ∀ k : ℕ, ∀ s : ℕ, 1 ≤ s → s ≤ k + 2 →
      Module.finrank ℝ ↥(Module.End.eigenspace
        ((F.ops (k + 1)).D.comp (F.ops (k + 1)).U) (↑s : ℝ)) =
          kerDimDiff (k + 2 - s) := by
  intro k
  induction k with
  | zero =>
    intro s hs hsle
    have result := DU_eigenspace_dim_from_commutation 2 (by omega)
      (finrank_partitionSpace 1)
      (F.ops 1).U (F.ops 1).D
      (F.ops 0).U (F.ops 0).D
      (F.hcomm 0)
      (finrank_partitionSpace 0)
      (F.ops 0).hU_inj (F.ops 0).hD_surj
      (eigenspace_dim_of_id F)
    exact result s hs hsle
  | succ n ih =>
    intro s hs hsle
    exact DU_eigenspace_dim_from_commutation (n + 3) (by omega)
      (finrank_partitionSpace (n + 2))
      (F.ops (n + 2)).U (F.ops (n + 2)).D
      (F.ops (n + 1)).U (F.ops (n + 1)).D
      (F.hcomm (n + 1))
      (finrank_partitionSpace (n + 1))
      (F.ops (n + 1)).hU_inj (F.ops (n + 1)).hD_surj
      (by intro t ht1 ht2
          exact ih t ht1 (by omega))
      s hs hsle

lemma DU_eigenspace_dim_all_levels (F : YoungLatticeFamily) (k : ℕ) :
    ∀ s : ℕ, 1 ≤ s → s ≤ k + 1 →
      Module.finrank ℝ ↥(Module.End.eigenspace
        ((F.ops k).D.comp (F.ops k).U) (↑s : ℝ)) =
          kerDimDiff (k + 1 - s) := by
  cases k with
  | zero => exact eigenspace_dim_of_id F
  | succ m => exact DU_eigenspace_dim_induction F m

theorem young_lattice_eigenvalues_closed (F : YoungLatticeFamily) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℝ ↥((adjOp₂ (F.ops (j - 1)).U (F.ops (j - 1)).D).eigenspace 0) =
      p j - p (j - 1) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ (F.ops (j - 1)).U (F.ops (j - 1)).D).eigenspace
        (Real.sqrt ↑s)) = kerDimDiff (j - s)) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ j →
      Module.finrank ℝ ↥((adjOp₂ (F.ops (j - 1)).U (F.ops (j - 1)).D).eigenspace
        (-(Real.sqrt ↑s))) = kerDimDiff (j - s)) ∧
    (p j - p (j - 1) + 2 * (Finset.range j).sum kerDimDiff = p (j - 1) + p j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  cases n with
  | zero =>

    simp only [Nat.add_sub_cancel]
    have hDU_id := F.hbase
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Module.End.eigenspace_zero]
      have mem_ker_adj : ∀ (a : PartitionSpace 0) (b : PartitionSpace 1),
          (a, b) ∈ LinearMap.ker (adjOp₂ (F.ops 0).U (F.ops 0).D) ↔
            (F.ops 0).D b = 0 ∧ (F.ops 0).U a = 0 := by
        intro a b
        simp only [LinearMap.mem_ker, adjOp₂, LinearMap.coe_mk, AddHom.coe_mk]
        constructor
        · intro h; exact ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩
        · intro ⟨h1, h2⟩; exact Prod.ext h1 h2
      let fwd : LinearMap.ker (F.ops 0).D →ₗ[ℝ]
          LinearMap.ker (adjOp₂ (F.ops 0).U (F.ops 0).D) :=
        { toFun := fun x => ⟨(0, x.1), (mem_ker_adj 0 x.1).mpr
            ⟨LinearMap.mem_ker.mp x.2, map_zero _⟩⟩
          map_add' := fun x y => by apply Subtype.ext; simp
          map_smul' := fun r x => by apply Subtype.ext; simp }
      let bwd : LinearMap.ker (adjOp₂ (F.ops 0).U (F.ops 0).D) →ₗ[ℝ]
          LinearMap.ker (F.ops 0).D :=
        { toFun := fun x => ⟨x.1.2, LinearMap.mem_ker.mpr
            ((mem_ker_adj x.1.1 x.1.2).mp x.2).1⟩
          map_add' := fun _ _ => Subtype.ext rfl
          map_smul' := fun _ _ => Subtype.ext rfl }
      have equiv : LinearMap.ker (adjOp₂ (F.ops 0).U (F.ops 0).D) ≃ₗ[ℝ]
          LinearMap.ker (F.ops 0).D :=
        LinearEquiv.ofLinear bwd fwd
          (by ext1 x; exact Subtype.ext rfl)
          (by ext1 ⟨⟨a, b⟩, hab⟩
              have hUa := ((mem_ker_adj a b).mp hab).2
              have ha : a = 0 := (F.ops 0).hU_inj (by rw [hUa, map_zero])
              subst ha; rfl)
      rw [equiv.finrank_eq]
      have hrnk := (F.ops 0).D.finrank_range_add_finrank_ker
      have hrange : LinearMap.range (F.ops 0).D = ⊤ :=
        LinearMap.range_eq_top.mpr (F.ops 0).hD_surj
      rw [hrange, finrank_top, finrank_partitionSpace, finrank_partitionSpace] at hrnk
      omega
    ·
      intro s hs1 hs2
      have hs_eq : s = 1 := by omega
      subst hs_eq
      simp only [Nat.sub_self, kerDimDiff_zero]
      have hsqrt_ne : Real.sqrt ↑(1 : ℕ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < ↑(1 : ℕ)))
      rw [(eigenspace_adjOp₂_equiv_DU (F.ops 0).U (F.ops 0).D
        (Real.sqrt ↑(1 : ℕ)) hsqrt_ne ↑(1 : ℕ)
        (Real.mul_self_sqrt (Nat.cast_nonneg 1))).finrank_eq]
      rw [hDU_id]
      have : Module.End.eigenspace (LinearMap.id : Module.End ℝ (PartitionSpace 0))
          ((1 : ℕ) : ℝ) = ⊤ := by
        ext w
        simp only [Module.End.mem_eigenspace_iff, LinearMap.id_apply, Nat.cast_one,
                   one_smul, Submodule.mem_top, iff_true]
      rw [this, finrank_top, finrank_partitionSpace]
    ·
      intro s hs1 hs2
      have hs_eq : s = 1 := by omega
      subst hs_eq
      simp only [Nat.sub_self, kerDimDiff_zero]
      have hsqrt_ne : Real.sqrt ↑(1 : ℕ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < ↑(1 : ℕ)))
      rw [(eigenspace_adjOp₂_equiv_DU (F.ops 0).U (F.ops 0).D
        (-(Real.sqrt ↑(1 : ℕ))) (neg_ne_zero.mpr hsqrt_ne) ↑(1 : ℕ)
        (by rw [neg_mul_neg]; exact Real.mul_self_sqrt (Nat.cast_nonneg 1))).finrank_eq]
      rw [hDU_id]
      have : Module.End.eigenspace (LinearMap.id : Module.End ℝ (PartitionSpace 0))
          ((1 : ℕ) : ℝ) = ⊤ := by
        ext w
        simp only [Module.End.mem_eigenspace_iff, LinearMap.id_apply, Nat.cast_one,
                   one_smul, Submodule.mem_top, iff_true]
      rw [this, finrank_top, finrank_partitionSpace]
    ·
      simp only [Nat.zero_add, Nat.add_sub_cancel]
      rw [kerDimDiff_sum_eq 1 le_rfl]
      simp only [Nat.sub_self, kerDimDiff_zero]
      have : p 0 ≤ p 1 := p_le_p (by omega)
      omega

  | succ m =>

    cases m with
    | zero =>
      exact young_lattice_eigenvalue_multiplicities 2 (by omega)
        (F.ops 1).U (F.ops 1).D (F.ops 1).hU_inj (F.ops 1).hD_surj
        (F.ops 0).U (F.ops 0).D (F.hcomm 0) (F.ops 0).hU_inj (F.ops 0).hD_surj
        (DU_eigenspace_dim_all_levels F 0)
    | succ k =>
      exact young_lattice_eigenvalue_multiplicities (k + 3) (by omega)
        (F.ops (k + 2)).U (F.ops (k + 2)).D
        (F.ops (k + 2)).hU_inj (F.ops (k + 2)).hD_surj
        (F.ops (k + 1)).U (F.ops (k + 1)).D
        (F.hcomm (k + 1)) (F.ops (k + 1)).hU_inj (F.ops (k + 1)).hD_surj
        (DU_eigenspace_dim_all_levels F (k + 1))

end YoungEigenvalues
end
