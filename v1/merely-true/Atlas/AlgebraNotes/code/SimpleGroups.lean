/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SimpleGroups

open Matrix

@[reducible] def lieAlgebraMatrix (n : ℕ) :
    LieAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := inferInstance

theorem lie_bracket_def {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (A B : Matrix n n R) : ⁅A, B⁆ = A * B - B * A :=
  Ring.lie_def A B

noncomputable def lieAlgebraSet (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∀ t : ℝ, ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
    (u : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (t • A) ∧ u ∈ G}

noncomputable def lieAlgebraSetPath (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∃ (ε : ℝ) (_ : ε > 0) (f : ℝ → Matrix (Fin m) (Fin m) ℝ),
    DifferentiableAt ℝ f 0 ∧
    f 0 = 1 ∧
    deriv f 0 = A ∧
    (∀ t : ℝ, |t| < ε → ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (u : Matrix (Fin m) (Fin m) ℝ) = f t ∧ u ∈ G)}

open DualNumber in
noncomputable def lieAlgebraSetDual (m : ℕ)
    (P : Matrix (Fin m) (Fin m) ℝ[ε] → Prop) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | P ((1 : Matrix (Fin m) (Fin m) ℝ[ε]) + A.map (TrivSqZeroExt.inr))}



structure IsOneParameterGroup (m : ℕ) (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) : Prop where
  map_zero : φ 0 = 1
  map_add : ∀ s t : ℝ, φ (s + t) = φ s * φ t
  differentiable : Differentiable ℝ φ

section OneParamSubgroupTheorem
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem one_param_subgroup_form (m : ℕ)
    (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) (hφ : IsOneParameterGroup m φ) :
    ∃! A : Matrix (Fin m) (Fin m) ℂ,
      ∀ t : ℝ, φ t = NormedSpace.exp ((↑t : ℂ) • A) := by

  have exp_hd : ∀ (B : Matrix (Fin m) (Fin m) ℂ) (s : ℝ),
      HasDerivAt (fun u : ℝ => NormedSpace.exp ((↑u : ℂ) • B))
        (NormedSpace.exp ((↑s : ℂ) • B) * B) s := by
    intro B s
    have ist : IsScalarTower ℝ ℂ (Matrix (Fin m) (Fin m) ℂ) := inferInstance
    have h2 := @HasDerivAt.scomp ℝ _ (Matrix (Fin m) (Fin m) ℂ) _ _ s ℂ _ _ _ ist _ _ _ _
      (hasDerivAt_exp_smul_const B (↑s : ℂ)) Complex.ofRealCLM.hasDerivAt
    convert h2 using 1; simp

  set A := deriv φ 0

  have hφ_ode : ∀ s : ℝ, deriv φ s = A * φ s := by
    intro s
    have h : (fun u => φ (u + s)) = (fun u => φ u * φ s) := funext (fun u => hφ.map_add u s)
    calc deriv φ s = deriv φ (0 + s) := by ring_nf
      _ = deriv (fun u => φ (u + s)) 0 := (deriv_comp_add_const φ s 0).symm
      _ = deriv (fun u => φ u * φ s) 0 := by rw [h]
      _ = deriv φ 0 * φ s := (hφ.differentiable.differentiableAt.hasDerivAt.mul_const (φ s)).deriv

  set g : ℝ → Matrix (Fin m) (Fin m) ℂ := fun s => φ s - NormedSpace.exp ((↑s : ℂ) • A)
  have hg_diff : Differentiable ℝ g :=
    hφ.differentiable.sub (fun s => (exp_hd A s).differentiableAt)
  have hg_zero : g 0 = 0 := by simp [g, hφ.map_zero, NormedSpace.exp_zero]
  have hg_ode : ∀ s : ℝ, deriv g s = A * g s := by
    intro s
    have hd := (hφ.differentiable s).hasDerivAt.sub (exp_hd A s)
    have heq : deriv g s = deriv φ s - NormedSpace.exp ((↑s : ℂ) • A) * A := hd.deriv
    rw [heq, hφ_ode s, ((Commute.refl A).smul_left (↑s : ℂ)).exp_left.eq, mul_sub]

  have hg_eq_zero : ∀ t : ℝ, g t = 0 := by
    intro t
    by_cases ht : 0 ≤ t
    ·
      exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
        hg_diff.continuous.continuousOn
        (fun x _ => (hg_diff x).hasDerivAt.hasDerivWithinAt)
        hg_zero
        (fun x _ => by rw [hg_ode x]; exact norm_mul_le A (g x))
        t ⟨ht, le_refl t⟩
    ·
      have ht' : t < 0 := not_le.mp ht
      have hh_diff : Differentiable ℝ (fun s => g (-s)) := hg_diff.comp differentiable_neg
      have hmem : -t ∈ Set.Icc 0 (-t) := ⟨by linarith, le_refl _⟩
      have h_eq := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
        hh_diff.continuous.continuousOn
        (fun x _ => (hh_diff x).hasDerivAt.hasDerivWithinAt)
        (show (fun s => g (-s)) 0 = 0 by simp [hg_zero])
        (fun x _ => by
          show ‖deriv (fun s => g (-s)) x‖ ≤ ‖A‖ * ‖g (-x)‖
          rw [deriv_comp_neg g x, norm_neg, hg_ode (-x)]
          exact norm_mul_le A (g (-x)))
        (-t) hmem
      simpa using h_eq
  refine ⟨A, ?_, ?_⟩
  ·
    intro t; exact sub_eq_zero.mp (hg_eq_zero t)
  ·
    intro B hB
    have heq : (fun s : ℝ => φ s) = (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) :=
      funext hB
    have hB_deriv : deriv (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) 0 = B := by
      rw [(exp_hd B 0).deriv]; simp [NormedSpace.exp_zero]
    calc B = deriv (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) 0 := hB_deriv.symm
      _ = deriv (fun s : ℝ => φ s) 0 := by rw [← heq]
      _ = A := rfl

end OneParamSubgroupTheorem


theorem su2_matrix_form (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ (α β : ℂ), M = !![α, β; -starRingEnd ℂ β, starRingEnd ℂ α] ∧
      Complex.normSq α + Complex.normSq β = 1 := by
  set α := M 0 0
  set β := M 0 1
  have hdet : M.det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hunit : star M * M = 1 := hU.1.1
  have hstarM : star M = M⁻¹ := (Matrix.inv_eq_left_inv hunit).symm
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
  have hstarAdj := hstarM.trans hinv
  refine ⟨α, β, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [α, β]
    ·
      have h := congr_fun (congr_fun hstarAdj 0) 1
      simp [Matrix.adjugate_fin_two] at h
      have := congr_arg (starRingEnd ℂ) h
      simp [map_neg] at this
      exact this
    ·
      have h := congr_fun (congr_fun hstarAdj 0) 0
      simp [Matrix.adjugate_fin_two] at h
      exact h.symm
  ·
    have hunit2 := hU.1.2
    have h00 := congr_fun (congr_fun hunit2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    rw [Complex.mul_conj, Complex.mul_conj] at h00
    exact_mod_cast h00

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

lemma D_mem_SU2 : !![Complex.I, (0:ℂ); 0, -Complex.I] ∈ SU2 := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | left; (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | right; (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two, Complex.I]
    apply Complex.ext <;> simp

lemma W_mem_SU2 : !![(0:ℂ), 1; -1, 0] ∈ SU2 := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two]

lemma su2_center_mem_iff (M : ↥SU2) :
    M ∈ Subgroup.center ↥SU2 ↔
    (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (M : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  constructor
  · intro hM
    rw [Subgroup.mem_center_iff] at hM
    have comm_of (g_val : Matrix (Fin 2) (Fin 2) ℂ) (g_mem : g_val ∈ SU2) :
        (M : Matrix (Fin 2) (Fin 2) ℂ) * g_val = g_val * (M : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := hM ⟨g_val, g_mem⟩
      have hv := congr_arg Subtype.val h
      simp only [Submonoid.coe_mul] at hv
      exact hv.symm

    have hDcomm := comm_of _ D_mem_SU2

    have hM01 : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have h := congr_fun (congr_fun hDcomm 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      have h1 : Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
        have heq : -(Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) =
            Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
          rw [mul_comm ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)] at h; exact h
        have h2 : (2 : ℂ) * (Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0 := by
          linear_combination -heq
        exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
      exact (mul_eq_zero.mp h1).resolve_left Complex.I_ne_zero

    have hM10 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have h := congr_fun (congr_fun hDcomm 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      rw [mul_comm Complex.I ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0)] at h
      have h2 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Complex.I = 0 := by
        have : (2 : ℂ) * ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Complex.I) = 0 := by
          linear_combination h
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      exact (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero

    have hWcomm := comm_of _ W_mem_SU2
    have hdiag : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
      have h := congr_fun (congr_fun hWcomm 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      exact h

    have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      have := M.2.2; simp [MonoidHom.mem_mker] at this; exact this
    rw [Matrix.det_fin_two] at hdet
    rw [hM01, hM10] at hdet
    simp at hdet
    rw [hdiag] at hdet
    have ha := mul_self_eq_one_iff.mp hdet
    rcases ha with ha1 | ha_neg1
    · left
      ext i j; fin_cases i <;> fin_cases j <;> simp [hM01, hM10, hdiag, ha1]
    · right
      ext i j; fin_cases i <;> fin_cases j <;> simp [hM01, hM10, hdiag, ha_neg1]
  · intro hM_eq
    rw [Subgroup.mem_center_iff]
    intro g
    ext1
    simp only [Submonoid.coe_mul]
    rcases hM_eq with h1 | h_neg1
    · simp [h1]
    · simp [h_neg1]

lemma su2_trace_real (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 := by
  rw [Matrix.trace_fin_two]
  have hU := M.2
  have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hunit : star (M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 := hU.1.1
  have hstarM : star (M : Matrix (Fin 2) (Fin 2) ℂ) = (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
    (Matrix.inv_eq_left_inv hunit).symm
  have hinv : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
  have hstarAdj := hstarM.trans hinv
  have h00 := congr_fun (congr_fun hstarAdj 0) 0
  simp [Matrix.adjugate_fin_two] at h00
  rw [show (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (starRingEnd ℂ) ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
    from by rw [← h00]]
  rw [Complex.add_conj]
  simp

lemma su2_trace_bound (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  rw [Matrix.trace_fin_two]
  have hU := M.2
  have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hstarAdj : star (M : Matrix (Fin 2) (Fin 2) ℂ) = (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    have hunit : star (M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 := hU.1.1
    have hstarM : star (M : Matrix (Fin 2) (Fin 2) ℂ) = (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
      (Matrix.inv_eq_left_inv hunit).symm
    have hinv : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
      rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
    exact hstarM.trans hinv
  have h00 := congr_fun (congr_fun hstarAdj 0) 0
  simp [Matrix.adjugate_fin_two] at h00
  rw [show (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (starRingEnd ℂ) ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
    from by rw [← h00]]
  rw [Complex.add_conj]
  simp [Real.norm_eq_abs]
  have hunit2 := hU.1.2
  have h00' := congr_fun (congr_fun hunit2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00'
  rw [Complex.mul_conj, Complex.mul_conj] at h00'
  have h00_real : (Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) : ℝ) +
    (Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) : ℝ) = 1 := by
    exact_mod_cast h00'
  have hnsq : Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ≤ 1 := by
    linarith [Complex.normSq_nonneg ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)]
  have hre_sq : ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ≤ 1 ^ 2 := by
    calc ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2
        ≤ ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 +
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 := by
          linarith [sq_nonneg ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im]
      _ = Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
          rw [Complex.normSq_apply]; ring
      _ ≤ 1 := hnsq
      _ = 1 ^ 2 := by ring
  exact abs_le_of_sq_le_sq hre_sq (by norm_num)

noncomputable def diagRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (↑θ * Complex.I), (0:ℂ); 0, Complex.exp (-(↑θ * Complex.I))]

lemma diagRotation_add (θ₁ θ₂ : ℝ) :
    diagRotation θ₁ * diagRotation θ₂ = diagRotation (θ₁ + θ₂) := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  · ring_nf
  · ring_nf

lemma diagRotation_zero : diagRotation 0 = 1 := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
lemma diagRotation_mem_SU2 (θ : ℝ) : diagRotation θ ∈ SU2 := by
  simp only [diagRotation, Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  have hconj1 : starRingEnd ℂ (Complex.exp (↑θ * Complex.I)) =
      Complex.exp (-(↑θ * Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj2 : starRingEnd ℂ (Complex.exp (-(↑θ * Complex.I))) =
      Complex.exp (↑θ * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj_struct : ∀ z : ℂ, ({ re := z.re, im := -z.im } : ℂ) = starRingEnd ℂ z := by
    intro z; apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_mul, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · simp [Matrix.det_fin_two, ← Complex.exp_add]

noncomputable def longitudeI : Subgroup SU2 where
  carrier := {M | ∃ θ : ℝ, M.val = diagRotation θ}
  mul_mem' := by
    intro a b ⟨θ₁, hθ₁⟩ ⟨θ₂, hθ₂⟩
    exact ⟨θ₁ + θ₂, by
      change (a * b).val = diagRotation (θ₁ + θ₂)
      change a.val * b.val = diagRotation (θ₁ + θ₂)
      rw [hθ₁, hθ₂, diagRotation_add]⟩
  one_mem' := ⟨0, by show (1 : SU2).val = diagRotation 0; simp [diagRotation_zero]⟩
  inv_mem' := by
    intro a ⟨θ, hθ⟩
    refine ⟨-θ, ?_⟩
    have hinv : a⁻¹ = ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ := by
      have h : ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ * a = 1 := by
        ext1
        show diagRotation (-θ) * a.val = 1
        rw [hθ, diagRotation_add]; simp [diagRotation_zero]
      exact (mul_eq_one_iff_eq_inv.mp h).symm
    show a⁻¹.val = diagRotation (-θ)
    rw [hinv]

lemma diagRotation_periodic (θ : ℝ) (n : ℤ) :
    diagRotation (θ + n * (2 * Real.pi)) = diagRotation θ := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp
  · have h : (↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I =
        ↑θ * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · have h : -((↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I) =
        -(↑θ * Complex.I) + (-(↑n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add]
    rw [show -(↑n : ℂ) * (2 * ↑Real.pi * Complex.I) = ↑(-n) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

noncomputable def diagRotationToLongI (θ : ℝ) : longitudeI :=
  ⟨⟨diagRotation θ, diagRotation_mem_SU2 θ⟩, ⟨θ, rfl⟩⟩

lemma diagRotationToLongI_periodic (a b : ℝ)
    (h : @Setoid.r _ (QuotientAddGroup.leftRel (AddSubgroup.zmultiples (2 * Real.pi))) a b) :
    diagRotationToLongI a = diagRotationToLongI b := by
  simp only [QuotientAddGroup.leftRel_apply] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  simp only [diagRotationToLongI]
  ext1; ext1
  show diagRotation a = diagRotation b
  have hba : b = a + n * (2 * Real.pi) := by
    have := hn; simp [zsmul_eq_mul] at this; linarith
  rw [hba, diagRotation_periodic]

noncomputable def longitudeMap : Multiplicative (AddCircle (2 * Real.pi)) →* longitudeI where
  toFun x := Quotient.lift diagRotationToLongI
    diagRotationToLongI_periodic (Multiplicative.toAdd x)
  map_one' := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (0 : AddCircle (2 * Real.pi)) = 1
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (QuotientAddGroup.mk 0) = 1
    simp only [Quotient.lift_mk, diagRotationToLongI]
    ext1; ext1
    exact diagRotation_zero
  map_mul' x y := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd x) *
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd y)
    induction Multiplicative.toAdd x using Quotient.inductionOn with
    | h a =>
      induction Multiplicative.toAdd y using Quotient.inductionOn with
      | h b =>
        show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk a + QuotientAddGroup.mk b) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        change Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk (a + b)) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        simp only [Quotient.lift_mk, diagRotationToLongI]
        ext1; ext1
        exact (diagRotation_add a b).symm







set_option maxHeartbeats 800000 in
theorem su2_conj_to_diag (A : ↥SU2) :
    ∃ (D : ↥SU2), (∃ z : ℂ, z * starRingEnd ℂ z = 1 ∧
      (D : Matrix (Fin 2) (Fin 2) ℂ) = !![z, (0:ℂ); 0, starRingEnd ℂ z]) ∧ IsConj A D := by
  obtain ⟨α, β, hA, hnorm⟩ := su2_matrix_form A.val A.2
  by_cases hβ : β = 0
  ·
    have hα_norm : Complex.normSq α = 1 := by simp [hβ] at hnorm; exact hnorm
    have hz : α * starRingEnd ℂ α = 1 := by
      rw [Complex.mul_conj]; exact_mod_cast hα_norm
    have hA_diag : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![α, (0:ℂ); 0, starRingEnd ℂ α] := by
      rw [hA, hβ]; simp
    exact ⟨A, ⟨α, hz, hA_diag⟩, IsConj.refl A⟩
  ·
    have hβ_pos : Complex.normSq β > 0 := Complex.normSq_pos.mpr hβ
    have hα_lt : Complex.normSq α < 1 := by linarith
    have h_re_lt : α.re ^ 2 < 1 := by
      calc α.re ^ 2 ≤ Complex.normSq α := by
            rw [Complex.normSq_apply]; linarith [sq_nonneg α.im]
        _ < 1 := hα_lt
    set s := Real.sqrt (1 - α.re ^ 2)
    have hs_pos : s > 0 := Real.sqrt_pos.mpr (by linarith)
    have hs_sq : s ^ 2 = 1 - α.re ^ 2 := Real.sq_sqrt (by linarith)

    set z : ℂ := ⟨α.re, s⟩
    have hz : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj]; apply Complex.ext
      · simp [Complex.normSq_apply]; nlinarith [hs_sq]
      · simp
    have hz' : (starRingEnd ℂ) z * z = 1 := by rw [mul_comm]; exact hz

    set D_val : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, starRingEnd ℂ z]
    have hD_mem : D_val ∈ SU2 := by
      simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [D_val, z, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map]
        · exact hz'
        · left; rfl
        · left; rfl
        · exact hz
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [D_val, z, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map]
        · exact hz
        · right; rfl
        · right; rfl
        · exact hz'
      · simp [D_val, z, det_fin_two]; linear_combination hz
    set D : ↥SU2 := ⟨D_val, hD_mem⟩

    have hN_pos_r : Complex.normSq β + (s - α.im) ^ 2 > 0 := by
      linarith [Complex.normSq_nonneg β, sq_nonneg (s - α.im)]
    set N := Real.sqrt (Complex.normSq β + (s - α.im) ^ 2)
    have hN_pos : N > 0 := Real.sqrt_pos.mpr hN_pos_r
    have hN_sq : N ^ 2 = Complex.normSq β + (s - α.im) ^ 2 := Real.sq_sqrt (by linarith)
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos

    set p1 : ℂ := β / (↑N : ℂ)
    set p2 : ℂ := ⟨0, (s - α.im) / N⟩
    have hP_norm : Complex.normSq p1 + Complex.normSq p2 = 1 := by
      simp only [p1, p2, Complex.normSq_apply, Complex.div_ofReal_re, Complex.div_ofReal_im]
      have hN_sq' : N * N = Complex.normSq β + (s - α.im) ^ 2 := by nlinarith [hN_sq]
      field_simp
      nlinarith [Complex.normSq_apply β, sq_nonneg β.re, sq_nonneg β.im]
    set P_val : Matrix (Fin 2) (Fin 2) ℂ := !![p1, p2; -starRingEnd ℂ p2, starRingEnd ℂ p1]
    have hP_mem : P_val ∈ SU2 := by
      simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
      have hpq : p1 * (starRingEnd ℂ) p1 + p2 * (starRingEnd ℂ) p2 = 1 := by
        rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast hP_norm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [P_val, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
        (apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hpq ⊢ <;>
         nlinarith [congr_arg Complex.re hpq, congr_arg Complex.im hpq,
                    Complex.normSq_apply p1, Complex.normSq_apply p2])
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [P_val, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
        (apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hpq ⊢ <;>
         nlinarith [congr_arg Complex.re hpq, congr_arg Complex.im hpq,
                    Complex.normSq_apply p1, Complex.normSq_apply p2])
      · simp [P_val, det_fin_two]
        linear_combination hpq

    set P : ↥SU2 := ⟨P_val, hP_mem⟩

    refine ⟨D, ⟨z, hz, rfl⟩, ?_⟩
    rw [isConj_iff]
    refine ⟨P⁻¹, ?_⟩
    apply Subtype.ext
    simp only [Submonoid.coe_mul]
    have hPinv_val : (P⁻¹ : ↥SU2).val = P.val⁻¹ := by
      symm; apply Matrix.inv_eq_left_inv
      have h' := congr_arg Subtype.val (show (P⁻¹ * P : ↥SU2) = 1 from inv_mul_cancel P)
      simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'; exact h'
    have hPinvinv : ((P⁻¹)⁻¹ : ↥SU2).val = P.val := by rw [inv_inv]
    rw [hPinv_val, hPinvinv]
    have hPdet : P.val.det = 1 := by have := P.2.2; simp [MonoidHom.mem_mker] at this; exact this
    have hPunit : IsUnit P.val.det := by rw [hPdet]; exact isUnit_one
    have hPinv_mul : P.val⁻¹ * P.val = 1 := Matrix.nonsing_inv_mul P.val hPunit

    have hnorm_re : α.re ^ 2 + α.im ^ 2 + β.re ^ 2 + β.im ^ 2 = 1 := by
      have := hnorm; rw [Complex.normSq_apply, Complex.normSq_apply] at this; linarith
    have hAP_eq : A.val * P.val = P.val * D.val := by
      rw [show A.val = !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] from hA]
      show !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] *
        !![p1, p2; -(starRingEnd ℂ) p2, (starRingEnd ℂ) p1] =
        !![p1, p2; -(starRingEnd ℂ) p2, (starRingEnd ℂ) p1] * !![z, 0; 0, (starRingEnd ℂ) z]
      ext i j; fin_cases i <;> fin_cases j <;>
      simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one] <;>
      (apply Complex.ext <;> simp [p1, p2, z, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
       field_simp <;> nlinarith [hnorm_re, hs_sq, sq_nonneg α.re, sq_nonneg α.im,
                                  sq_nonneg β.re, sq_nonneg β.im, sq_nonneg s,
                                  sq_nonneg N, sq_nonneg (s - α.im)])
    calc P.val⁻¹ * A.val * P.val
        = P.val⁻¹ * (A.val * P.val) := by rw [Matrix.mul_assoc]
      _ = P.val⁻¹ * (P.val * D.val) := by rw [hAP_eq]
      _ = (P.val⁻¹ * P.val) * D.val := by rw [Matrix.mul_assoc]
      _ = 1 * D.val := by rw [hPinv_mul]
      _ = D.val := by rw [Matrix.one_mul]

lemma su2_trace_conj_inv (P A : ↥SU2) :
    trace (P * A * P⁻¹ : ↥SU2).val = trace A.val := by
  have hval : (P * A * P⁻¹ : ↥SU2).val = P.val * A.val * (P⁻¹ : ↥SU2).val := by
    simp [Submonoid.coe_mul]
  have hinv : (P⁻¹ : ↥SU2).val = P.val⁻¹ := by
    symm; apply Matrix.inv_eq_left_inv
    have h' := congr_arg Subtype.val (show (P⁻¹ * P : ↥SU2) = 1 from inv_mul_cancel P)
    simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'
    exact h'
  rw [hval, hinv]
  have hunit : IsUnit P.val := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : P.val.det = 1 := by
      have := P.2.2; simp [MonoidHom.mem_mker] at this; exact this
    rw [hdet]; exact isUnit_one
  exact trace_conj hunit A.val

lemma su2_diag_conj_of_trace (D₁ D₂ : ↥SU2)
    (z₁ z₂ : ℂ) (hz₁ : z₁ * starRingEnd ℂ z₁ = 1) (hz₂ : z₂ * starRingEnd ℂ z₂ = 1)
    (hD₁ : (D₁ : Matrix (Fin 2) (Fin 2) ℂ) = !![z₁, (0:ℂ); 0, starRingEnd ℂ z₁])
    (hD₂ : (D₂ : Matrix (Fin 2) (Fin 2) ℂ) = !![z₂, (0:ℂ); 0, starRingEnd ℂ z₂])
    (htrace : trace (D₁ : Matrix (Fin 2) (Fin 2) ℂ) = trace (D₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    IsConj D₁ D₂ := by
  have ht1 : trace (D₁ : Matrix (Fin 2) (Fin 2) ℂ) = z₁ + starRingEnd ℂ z₁ := by
    rw [hD₁]; simp [trace_fin_two]
  have ht2 : trace (D₂ : Matrix (Fin 2) (Fin 2) ℂ) = z₂ + starRingEnd ℂ z₂ := by
    rw [hD₂]; simp [trace_fin_two]
  have hsum : z₁ + starRingEnd ℂ z₁ = z₂ + starRingEnd ℂ z₂ := by
    rw [← ht1, ← ht2]; exact htrace
  have hre : z₁.re = z₂.re := by
    have h := congr_arg Complex.re hsum
    simp [Complex.add_re, Complex.conj_re] at h; linarith
  have him_sq : z₁.im * z₁.im = z₂.im * z₂.im := by
    have h1' := congr_arg Complex.re hz₁; have h2' := congr_arg Complex.re hz₂
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1' h2'
    have h3 : z₁.re * z₁.re = z₂.re * z₂.re := by rw [hre]
    linarith
  rcases mul_self_eq_mul_self_iff.mp him_sq with him_eq | him_neg
  ·
    have heq : z₁ = z₂ := Complex.ext hre him_eq
    have hD_eq : D₁ = D₂ := by ext1; rw [hD₁, hD₂, heq]
    rw [hD_eq]

  ·
    have hconj : z₁ = starRingEnd ℂ z₂ := by
      simp [Complex.ext_iff, Complex.conj_re, Complex.conj_im, hre, him_neg]
    let W : ↥SU2 := ⟨!![(0:ℂ), 1; -1, 0], W_mem_SU2⟩
    rw [isConj_iff]
    refine ⟨W, ?_⟩
    ext1
    have hW_val : (W : Matrix (Fin 2) (Fin 2) ℂ) = !![(0:ℂ), 1; -1, 0] := rfl
    have hWinv_val : (W⁻¹ : ↥SU2).val = (!![(0:ℂ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
      have hinv : (W⁻¹ : ↥SU2).val = (W.val)⁻¹ := by
        symm; apply Matrix.inv_eq_left_inv
        have h' := congr_arg Subtype.val (show (W⁻¹ * W : ↥SU2) = 1 from inv_mul_cancel W)
        simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'; exact h'
      rw [hinv]
    simp only [Submonoid.coe_mul, hW_val, hD₁, hD₂, hconj, hWinv_val]
    simp [inv_def, adjugate_fin_two, det_fin_two]

theorem su2_conj_of_trace_eq (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) =
         Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℂ)) :
    IsConj A B := by
  obtain ⟨D_A, ⟨z_A, hz_A, hD_A⟩, hconj_A⟩ := su2_conj_to_diag A
  obtain ⟨D_B, ⟨z_B, hz_B, hD_B⟩, hconj_B⟩ := su2_conj_to_diag B

  have htrace_D : trace (D_A : Matrix (Fin 2) (Fin 2) ℂ) =
      trace (D_B : Matrix (Fin 2) (Fin 2) ℂ) := by

    have hA := su2_trace_conj_inv
    rw [isConj_iff] at hconj_A hconj_B
    obtain ⟨P_A, hP_A⟩ := hconj_A
    obtain ⟨P_B, hP_B⟩ := hconj_B
    have h1 : trace D_A.val = trace A.val := by
      rw [← hP_A]; exact su2_trace_conj_inv P_A A
    have h2 : trace D_B.val = trace B.val := by
      rw [← hP_B]; exact su2_trace_conj_inv P_B B
    rw [show (D_A : Matrix _ _ ℂ) = D_A.val from rfl,
        show (D_B : Matrix _ _ ℂ) = D_B.val from rfl]
    rw [h1, h2]; exact h
  have hconj_D := su2_diag_conj_of_trace D_A D_B z_A z_B hz_A hz_B hD_A hD_B htrace_D
  exact hconj_A.trans (hconj_D.trans hconj_B.symm)




lemma su2_center_ne_top :
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ ⊤ := by
  intro heq
  have hA : !![((0 : ℂ)), -1; 1, 0] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
      (apply Complex.ext <;> simp)
    · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
      (apply Complex.ext <;> simp)
    · simp [Matrix.detMonoidHom, Matrix.det_fin_two]
  have hB : !![(Complex.I : ℂ), 0; 0, -Complex.I] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
            Matrix.map, Complex.I] <;>
      first | (apply Complex.ext <;> simp) | left; (apply Complex.ext <;> simp)
    · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
            Matrix.map, Complex.I] <;>
      first | (apply Complex.ext <;> simp) | right; (apply Complex.ext <;> simp)
    · simp [Matrix.detMonoidHom, Matrix.det_fin_two, Complex.I]
      apply Complex.ext <;> simp
  have hAmem : (⟨!![0, -1; 1, 0], hA⟩ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := heq ▸ Subgroup.mem_top _
  rw [Subgroup.mem_center_iff] at hAmem
  have hcomm := hAmem ⟨!![Complex.I, 0; 0, -Complex.I], hB⟩
  have hval := congr_arg Subtype.val hcomm
  have h01 := congr_fun (congr_fun hval 0) 1
  simp at h01
  have : Complex.I.im = (-Complex.I).im := by rw [h01]
  simp at this; norm_num at this



theorem exists_sq_not_in_zero_one_neg_one' (F : Type*) [Field F] [Fintype F]
    (hF : 5 < Fintype.card F) :
    ∃ r : F, r ^ 2 ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 ≠ -1 := by
  classical
  by_contra h
  push_neg at h
  set S0 : Finset F := Finset.univ.filter (fun r => r ^ 2 = 0)
  set S1 : Finset F := Finset.univ.filter (fun r => r ^ 2 = 1)
  set Sn1 : Finset F := Finset.univ.filter (fun r => r ^ 2 = -1)
  have hcover : Finset.univ ⊆ S0 ∪ S1 ∪ Sn1 := by
    intro r _
    simp only [S0, S1, Sn1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have := h r; tauto
  have hS0 : S0.card ≤ 1 := by
    have h0 : S0 ⊆ ({(0 : F)} : Finset F) := by
      intro x hx
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [pow_eq_zero_iff (by omega : 2 ≠ 0)] at hx
      exact Finset.mem_singleton.mpr hx
    linarith [Finset.card_le_card h0, Finset.card_singleton (0 : F)]
  have hS1 : S1.card ≤ 2 := by
    have hsub : S1 ⊆ ({(1 : F), -1} : Finset F) := by
      intro x hx
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have h1 : x ^ 2 = (1 : F) ^ 2 := by ring_nf; exact hx
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with heq | heq
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq))
    calc S1.card ≤ ({(1 : F), -1} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hSn1 : Sn1.card ≤ 2 := by
    by_cases hn1 : ∃ r : F, r ^ 2 = -1
    · obtain ⟨r0, hr0⟩ := hn1
      have hsub : Sn1 ⊆ ({r0, -r0} : Finset F) := by
        intro x hx
        simp only [Sn1, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have h1 : x ^ 2 = r0 ^ 2 := by rw [hx, hr0]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with heq | heq
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq))
      calc Sn1.card ≤ ({r0, -r0} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    · have hempty : Sn1 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x
        simp only [Sn1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hx => hn1 ⟨x, hx⟩
      rw [hempty]; simp
  have hle : Fintype.card F ≤ (S0 ∪ S1 ∪ Sn1).card :=
    (Finset.card_univ (α := F)).symm ▸ Finset.card_le_card hcover
  have hle2 : (S0 ∪ S1 ∪ Sn1).card ≤ 5 :=
    calc (S0 ∪ S1 ∪ Sn1).card
        ≤ (S0 ∪ S1).card + Sn1.card := Finset.card_union_le _ _
      _ ≤ S0.card + S1.card + Sn1.card := by linarith [Finset.card_union_le S0 S1]
      _ ≤ 1 + 2 + 2 := by linarith
      _ = 5 := by norm_num
  linarith


variable {F : Type*} [Field F]

open Polynomial Module.End in
set_option maxHeartbeats 8000000 in
def SL2.HasEigenvalues (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  (↑M : Matrix (Fin 2) (Fin 2) F).charpoly =
    (Polynomial.X - Polynomial.C s) * (Polynomial.X - Polynomial.C s⁻¹)

def SL2.IsConjToDiag (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
    (P * M * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Matrix.diagonal ![s, s⁻¹]

theorem sl2_normal_subgroup_contains_all_conj_to_diag
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hN : N.Normal) (s : F)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (hB : B ∈ N)
    (hBdiag : SL2.IsConjToDiag B s)
    (Q : Matrix.SpecialLinearGroup (Fin 2) F)
    (hQdiag : SL2.IsConjToDiag Q s) :
    Q ∈ N := by
  obtain ⟨P_B, hPB⟩ := hBdiag
  obtain ⟨P_Q, hPQ⟩ := hQdiag

  have h1 : P_B * B * P_B⁻¹ = P_Q * Q * P_Q⁻¹ := by
    ext1; rw [hPB, hPQ]

  have hconj : Q = (P_Q⁻¹ * P_B) * B * (P_Q⁻¹ * P_B)⁻¹ := by
    have h2 : Q = P_Q⁻¹ * (P_B * B * P_B⁻¹) * P_Q := by
      rw [h1]; group
    rw [h2]; group

  rw [hconj]
  exact hN.conj_mem B hB (P_Q⁻¹ * P_B)


set_option maxHeartbeats 8000000 in
theorem sl2_eigenvalues_implies_conj_to_diag (s : F) (hs : s ≠ s⁻¹)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (hM : SL2.HasEigenvalues M s) :
    SL2.IsConjToDiag M s := by
  open Polynomial Module.End in
  unfold SL2.HasEigenvalues at hM
  unfold SL2.IsConjToDiag
  have hs_sub : s - s⁻¹ ≠ 0 := sub_ne_zero.mpr hs
  set M' := (↑M : Matrix (Fin 2) (Fin 2) F)
  have heig_s : HasEigenvalue (Matrix.toLin' M') s := by
    rw [hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM]; simp [IsRoot]
  have heig_sinv : HasEigenvalue (Matrix.toLin' M') s⁻¹ := by
    rw [hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM]; simp [IsRoot]
  obtain ⟨v₁, hv₁_mem, hv₁_ne⟩ := (Submodule.ne_bot_iff _).mp (hasEigenvalue_iff.mp heig_s)
  obtain ⟨v₂, hv₂_mem, hv₂_ne⟩ := (Submodule.ne_bot_iff _).mp (hasEigenvalue_iff.mp heig_sinv)
  rw [mem_eigenspace_iff] at hv₁_mem hv₂_mem
  have hd : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0 := by
    intro hd0
    have hd_eq : v₁ 0 * v₂ 1 = v₁ 1 * v₂ 0 := sub_eq_zero.mp hd0
    have hprop : ∃ a : F, v₁ = a • v₂ := by
      by_cases hv20 : v₂ 0 = 0
      · have hv21 : v₂ 1 ≠ 0 := fun h21 => hv₂_ne (funext fun i => by fin_cases i <;> assumption)
        have hv10 : v₁ 0 = 0 := by
          have h := hd_eq; rw [hv20, mul_zero] at h; exact (mul_eq_zero.mp h).resolve_right hv21
        exact ⟨v₁ 1 / v₂ 1, funext fun i => by
          fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv10, hv20, div_mul_cancel₀ _ hv21]⟩
      · exact ⟨v₁ 0 / v₂ 0, funext fun i => by
          fin_cases i
          · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv20]
          · simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
            rw [eq_div_iff hv20]
            have h1 : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := rfl
            simp only [h1]; ring_nf
            simp only [show v₁ 1 * v₂ 0 = v₁ 0 * v₂ 1 from hd_eq.symm]⟩
    obtain ⟨a, ha⟩ := hprop
    have h1 := hv₁_mem; rw [ha, map_smul, hv₂_mem, smul_smul, smul_smul] at h1
    have heq2 : a * s⁻¹ = s * a := smul_left_injective _ hv₂_ne h1
    have h4 : a * (s - s⁻¹) = 0 := by linear_combination (mul_comm s a).symm.trans heq2.symm
    rcases mul_eq_zero.mp h4 with h | h
    · rw [h, zero_smul] at ha; exact hv₁_ne ha
    · exact hs_sub h
  set d := v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0
  let Q_mat : Matrix (Fin 2) (Fin 2) F :=
    Matrix.of fun i j => if j = (0 : Fin 2) then d⁻¹ * v₁ i else v₂ i
  have hQ_det : Q_mat.det = 1 := by
    simp only [Q_mat, Matrix.det_fin_two, Matrix.of_apply]; norm_num; field_simp; ring
  let Q : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Q_mat, hQ_det⟩
  have hv₁_eq : ∀ i, M' i 0 * v₁ 0 + M' i 1 * v₁ 1 = s * v₁ i := fun i => by
    have := congr_fun hv₁_mem i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
      Fin.sum_univ_two] using this
  have hv₂_eq : ∀ i, M' i 0 * v₂ 0 + M' i 1 * v₂ 1 = s⁻¹ * v₂ i := fun i => by
    have := congr_fun hv₂_mem i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
      Fin.sum_univ_two] using this
  have hMQ : M' * Q_mat = Q_mat * Matrix.diagonal ![s, s⁻¹] := by
    ext i j
    simp only [Q_mat, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
    fin_cases j
    · simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false, mul_zero,
        add_zero, cons_val_zero, cons_val_one, head_cons, mul_ite, mul_one]
      linear_combination d⁻¹ * hv₁_eq i
    · simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false, mul_zero,
        zero_add, cons_val_zero, cons_val_one, head_cons, mul_ite, mul_one]
      linear_combination hv₂_eq i
  have hQinv_mul : Q_mat⁻¹ * Q_mat = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [isUnit_iff_ne_zero, hQ_det]; exact one_ne_zero)
  refine ⟨Q⁻¹, ?_⟩
  have hQinv_val : (Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Q_mat.adjugate := rfl
  have hadj : Q_mat.adjugate = Q_mat⁻¹ := by
    rw [Matrix.inv_def, hQ_det, Ring.inverse_one, one_smul]
  show (Q⁻¹ * M * Q⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Matrix.diagonal ![s, s⁻¹]
  show (Q⁻¹).1 * M.1 * (Q⁻¹⁻¹).1 = Matrix.diagonal ![s, s⁻¹]
  rw [hQinv_val, hadj, show (Q⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Q_mat from by
    simp [Q]]
  calc Q_mat⁻¹ * M' * Q_mat
      = Q_mat⁻¹ * (M' * Q_mat) := by rw [Matrix.mul_assoc]
    _ = Q_mat⁻¹ * (Q_mat * Matrix.diagonal ![s, s⁻¹]) := by rw [hMQ]
    _ = Q_mat⁻¹ * Q_mat * Matrix.diagonal ![s, s⁻¹] := by rw [Matrix.mul_assoc]
    _ = 1 * Matrix.diagonal ![s, s⁻¹] := by rw [hQinv_mul]
    _ = Matrix.diagonal ![s, s⁻¹] := by rw [Matrix.one_mul]

theorem sl2_normal_contains_all_with_eigenvalues
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hN : N.Normal) (s : F) (hs : s ≠ s⁻¹)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (hB : B ∈ N)
    (hBeig : SL2.HasEigenvalues B s)
    (Q : Matrix.SpecialLinearGroup (Fin 2) F)
    (hQeig : SL2.HasEigenvalues Q s) :
    Q ∈ N :=
  sl2_normal_subgroup_contains_all_conj_to_diag N hN s B hB
    (sl2_eigenvalues_implies_conj_to_diag s hs B hBeig) Q
    (sl2_eigenvalues_implies_conj_to_diag s hs Q hQeig)



end SimpleGroups
