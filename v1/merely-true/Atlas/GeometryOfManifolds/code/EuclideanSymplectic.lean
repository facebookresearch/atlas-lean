/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.EuclideanDFS
import Atlas.GeometryOfManifolds.code.SymplecticManifolds

noncomputable section

open EuclideanΩ

/-- Every element of `Fin 2` is either `0` or `1`. -/
lemma Fin2_eq_zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨k, hk⟩; simp only [Fin.ext_iff]; omega

/-- Standard symplectic alternating $2$-form on $\mathbb{R}^{2n}$:
$\Omega(u, v) = \sum_{i=1}^{n} (u_i v_{n+i} - u_{n+i} v_i)$, with the $(e_i, f_i)$ basis given by
$f_i = e_{n+i}$ so that $\Omega(e_i, f_j) = \delta_{ij}$. -/
def standardSymplecticAlt (n : ℕ) : Eℝ (2 * n) [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  AlternatingMap.mk
    { toFun := fun v =>
        ∑ i : Fin n, (v 0 ⟨i.val, by omega⟩ * v 1 ⟨n + i.val, by omega⟩ -
                      v 0 ⟨n + i.val, by omega⟩ * v 1 ⟨i.val, by omega⟩)
      map_update_add' := fun v k u₁ u₂ => by
        classical
        have h01 : (0 : Fin 2) ≠ 1 := by omega
        have h10 : (1 : Fin 2) ≠ 0 := by omega
        rcases Fin2_eq_zero_or_one k with rfl | rfl
        · simp_rw [Function.update_self, Function.update_of_ne h10]
          rw [← Finset.sum_add_distrib]; congr 1; ext i
          simp only [PiLp.add_apply]; ring
        · simp_rw [Function.update_self, Function.update_of_ne h01]
          rw [← Finset.sum_add_distrib]; congr 1; ext i
          simp only [PiLp.add_apply]; ring
      map_update_smul' := fun v k r u => by
        classical
        have h01 : (0 : Fin 2) ≠ 1 := by omega
        have h10 : (1 : Fin 2) ≠ 0 := by omega
        rcases Fin2_eq_zero_or_one k with rfl | rfl
        · simp only [smul_eq_mul]
          simp_rw [Function.update_self, Function.update_of_ne h10]
          rw [Finset.mul_sum]; congr 1; ext i
          simp only [PiLp.smul_apply, smul_eq_mul]; ring
        · simp only [smul_eq_mul]
          simp_rw [Function.update_self, Function.update_of_ne h01]
          rw [Finset.mul_sum]; congr 1; ext i
          simp only [PiLp.smul_apply, smul_eq_mul]; ring }
    (fun v i j hij hveq => by
      have h01 : v 0 = v 1 := by
        rcases Fin2_eq_zero_or_one i with rfl | rfl <;>
          rcases Fin2_eq_zero_or_one j with rfl | rfl <;> simp_all
      simp_rw [h01]
      apply Finset.sum_eq_zero; intro k _; ring)

/-- The standard symplectic $2$-form on $\mathbb{R}^{2n}$ viewed as a constant differential form. -/
def standardSymplecticForm (n : ℕ) : EuclideanΩ (2 * n) 2 :=
  fun _ => standardSymplecticAlt n

/-- The standard symplectic form is closed: $d\Omega = 0$ (it is constant in $x$). -/
theorem standardSymplecticForm_closed (n : ℕ) :
    euclideanD_lifted (standardSymplecticForm n) = 0 := by
  unfold euclideanD_lifted standardSymplecticForm toCEuclideanΩ
  ext x v
  simp only [euclideanD, AlternatingMap.alternatizeUncurryFin_apply, EuclideanΩ.zero_apply',
    AlternatingMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hconst : fderiv ℝ (fun (_ : Eℝ (2 * n)) => toCAlt (standardSymplecticAlt n)) x = 0 := by
    have : (fun (_ : Eℝ (2 * n)) => toCAlt (standardSymplecticAlt n)) =
        Function.const _ (toCAlt (standardSymplecticAlt n)) := rfl
    rw [this]
    exact congr_fun (fderiv_const (toCAlt (standardSymplecticAlt n))) x
  unfold fderivToAltMap
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hconst,
    ContinuousLinearMap.zero_apply, map_zero, AlternatingMap.zero_apply, smul_zero]

/-- Bilinear nondegeneracy of the standard symplectic form: if $\Omega(u, v) = 0$ for all
$v$, then $u = 0$. -/
theorem standardSymplecticBilinear_nondegenerate (n : ℕ) (u : Eℝ (2 * n))
    (h : ∀ v : Eℝ (2 * n),
      (∑ i : Fin n, (u ⟨i.val, by omega⟩ * v ⟨n + i.val, by omega⟩ -
                     u ⟨n + i.val, by omega⟩ * v ⟨i.val, by omega⟩)) = 0) :
    u = 0 := by
  ext ⟨k, hk⟩
  simp only [PiLp.zero_apply]
  by_cases hkn : k < n
  ·
    have htest := h (EuclideanSpace.single ⟨n + k, by omega⟩ 1)
    simp only [PiLp.single_apply] at htest
    rw [Finset.sum_eq_single ⟨k, hkn⟩] at htest
    · simp only [ite_true, mul_one] at htest
      have hne : ¬(⟨k, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne, ite_false, mul_zero, sub_zero] at htest
      exact htest
    · intro i _ hi
      have : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ := by
        intro heq; exact hi (Fin.ext (by simpa using Fin.val_eq_of_eq heq))
      simp only [this, ite_false, mul_zero]
      have : ¬(⟨i.val, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [this, ite_false, mul_zero, sub_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  ·
    push Not at hkn
    have hk' : k - n < n := by omega
    have htest := h (EuclideanSpace.single ⟨k - n, by omega⟩ 1)
    simp only [PiLp.single_apply] at htest
    rw [Finset.sum_eq_single ⟨k - n, hk'⟩] at htest
    · have hne : ¬(⟨n + (k - n), by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne, ite_false, mul_zero, zero_sub, neg_eq_zero] at htest
      simp only [ite_true, mul_one] at htest
      have hkk : (⟨k, hk⟩ : Fin (2 * n)) = ⟨n + (k - n), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hkk]
      exact htest
    · intro i _ hi
      have hne1 : ¬(⟨i.val, by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ := by
        intro heq; exact hi (Fin.ext (by simpa using Fin.val_eq_of_eq heq))
      simp only [hne1, ite_false, mul_zero, sub_zero]
      have hne2 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne2, ite_false, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Nondegeneracy at the level of vector fields: the contraction $X \mapsto \iota_X \Omega$
is injective on vector fields on $\mathbb{R}^{2n}$. -/
theorem standardSymplecticForm_nondegenerate (n : ℕ) :
    Function.Injective (fun (X : EuclideanVF (2 * n)) =>
      euclideanIota X (standardSymplecticForm n)) := by
  intro X Y h
  funext x
  suffices hdiff : X x - Y x = 0 from sub_eq_zero.mp hdiff
  apply standardSymplecticBilinear_nondegenerate n
  intro v

  have hpt : euclideanIota X (standardSymplecticForm n) x =
             euclideanIota Y (standardSymplecticForm n) x := by
    have := congr_fun h x
    simp only at this
    exact this

  have key : (standardSymplecticAlt n).curryLeft (X x) =
             (standardSymplecticAlt n).curryLeft (Y x) := by
    have : euclideanIota X (standardSymplecticForm n) x =
           euclideanIota Y (standardSymplecticForm n) x := hpt
    simp only [euclideanIota, standardSymplecticForm] at this
    exact this

  have h_map_sub : (standardSymplecticAlt n).curryLeft (X x - Y x) =
      (standardSymplecticAlt n).curryLeft (X x) -
      (standardSymplecticAlt n).curryLeft (Y x) :=
    map_sub (standardSymplecticAlt n).curryLeft (X x) (Y x)
  have h_zero : (standardSymplecticAlt n).curryLeft (X x - Y x) = 0 := by
    rw [h_map_sub, key, sub_self]

  have h_eval : ∀ w : Fin 1 → Eℝ (2 * n),
      (standardSymplecticAlt n).curryLeft (X x - Y x) w = 0 := by
    intro w; rw [h_zero]; rfl

  have h_sum := h_eval (fun _ => v)
  simp only [AlternatingMap.curryLeft_apply_apply, standardSymplecticAlt,
    AlternatingMap.coe_mk, MultilinearMap.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h_sum
  exact h_sum

end
