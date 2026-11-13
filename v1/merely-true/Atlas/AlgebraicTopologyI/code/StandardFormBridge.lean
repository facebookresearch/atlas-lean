/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Prop30_6
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section

set_option autoImplicit false

namespace SymmetricBilinearForms

open Finset

/-- Evaluates the `(j,i)`-entry of the diagonal block in the matrix of
the standard `F₂` form: summing the indicator `[x = j ∧ x = i]` over
`x : Fin a` gives `1` if `i < a` and `i = j`, otherwise `0`. Used in
`standardFormF2_eq_toMatrix'` to compute the diagonal part of the Gram
matrix. -/
lemma sum_diagonal_ji (a : ℕ) (i j : ℕ) :
    (∑ x : Fin a, if (x : Fin a).val = j then
        (if (x : Fin a).val = i then (1 : ZMod 2) else 0) else 0) =
      if (i < a ∧ i = j) then 1 else 0 := by
  have key : ∀ x : Fin a,
      (if x.val = j then (if x.val = i then (1 : ZMod 2) else 0) else 0) =
      if (x.val = i ∧ i = j) then 1 else 0 := by
    intro x; split_ifs <;> simp_all
  simp_rw [key, ite_and]
  by_cases hia : i < a
  · have heq : (∑ x : Fin a, if x.val = i then (if i = j then (1 : ZMod 2) else 0) else 0) =
        (∑ x : Fin a, if x = ⟨i, hia⟩ then (if i = j then 1 else 0) else 0) := by
      congr 1; funext x; simp [Fin.ext_iff]
    rw [heq, Finset.sum_ite_eq']; simp [hia]
  · have : (∑ x : Fin a, if x.val = i then (if i = j then (1 : ZMod 2) else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro x _; simp [show x.val ≠ i from by omega]
    rw [this]; simp [hia]

/-- Evaluates the `(j,i)`-entry of the hyperbolic-plane block in the
matrix of the standard `F₂` form: each pair `(a+2x, a+2x+1)` contributes
the antidiagonal `[[0,1],[1,0]]`, so the sum is `1` iff `i, j ≥ a` and
`(i-a)/2 = (j-a)/2` while `(i-a) % 2 ≠ (j-a) % 2`. Used in
`standardFormF2_eq_toMatrix'`. -/
lemma sum_hyperbolic_ji (a b : ℕ) (i j : ℕ) (_hi : i < a + 2*b) (hj : j < a + 2*b) :
    (∑ x : Fin b,
        ((if a + 2 * x.val + 1 = j then
            (if a + 2 * x.val + 0 = i then (1 : ZMod 2) else 0) else 0) +
        (if a + 2 * x.val + 0 = j then
            (if a + 2 * x.val + 1 = i then (1 : ZMod 2) else 0) else 0))) =
      if (i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2) then 1 else 0 := by
  have key : ∀ x : Fin b,
      (if a + 2 * x.val + 1 = j then
          (if a + 2 * x.val + 0 = i then (1 : ZMod 2) else 0) else 0) +
      (if a + 2 * x.val + 0 = j then
          (if a + 2 * x.val + 1 = i then (1 : ZMod 2) else 0) else 0) =
      if (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2)
        then 1 else 0 := by
    intro x; split_ifs <;> simp_all (config := { decide := true }) <;> omega
  simp_rw [key]
  split_ifs with hP
  · obtain ⟨hia, hja, hdiv, hmod⟩ := hP
    have hk : (i - a) / 2 < b := by omega
    have hsimpl : ∀ x : Fin b,
        (if (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2)
          then (1 : ZMod 2) else 0) =
        (if x.val = (i - a) / 2 then 1 else 0) := by
      intro x; split_ifs with h1 h2 h3 <;> simp_all
    simp_rw [hsimpl]
    have heq2 : (∑ x : Fin b, if x.val = (i - a) / 2 then (1 : ZMod 2) else 0) =
        (∑ x : Fin b, if x = ⟨(i - a) / 2, hk⟩ then 1 else 0) := by
      congr 1; funext x; simp [Fin.ext_iff]
    rw [heq2, Finset.sum_ite_eq']; simp
  · apply Finset.sum_eq_zero; intro x _
    have : ¬ (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2) := by
      intro ⟨_, h2, h3, h4, h5⟩; exact hP ⟨h2, h3, h4, h5⟩
    simp [this]

/-- Linear isomorphism `(Fin a → F₂) × (Fin b → Fin 2 → F₂) ≃ₗ
Fin (a + 2 b) → F₂` that interleaves the two factors as in
`standardFormF2`: indices `< a` come from the first factor, and indices
`a + 2k + r` (with `r ∈ {0,1}`) come from the `r`-th coordinate of the
`k`-th block in the second factor. Bridges the abstract product
presentation of Proposition 30.6 with the concrete matrix presentation
`standardFormF2 a b`. -/
def prodToFinEquiv (a b : ℕ) :
    ((Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)) ≃ₗ[ZMod 2] (Fin (a + 2 * b) → ZMod 2) where
  toFun := fun ⟨f, g⟩ => fun i =>
    if h : i.val < a then f ⟨i.val, h⟩
    else g ⟨(i.val - a) / 2, by omega⟩ ⟨(i.val - a) % 2, by omega⟩
  map_add' := by
    intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩; funext i; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' := by
    intro r ⟨f, g⟩; funext i; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl
  invFun := fun h =>
    (fun i => h ⟨i.val, by omega⟩, fun j k => h ⟨a + 2 * j.val + k.val, by omega⟩)
  left_inv := by
    intro ⟨f, g⟩; simp only; show (_, _) = (f, g)
    congr 1
    · funext i; simp only [dif_pos i.isLt]
    · funext j k
      have hlt : ¬ (a + 2 * j.val + k.val) < a := by omega
      simp only [hlt, dite_false]
      show g ⟨(a + 2 * j.val + k.val - a) / 2, _⟩ ⟨(a + 2 * j.val + k.val - a) % 2, _⟩ = g j k
      have h1 : (a + 2 * j.val + k.val - a) / 2 = j.val := by omega
      have h2 : (a + 2 * j.val + k.val - a) % 2 = k.val := by omega
      simp only [h1, h2]
  right_inv := by
    intro h; funext i; simp only
    split_ifs with hlt
    · rfl
    · show h ⟨a + 2 * ((i.val - a) / 2) + (i.val - a) % 2, _⟩ = h i
      have heq : a + 2 * ((i.val - a) / 2) + (i.val - a) % 2 = i.val := by omega
      simp only [heq]

set_option maxHeartbeats 1600000 in
/-- **Bridge from the abstract Proposition 30.6 to the concrete
`standardFormF2 a b`.** Transporting `BilinFormZMod2.standardF2Form a b`
along the isomorphism `prodToFinEquiv a b` and then taking its matrix
representation reproduces exactly the explicit Gram matrix
`standardFormF2 a b`. This identifies the abstract block-diagonal form
of the classification theorem with the concrete `(a + 2b) × (a + 2b)`
matrix used downstream. -/
theorem standardFormF2_eq_toMatrix' (a b : ℕ) :
    LinearMap.BilinForm.toMatrix' (LinearMap.BilinForm.congr (prodToFinEquiv a b)
      (BilinFormZMod2.standardF2Form a b)) = standardFormF2 a b := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.congr_apply,
    BilinFormZMod2.standardF2Form, LinearMap.mk₂_apply, prodToFinEquiv, LinearEquiv.coe_symm_mk]
  simp only [Pi.single_apply, Fin.ext_iff]
  simp only [mul_ite, mul_one, mul_zero]

  simp only [Fin.val_zero, Fin.val_one]

  rw [sum_diagonal_ji a i.val j.val,
      sum_hyperbolic_ji a b i.val j.val i.isLt j.isLt]

  simp only [standardFormF2]
  split_ifs <;> first | rfl | omega

end SymmetricBilinearForms

end
