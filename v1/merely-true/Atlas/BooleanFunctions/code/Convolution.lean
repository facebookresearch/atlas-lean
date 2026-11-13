/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion

open Finset BigOperators

namespace BooleanFourier

def boolMul {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => !(x i ^^ y i)

lemma boolToReal_xnor (a b : Bool) :
    boolToReal (!(a ^^ b)) = boolToReal a * boolToReal b := by
  cases a <;> cases b <;> simp [boolToReal]

lemma chi_boolMul {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) :
    chi S (boolMul x y) = chi S x * chi S y := by
  simp only [chi, boolMul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact boolToReal_xnor (x i) (y i)

lemma boolMul_comm {n : ℕ} (x y : Fin n → Bool) : boolMul x y = boolMul y x := by
  ext i
  simp [boolMul, Bool.xor_comm]

noncomputable def conv {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun x => (1 / (2 : ℝ) ^ n) * ∑ y : Fin n → Bool, f y * g (boolMul x y)

theorem fourierCoeff_conv {n : ℕ} (f g : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff (conv f g) S = fourierCoeff f S * fourierCoeff g S := by
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp only [fourierCoeff, conv, one_div]


  suffices key : ∑ x : Fin n → Bool,
      (∑ y : Fin n → Bool, f y * g (boolMul x y)) * chi S x =
      (∑ x : Fin n → Bool, f x * chi S x) *
      (∑ x : Fin n → Bool, g x * chi S x) by
    have lhs_rw : ((2 : ℝ) ^ n)⁻¹ *
        ∑ x : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ *
          (∑ y : Fin n → Bool, f y * g (boolMul x y)) * chi S x =
        ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ *
          ∑ x : Fin n → Bool,
            (∑ y : Fin n → Bool, f y * g (boolMul x y)) * chi S x := by
      simp_rw [show ∀ x : Fin n → Bool,
        ((2 : ℝ) ^ n)⁻¹ * (∑ y, f y * g (boolMul x y)) * chi S x =
        ((2 : ℝ) ^ n)⁻¹ * ((∑ y, f y * g (boolMul x y)) * chi S x)
        from fun x => by ring]
      rw [← Finset.mul_sum]
      ring
    rw [lhs_rw, key]
    ring

  have expand_lhs : ∑ x : Fin n → Bool,
      (∑ y : Fin n → Bool, f y * g (boolMul x y)) * chi S x =
      ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
        f y * g (boolMul x y) * chi S x := by
    congr 1; ext x; exact Finset.sum_mul _ _ _
  rw [expand_lhs, Finset.sum_comm]

  have inner_eq : ∀ y : Fin n → Bool,
      ∑ x : Fin n → Bool, f y * g (boolMul x y) * chi S x =
      f y * chi S y * ∑ z : Fin n → Bool, g z * chi S z := by
    intro y
    have boolMul_right_cancel : ∀ z : Fin n → Bool,
        boolMul (boolMul z y) y = z := by
      intro z; ext i; simp [boolMul]
    have reindex : ∑ x : Fin n → Bool, f y * g (boolMul x y) * chi S x =
        ∑ z : Fin n → Bool, f y * g z * chi S (boolMul y z) := by
      apply Finset.sum_nbij (fun x => boolMul x y)
      · intro a _; exact Finset.mem_univ _
      · intro a₁ a₂ _ _ h
        have := congr_arg (boolMul · y) h
        simp only [boolMul_right_cancel] at this
        exact this
      · intro z _
        exact ⟨boolMul z y, Finset.mem_univ _, boolMul_right_cancel z⟩
      · intro x _
        have hx : boolMul y (boolMul x y) = x := by
          rw [boolMul_comm y (boolMul x y), boolMul_right_cancel x]
        simp only [hx]
    rw [reindex]
    simp_rw [chi_boolMul]
    simp_rw [show ∀ z, f y * g z * (chi S y * chi S z) =
      f y * chi S y * (g z * chi S z) from fun z => by ring]
    rw [← Finset.mul_sum]
  simp_rw [inner_eq, ← Finset.sum_mul]

end BooleanFourier
