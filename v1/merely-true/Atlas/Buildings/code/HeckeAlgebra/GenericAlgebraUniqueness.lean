/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity

open scoped Classical

namespace HeckeAlgebra


section Uniqueness

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- Abstract data of a Hecke-algebra multiplication on `C` over $R$ with basis indexed by
$W = M.\mathrm{Group}$: the length-up product $T_s T_w = T_{sw}$ when $\ell(sw) > \ell(w)$,
the length-down product $T_s T_w = a_s T_w + b_s T_{sw}$, left-identity, distributivity,
scalar associativity, and a span principle on the basis. -/
structure HeckeMultiplication (M : CoxeterMatrix B') (R : Type*) [CommRing R]
    (C : Type*) where
  basis : M.Group → C
  smul : R → C → C
  mul : C → C → C
  add : C → C → C
  sc : StructureConstants B' R
  length_up : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) >
      M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      basis (M.toCoxeterSystem.simple s * w)
  length_down : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) <
      M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      add (smul (sc.a s) (basis w))
          (smul (sc.b s) (basis (M.toCoxeterSystem.simple s * w)))
  identity_left : ∀ (x : C), mul (basis 1) x = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  gen_left_assoc : ∀ (s : B') (x y : C),
    mul (basis (M.toCoxeterSystem.simple s)) (mul x y) =
      mul (mul (basis (M.toCoxeterSystem.simple s)) x) y
  basis_span : ∀ (P : C → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z

variable {C : Type*}


/-- If two Hecke multiplications share the same basis function, they agree pointwise on basis elements. -/
theorem basis_eq_of_h_basis
    {H₁ H₂ : HeckeMultiplication M' R' C}
    (h_basis : H₁.basis = H₂.basis) (w : M'.Group) :
    H₁.basis w = H₂.basis w :=
  congr_fun h_basis w

/-- Step in the uniqueness argument: two Hecke multiplications agree on products
$T_s · T_w$ where $T_s$ is a simple generator and $T_w$ is any basis element. -/
theorem HeckeMultiplication.mul_gen_basis_eq
    (H₁ H₂ : HeckeMultiplication M' R' C)
    (h_basis : H₁.basis = H₂.basis)
    (h_add : H₁.add = H₂.add)
    (h_smul : H₁.smul = H₂.smul)
    (h_sc : H₁.sc = H₂.sc)
    (s : B') (w : M'.Group) :
    H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) (H₁.basis w) =
    H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) (H₁.basis w) := by

  have hbs := basis_eq_of_h_basis h_basis
  rcases M'.toCoxeterSystem.length_simple_mul w s with h_up | h_down
  ·
    have hgt : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
        M'.toCoxeterSystem.length w := by omega
    rw [H₁.length_up s w hgt]
    rw [show H₁.basis (M'.toCoxeterSystem.simple s) = H₂.basis (M'.toCoxeterSystem.simple s)
          from hbs _, show H₁.basis w = H₂.basis w from hbs w]
    rw [H₂.length_up s w hgt, ← hbs]
  ·
    have hlt : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) <
        M'.toCoxeterSystem.length w := by omega
    rw [H₁.length_down s w hlt]
    rw [show H₁.basis (M'.toCoxeterSystem.simple s) = H₂.basis (M'.toCoxeterSystem.simple s)
          from hbs _, show H₁.basis w = H₂.basis w from hbs w]
    rw [H₂.length_down s w hlt]
    simp only [hbs, h_add, h_smul, h_sc]

/-- Two Hecke multiplications agree on products $T_s · z$ for any $z ∈ C$, given
agreement on basis, addition, scalar action, and structure constants. -/
theorem HeckeMultiplication.mul_gen_eq
    (H₁ H₂ : HeckeMultiplication M' R' C)
    (h_basis : H₁.basis = H₂.basis)
    (h_add : H₁.add = H₂.add)
    (h_smul : H₁.smul = H₂.smul)
    (h_sc : H₁.sc = H₂.sc)
    (s : B') (z : C) :
    H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z =
    H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z := by
  apply H₁.basis_span (fun z =>
    H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z =
    H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z)
  · intro w
    exact H₁.mul_gen_basis_eq H₂ h_basis h_add h_smul h_sc s w
  ·
    intro x y hx hy
    rw [H₁.mul_add_right, hx, hy]
    simp only [show H₁.add = H₂.add from h_add]
    rw [← H₂.mul_add_right]
  ·
    intro r x hx
    rw [H₁.mul_smul_right, hx]
    simp only [show H₁.smul = H₂.smul from h_smul]
    rw [← H₂.mul_smul_right]

/-- Uniqueness on the basis: under agreement of basis, add, smul, and structure
constants, two Hecke multiplications coincide on all products $T_w · z$. The proof
proceeds by induction on $\ell(w)$. -/
theorem HeckeMultiplication.mul_basis_eq
    (H₁ H₂ : HeckeMultiplication M' R' C)
    (h_basis : H₁.basis = H₂.basis)
    (h_add : H₁.add = H₂.add)
    (h_smul : H₁.smul = H₂.smul)
    (h_sc : H₁.sc = H₂.sc) :
    ∀ (w : M'.Group) (z : C),
      H₁.mul (H₁.basis w) z = H₂.mul (H₁.basis w) z := by
  have hbs := basis_eq_of_h_basis h_basis
  suffices ∀ (n : ℕ) (w : M'.Group),
      M'.toCoxeterSystem.length w ≤ n →
      ∀ z, H₁.mul (H₁.basis w) z = H₂.mul (H₁.basis w) z by
    intro w z
    exact this (M'.toCoxeterSystem.length w) w le_rfl z
  intro n
  induction n with
  | zero =>
    intro w hw z
    have hw1 : w = 1 :=
      M'.toCoxeterSystem.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    rw [H₁.identity_left, hbs, H₂.identity_left]
  | succ n ih =>
    intro w hw z
    by_cases hw1 : w = 1
    · subst hw1
      rw [H₁.identity_left, hbs, H₂.identity_left]
    · obtain ⟨s, hs⟩ := M'.toCoxeterSystem.exists_leftDescent_of_ne_one hw1
      set cs := M'.toCoxeterSystem
      set sw := cs.simple s * w with hsw_def
      have hsw_lt : cs.length sw < cs.length w := hs
      have h_w_eq : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [h_w_eq]; exact hsw_lt

      have h1_decomp : H₁.mul (H₁.basis w) z =
          H₁.mul (H₁.basis (cs.simple s)) (H₁.mul (H₁.basis sw) z) := by
        conv_lhs => rw [← h_w_eq, ← H₁.length_up s sw hs_sw]
        rw [← H₁.gen_left_assoc]

      have h2_decomp : H₂.mul (H₁.basis w) z =
          H₂.mul (H₁.basis (cs.simple s)) (H₂.mul (H₁.basis sw) z) := by

        have : H₂.mul (H₂.basis w) z =
            H₂.mul (H₂.basis (cs.simple s)) (H₂.mul (H₂.basis sw) z) := by
          conv_lhs => rw [← h_w_eq, ← H₂.length_up s sw hs_sw]
          rw [← H₂.gen_left_assoc]
        rw [← hbs] at this
        rw [show H₂.basis (cs.simple s) = H₁.basis (cs.simple s) from (hbs _).symm,
            show H₂.basis sw = H₁.basis sw from (hbs _).symm] at this
        exact this
      rw [h1_decomp, h2_decomp]

      rw [ih sw (by omega) z]

      exact H₁.mul_gen_eq H₂ h_basis h_add h_smul h_sc s _

end Uniqueness

end HeckeAlgebra
