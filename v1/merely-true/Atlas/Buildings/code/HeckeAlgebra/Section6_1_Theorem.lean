/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.HeckeAlgebra.GenericAlgebraUniqueness

open scoped Classical

namespace HeckeAlgebra


variable {B : Type*} {M : CoxeterMatrix B} {R : Type*} [CommRing R]

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- Section 6.1 main theorem (Garrett): combining existence and uniqueness for the
generic Hecke algebra. The first conjunct asserts $A$ satisfies all standard length
rules, identities, and associativity; the second asserts that any other multiplication
on the same module satisfying these axioms equals $A.\mathrm{mul}$. -/
theorem section6_1_theorem (A : GenericAlgebra M' R') :

    (
     (let cs := M'.toCoxeterSystem
      ∀ (s : B') (w : M'.Group),
        cs.length (cs.simple s * w) > cs.length w →
        A.mul (A.basis (cs.simple s)) (A.basis w) = A.basis (cs.simple s * w)) ∧

     (let cs := M'.toCoxeterSystem
      ∀ (s : B'),
        A.mul (A.basis (cs.simple s)) (A.basis (cs.simple s)) =
          A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
                (A.smul (A.sc.b s) (A.basis 1))) ∧

     (∀ x, A.mul (A.basis 1) x = x) ∧
     (∀ x, A.mul x (A.basis 1) = x) ∧

     (let cs := M'.toCoxeterSystem
      ∀ (s : B') (w : M'.Group),
        cs.length (cs.simple s * w) < cs.length w →
        A.mul (A.basis (cs.simple s)) (A.basis w) =
          A.add (A.smul (A.sc.a s) (A.basis w))
                (A.smul (A.sc.b s) (A.basis (cs.simple s * w)))) ∧

     (let cs := M'.toCoxeterSystem
      ∀ (t : B') (w : M'.Group),
        cs.length (w * cs.simple t) > cs.length w →
        A.mul (A.basis w) (A.basis (cs.simple t)) = A.basis (w * cs.simple t)) ∧

     (let cs := M'.toCoxeterSystem
      ∀ (s : B') (w : M'.Group),
        cs.length (w * cs.simple s) < cs.length w →
        A.mul (A.basis w) (A.basis (cs.simple s)) =
          A.add (A.smul (A.sc.a s) (A.basis w))
                (A.smul (A.sc.b s) (A.basis (w * cs.simple s)))) ∧

     (∀ x y z, A.mul (A.mul x y) z = A.mul x (A.mul y z))) ∧

    (∀ (mul₂ : A.carrier → A.carrier → A.carrier),
      (∀ (s : B') (w : M'.Group),
        M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
          M'.toCoxeterSystem.length w →
        mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) =
          A.basis (M'.toCoxeterSystem.simple s * w)) →
      (∀ (s : B'),
        mul₂ (A.basis (M'.toCoxeterSystem.simple s))
             (A.basis (M'.toCoxeterSystem.simple s)) =
          A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s)))
                (A.smul (A.sc.b s) (A.basis 1))) →
      (∀ x, mul₂ (A.basis 1) x = x) →
      (∀ x, mul₂ x (A.basis 1) = x) →
      (∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z)) →
      (∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z)) →
      (∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y)) →
      (∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y)) →
      (∀ (s : B') (x y : A.carrier),
        mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) =
          mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) →
      (∀ (t : B') (x y : A.carrier),
        mul₂ (mul₂ x y) (A.basis (M'.toCoxeterSystem.simple t)) =
          mul₂ x (mul₂ y (A.basis (M'.toCoxeterSystem.simple t)))) →
      ∀ x y, mul₂ x y = A.mul x y) := by
  constructor
  · exact ⟨A.length_up,
           A.quadratic,
           A.identity_left,
           A.identity_right,
           A.SatisfiesLengthDownRule,
           A.SatisfiesRightLengthUpRule,
           A.SatisfiesRightLengthDownRule,
           A.mul_assoc⟩
  · intro mul₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact generic_algebra_unique A mul₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end HeckeAlgebra
