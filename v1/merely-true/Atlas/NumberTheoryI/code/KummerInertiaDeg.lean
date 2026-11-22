/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.KummerDedekind

open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField

namespace DedekindKummer

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

theorem inertiaDeg_eq_natDegree_lift
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        (Q.map (Int.castRingHom (ZMod p))).natDegree :=
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hp hQ

theorem ramificationIdx_eq_multiplicity_lift
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
    (span {(p : ℤ)}).ramificationIdx
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        multiplicity (Q.map (Int.castRingHom (ZMod p)))
          ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
  NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply hp hQ

theorem prime_eq_span_pair
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
    ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : 𝓞 K), aeval θ Q} :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ

theorem kummer_inertiaDeg_ramificationIdx_prime
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        (Q.map (Int.castRingHom (ZMod p))).natDegree
    ∧ (span {(p : ℤ)}).ramificationIdx
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        multiplicity (Q.map (Int.castRingHom (ZMod p)))
          ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))
    ∧ ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : 𝓞 K), aeval θ Q} :=
  ⟨inertiaDeg_eq_natDegree_lift hp hQ,
   ramificationIdx_eq_multiplicity_lift hp hQ,
   prime_eq_span_pair hp hQ⟩

end DedekindKummer
