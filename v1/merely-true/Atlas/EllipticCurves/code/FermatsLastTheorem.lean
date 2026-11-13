/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.EllipticCurves.code.Isogenies

noncomputable section GaloisRepInfra

open Matrix CongruenceSubgroup

/-- The algebraic closure of `ℚ` inside `ℂ`, viewed as an intermediate field. This
provides a concrete model of `ℚ̄` sitting inside `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- The absolute Galois group of `ℚ`, realized as the group of `ℚ`-algebra
automorphisms of `Qbar`. -/
abbrev AbsGaloisGroupQ := ↥Qbar ≃ₐ[ℚ] ↥Qbar

/-- A mod-`ℓ` Galois representation is a group homomorphism from the absolute Galois
group of `ℚ` to `GL₂(ℤ/ℓℤ)`. -/
abbrev GaloisRepMod (ℓ : ℕ) := AbsGaloisGroupQ →* GL (Fin 2) (ZMod ℓ)



/-- A mod-`ℓ` Galois representation is *irreducible* if no nonzero vector
`v ∈ (ℤ/ℓℤ)²` is simultaneously an eigenvector of every `ρ(g)`. -/
def GaloisRepMod.IsIrreducible {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  ∀ (v : Fin 2 → ZMod ℓ), v ≠ 0 →
    ¬∀ (g : AbsGaloisGroupQ),
      ∃ (c : ZMod ℓ), (↑(ρ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v



end GaloisRepInfra

noncomputable section

namespace FLT

/-- An elliptic curve over `ℚ`: a Weierstrass curve in affine form together with a
proof that it satisfies the elliptic (nonsingular) condition. -/
abbrev EllipticCurveOverQ := { E : WeierstrassCurve.Affine ℚ // E.IsElliptic }

open UniqueFactorizationMonoid





/-- An elliptic curve over `ℚ` is *semistable* if it has no additive reduction at any
prime — equivalently, all bad reduction is multiplicative. -/
def IsSemistable (E : EllipticCurveOverQ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ],
    ¬ (E.val.minimal R).HasAdditiveReduction R










/-- A weight-`2` newform of level `N`, specified by its Fourier coefficients:
normalized so that `a₁ = 1`, multiplicative on coprime indices, and satisfying the
standard Hecke recursion at primes `p ∤ N`. -/
structure Weight2Newform (N : ℕ) where
  coeff : ℕ → ℤ
  coeff_one : coeff 1 = 1
  coeff_mult : ∀ m n : ℕ, Nat.Coprime m n → coeff (m * n) = coeff m * coeff n
  coeff_prime_power : ∀ (p : ℕ) (r : ℕ), Nat.Prime p → ¬(p ∣ N) → r ≥ 1 →
    coeff (p ^ (r + 1)) = coeff p * coeff (p ^ r) - (p : ℤ) * coeff (p ^ (r - 1))



















/-- `3` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- `5` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩













end FLT

end

noncomputable section

namespace EllipticCurve

/-- Convenience abbreviation for `FLT.EllipticCurveOverQ`, the type of elliptic
curves over `ℚ`. -/
abbrev OverQ := FLT.EllipticCurveOverQ




/-- An elliptic curve over `ℚ` is semistable, re-exported from `FLT`. -/
def IsSemistable (E : FLT.EllipticCurveOverQ) : Prop := FLT.IsSemistable E


end EllipticCurve

end

noncomputable section


end
