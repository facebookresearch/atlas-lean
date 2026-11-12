/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

noncomputable section
open FractionalIdeal nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDomain R]

/-- Cartier divisors on the affine scheme `Spec R` realised as units of the fractional
ideals in the fraction field. -/
abbrev Prop22.DivC : Type _ :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ

/-- The principal-Cartier-divisor homomorphism: a nonzero element of the fraction
field maps to its principal fractional ideal. -/
abbrev Prop22.principalHom :
    (FractionRing R)ˣ →* Prop22.DivC R :=
  toPrincipalIdeal R (FractionRing R)

/-- The Cartier-to-Picard homomorphism `DivC(R) → Pic(R)`, sending a Cartier divisor
to its associated line bundle. -/
def Prop22.cartierToPicHom :
    Prop22.DivC R →* CommRing.Pic R :=
  (ClassGroup.equivPic R).toMonoidHom.comp (ClassGroup.mk (K := FractionRing R))

/-- The map from Cartier divisors to the Picard group is surjective: every line bundle
arises from a Cartier divisor. -/
theorem Prop22.cartier_to_pic_surjective :
    Function.Surjective (Prop22.cartierToPicHom R) := by
  apply Function.Surjective.comp (ClassGroup.equivPic R).surjective
  intro y
  induction y using Quotient.inductionOn' with
  | h a => exact ⟨a, by rw [← ClassGroup.Quot_mk_eq_mk]; rfl⟩

/-- The kernel of the Cartier-to-Picard homomorphism is exactly the image of the
principal-divisor map: `Pic(R) = DivC / principals`. -/
theorem Prop22.ker_cartier_to_pic :
    (Prop22.cartierToPicHom R).ker = (Prop22.principalHom R).range := by
  ext x
  simp only [MonoidHom.mem_ker, Prop22.cartierToPicHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (ClassGroup.equivPic R).injective,
    MonoidHom.mem_range]
  constructor
  · intro h
    have : (QuotientGroup.mk x : ClassGroup R) = 1 := by
      rwa [show (QuotientGroup.mk x : ClassGroup R) =
        ClassGroup.mk (K := FractionRing R) x from by
        rw [← ClassGroup.Quot_mk_eq_mk]; rfl]
    rwa [QuotientGroup.eq_one_iff] at this
  · intro h
    have : (QuotientGroup.mk x : ClassGroup R) = 1 := by
      rwa [QuotientGroup.eq_one_iff]
    rwa [show (QuotientGroup.mk x : ClassGroup R) =
      ClassGroup.mk (K := FractionRing R) x from by
      rw [← ClassGroup.Quot_mk_eq_mk]; rfl] at this

/-- Proposition 22: the class group of Cartier divisors is isomorphic to the Picard
group of line bundles, `ClassGroup R ≃* Pic R`. -/
def prop22_cartier_divisors_iso_line_bundles :
    ClassGroup R ≃* CommRing.Pic R :=
  ClassGroup.equivPic R

/-- Proposition 22 (existence): there is an isomorphism `ClassGroup R ≃* Pic R`. -/
theorem prop22_picard_iso_classGroup :
    Nonempty (ClassGroup R ≃* CommRing.Pic R) :=
  ⟨ClassGroup.equivPic R⟩

/-- Proposition 22 over Dedekind domains: `ClassGroup R ≃* Pic R`, expressing the
Picard group as Cartier divisors modulo principal divisors. -/
theorem prop22_picard_iso_cartier_quotient_geometric
    [IsDedekindDomain R] :
    Nonempty (ClassGroup R ≃* CommRing.Pic R) :=
  ⟨ClassGroup.equivPic R⟩

end
