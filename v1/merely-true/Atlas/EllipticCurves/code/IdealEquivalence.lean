/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.ComplexMultiplication

namespace IdealEquivalence

open ComplexLattice Pointwise

noncomputable section

/-- Two proper ideals `L₁`, `L₂` of an order `𝒪 ⊆ ℂ` are equivalent if they are
equivalent as complex lattices in the sense of `ComplexLattice.IsEquivalent`. -/
def IsEquivalent (𝒪 : Subring ℂ) (L₁ L₂ : ComplexLattice.ProperIdeal 𝒪) : Prop :=
  ComplexLattice.IsEquivalent 𝒪 L₁.val L₂.val

/-- Reflexivity of ideal equivalence: every proper ideal is equivalent to itself. -/
theorem IsEquivalent.refl (𝒪 : Subring ℂ) (L : ComplexLattice.ProperIdeal 𝒪) :
    IsEquivalent 𝒪 L L :=
  ComplexLattice.IsEquivalent.refl 𝒪 L.val

/-- Symmetry of ideal equivalence: `L₁ ~ L₂` implies `L₂ ~ L₁`. -/
theorem IsEquivalent.symm {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice.ProperIdeal 𝒪}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsEquivalent 𝒪 L₂ L₁ :=
  ComplexLattice.IsEquivalent.symm h

/-- Transitivity of ideal equivalence: `L₁ ~ L₂` and `L₂ ~ L₃` imply `L₁ ~ L₃`. -/
theorem IsEquivalent.trans {𝒪 : Subring ℂ} {L₁ L₂ L₃ : ComplexLattice.ProperIdeal 𝒪}
    (h₁₂ : IsEquivalent 𝒪 L₁ L₂) (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
    IsEquivalent 𝒪 L₁ L₃ :=
  ComplexLattice.IsEquivalent.trans h₁₂ h₂₃

/-- `IsEquivalent 𝒪` is an equivalence relation on proper ideals of `𝒪`. -/
theorem isEquivalent_equivalence (𝒪 : Subring ℂ) :
    Equivalence (IsEquivalent 𝒪) :=
  ⟨IsEquivalent.refl 𝒪, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The setoid on proper ideals of `𝒪` whose equivalence relation is ideal
equivalence. Quotienting by this setoid produces the ideal class group. -/
def properIdealSetoid (𝒪 : Subring ℂ) : Setoid (ComplexLattice.ProperIdeal 𝒪) where
  r := IsEquivalent 𝒪
  iseqv := isEquivalent_equivalence 𝒪

/-- The ideal class group of an order `𝒪 ⊆ ℂ`, defined as the quotient of the
set of proper ideals by ideal equivalence. -/
def IdealClassGroup (𝒪 : Subring ℂ) : Type :=
  Quotient (properIdealSetoid 𝒪)

/-- The canonical map sending a proper ideal `L` to its class in the ideal
class group. -/
def IdealClassGroup.mk (𝒪 : Subring ℂ) (L : ComplexLattice.ProperIdeal 𝒪) :
    IdealClassGroup 𝒪 :=
  Quotient.mk (properIdealSetoid 𝒪) L

/-- Two proper ideals have the same ideal class iff they are equivalent. -/
theorem IdealClassGroup.mk_eq_mk_iff (𝒪 : Subring ℂ)
    (L₁ L₂ : ComplexLattice.ProperIdeal 𝒪) :
    IdealClassGroup.mk 𝒪 L₁ = IdealClassGroup.mk 𝒪 L₂ ↔
      IsEquivalent 𝒪 L₁ L₂ :=
  Quotient.eq (r := properIdealSetoid 𝒪)

/-- The ideal class group built from `IsEquivalent` agrees with the analogous
quotient `ComplexLattice.IdealClassGroup 𝒪` defined in the lattice setting. -/
def idealClassGroupEquiv (𝒪 : Subring ℂ) :
    IdealClassGroup 𝒪 ≃ ComplexLattice.IdealClassGroup 𝒪 :=
  Quotient.congr (Equiv.refl _) (fun _ _ => ⟨id, id⟩)



/-- The class number of an order `𝒪 ⊆ ℂ`, defined as the cardinality of its
ideal class group. -/
noncomputable def classNumber (𝒪 : Subring ℂ) : ℕ :=
  Nat.card (IdealClassGroup 𝒪)

end

end IdealEquivalence
