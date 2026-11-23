/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Basic

noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


/-- A simplified placeholder model for the Cartier divisor group on `X`: integer-valued functions
on the underlying points. -/
def CartierDivisorGroup (X : Scheme.{u}) : Type u := X.carrier → ℤ

namespace CartierDivisorGroup

/-- Abelian group structure on `CartierDivisorGroup`, pointwise. -/
instance instAddCommGroup (X : Scheme.{u}) : AddCommGroup (CartierDivisorGroup X) :=
  Pi.addCommGroup

/-- Pullback of (model) Cartier divisors along a morphism `f : X → Y`: compose with the
underlying continuous map. -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CartierDivisorGroup Y →+ CartierDivisorGroup X where
  toFun D := D ∘ f.base
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Placeholder predicate: a (model) divisor is principal. Always `True` in this skeleton. -/
def isPrincipal {X : Scheme.{u}} (_D : CartierDivisorGroup X) : Prop :=
  True

/-- Functoriality of divisor pullback: `(f ∘ g)^* = f^* ∘ g^*`. -/
theorem pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : CartierDivisorGroup Z) :
    pullback (f ≫ g) D = pullback f (pullback g D) := by
  funext x
  simp [pullback]

/-- Pullback along the identity is the identity. -/
theorem pullback_id {X : Scheme.{u}} (D : CartierDivisorGroup X) :
    pullback (𝟙 X) D = D := by
  funext x
  simp [pullback]

end CartierDivisorGroup


/-- An `S`-point of a scheme `X` over `S`: a section of the structure morphism `p : X → S`. -/
structure SPoint {S X : Scheme.{u}} (p : X ⟶ S) where
  morphism : S ⟶ X
  isSection : morphism ≫ p = 𝟙 S

/-- A connected variety over `S`: an integral, topologically connected scheme equipped with a
structure morphism to `S`. Used to parametrize algebraic families. -/
structure ConnectedVariety (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ S
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isConnected : ConnectedSpace toScheme


/-- Two divisors `D₁`, `D₂` on `X` are *algebraically equivalent* if there is a connected
parameter scheme `T` over `S`, a divisor `𝒟` on `X ×_S T`, and two `S`-points `t₁, t₂` of `T`
whose pullbacks of `𝒟` are `D₁` and `D₂`. -/
def IsAlgebraicallyEquivalent {S X : Scheme.{u}} (sX : X ⟶ S)
    (D₁ D₂ : CartierDivisorGroup X) : Prop :=
  ∃ (T : ConnectedVariety S)
    (𝒟 : CartierDivisorGroup (pullback sX T.structureMorphism))
    (t₁ t₂ : SPoint T.structureMorphism),

    let ι₁ := pullback.lift (𝟙 X) (sX ≫ t₁.morphism)
      (by rw [Category.id_comp, Category.assoc, t₁.isSection, Category.comp_id])
    let ι₂ := pullback.lift (𝟙 X) (sX ≫ t₂.morphism)
      (by rw [Category.id_comp, Category.assoc, t₂.isSection, Category.comp_id])

    CartierDivisorGroup.pullback ι₁ 𝒟 = D₁ ∧
    CartierDivisorGroup.pullback ι₂ 𝒟 = D₂

/-- A divisor is *algebraically equivalent to zero* if it is algebraically equivalent to the zero
divisor. The subgroup of such divisors is the kernel of the map to the Néron-Severi group. -/
def IsAlgEquivZero {S X : Scheme.{u}} (sX : X ⟶ S)
    (D : CartierDivisorGroup X) : Prop :=
  IsAlgebraicallyEquivalent sX D 0

/-- An *irreducible complete curve* over `S`: an integral scheme together with a proper structure
morphism to `S`. -/
structure IrredCompleteCurve (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ S
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isProper : IsProper structureMorphism

/-- A morphism of `S`-curves: a scheme morphism over `S`. -/
structure CurveMorphism {S : Scheme.{u}}
    (X Y : IrredCompleteCurve S) where
  morphism : X.toScheme ⟶ Y.toScheme
  compatible : morphism ≫ Y.structureMorphism = X.structureMorphism

/-- A morphism of curves is *constant* if it is not dominant. -/
def CurveMorphism.IsConstant {S : Scheme.{u}}
    {X Y : IrredCompleteCurve S} (f : CurveMorphism X Y) : Prop :=
  ¬ IsDominant f.morphism



end AlgebraicEquivalence
