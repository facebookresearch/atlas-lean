/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Module.Projective
import Atlas.AlgebraicTopologyI.code.FundamentalThm

namespace ProjectiveModules

/-- **Definition 22.2 (Projective module).**  An `R`-module `P` is
*projective* if it satisfies the lifting property: every surjection
`f : M → N` and every map `g : P → N` admit a lift `h : P → M` with
`f ∘ h = g`.  Equivalently, `P` is a direct summand of a free module.
Thin wrapper around Mathlib's `Module.Projective`. -/
abbrev IsProjectiveModule (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P]
    [Module R P] : Prop :=
  Module.Projective R P

end ProjectiveModules

namespace FundamentalHomologicalAlgebra

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The chain map produced by the **Fundamental Theorem of Homological
Algebra (Theorem 22.1)**: any map `f : Y → Z` between objects of an abelian
category lifts to a chain map between any projective resolution of `Y` and
any resolution of `Z` covering `f`.  See `lift_commutes` for the relation
to the augmentations and `liftUniqueUpToHomotopy` for uniqueness. -/
noncomputable def lift {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    P.complex ⟶ Q.complex :=
  FundamentalThm.lift f P Q

/-- The chain map `lift f P Q` covers `f`: composing it with the
augmentation of `Q` agrees with composing the augmentation of `P` with the
chain map associated to `f`.  This is the commutativity clause in the
Fundamental Theorem (Theorem 22.1). -/
theorem lift_commutes {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f :=
  FundamentalThm.lift_commutes f P Q

/-- **Uniqueness up to chain homotopy** in Theorem 22.1: any two chain maps
`g, h : P.complex → Q.complex` between a projective resolution `P` of `Y`
and a resolution `Q` of `Z`, both covering the same map `f : Y → Z`, are
chain homotopic.  Combined with `lift` this produces a well-defined map on
derived functors. -/
noncomputable def liftUniqueUpToHomotopy {Y Z : C} (f : Y ⟶ Z)
    {P : ProjectiveResolution Y} {Q : FundamentalThm.Resolution Z}
    (g h : P.complex ⟶ Q.complex)
    (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    Homotopy g h :=
  FundamentalThm.liftHomotopy f g h g_comm h_comm

/-- **Theorem 22.1 (Fundamental Theorem of Homological Algebra).**  Given a
map `f : Y → Z` in an abelian category, a projective resolution `P` of `Y`,
and any resolution `Q` of `Z`, there exists a chain map
`g : P.complex → Q.complex` covering `f` (i.e. with
`g ≫ Q.π = P.π ≫ (single₀).map f`); moreover any other chain map covering
`f` is chain homotopic to `g`.  This packaged form returns the lift,
together with the commutativity equation and the uniqueness statement, all
in a single bundled term. -/
noncomputable def fundamentalTheorem {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    { g : P.complex ⟶ Q.complex //
      g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f ∧
      ∀ h : P.complex ⟶ Q.complex,
        h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → Nonempty (Homotopy g h) } :=
  ⟨lift f P Q, lift_commutes f P Q, fun h hcomm =>
    ⟨liftUniqueUpToHomotopy f (lift f P Q) h (lift_commutes f P Q) hcomm⟩⟩

end FundamentalHomologicalAlgebra
