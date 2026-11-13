/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A scheme X is an algebraic variety over a locally Noetherian base S if it is
reduced, separated, of locally finite type and quasi-compact over S. -/
class IsAlgebraicVariety (X : Scheme.{u}) [X.Over S] [IsLocallyNoetherian S] : Prop where
  isReduced : IsReduced X
  isSeparated : X.IsSeparated
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ S)
  quasiCompact : QuasiCompact (X ↘ S)

attribute [instance] IsAlgebraicVariety.isReduced
attribute [instance] IsAlgebraicVariety.isSeparated
attribute [instance] IsAlgebraicVariety.locallyOfFiniteType
attribute [instance] IsAlgebraicVariety.quasiCompact

/-- An open subscheme inherits the structure morphism to S via composition with the
inclusion U ↪ X. -/
instance openSubschemeOver (X : Scheme.{u}) [X.Over S] (U : X.Opens) :
    (↑U : Scheme).Over S :=
  OverClass.ofHom (U.ι ≫ (X ↘ S))

/-- Open subschemes of reduced schemes are reduced. -/
instance isReduced_openSubscheme (X : Scheme.{u}) [IsReduced X] (U : X.Opens) :
    IsReduced (↑U : Scheme) :=
  inferInstance

/-- Separatedness descends to open subschemes. -/
lemma isSeparated_openSubscheme (X : Scheme.{u}) [X.IsSeparated] (U : X.Opens) :
    Scheme.IsSeparated (↑U : Scheme) := by
  constructor
  rw [show terminal.from (↑U : Scheme) = U.ι ≫ terminal.from X from terminal.hom_ext _ _]
  infer_instance

/-- Local finite type descends to open subschemes. -/
lemma locallyOfFiniteType_openSubscheme (X : Scheme.{u}) [X.Over S] (U : X.Opens)
    [LocallyOfFiniteType (X ↘ S)] :
    LocallyOfFiniteType ((↑U : Scheme) ↘ S) := by
  show LocallyOfFiniteType (U.ι ≫ (X ↘ S))
  infer_instance

/-- Quasi-compactness over S descends to open subschemes when X is locally Noetherian
of finite type over S. -/
lemma quasiCompact_openSubscheme (X : Scheme.{u}) [X.Over S] (U : X.Opens)
    [IsLocallyNoetherian S] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)] :
    QuasiCompact ((↑U : Scheme) ↘ S) := by
  show QuasiCompact (U.ι ≫ (X ↘ S))
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  infer_instance

/-- An open subscheme of an algebraic variety is again an algebraic variety
(Corollary 4, Lecture 2). -/
theorem isAlgebraicVariety_openSubscheme
    (X : Scheme.{u}) [X.Over S] [IsLocallyNoetherian S]
    [hX : IsAlgebraicVariety (S := S) X] (U : X.Opens) :
    @IsAlgebraicVariety S (↑U : Scheme) (openSubschemeOver X U) ‹_› where
  isReduced := isReduced_openSubscheme X U
  isSeparated := isSeparated_openSubscheme X U
  locallyOfFiniteType := locallyOfFiniteType_openSubscheme X U
  quasiCompact := quasiCompact_openSubscheme X U

end AlgebraicGeometry
