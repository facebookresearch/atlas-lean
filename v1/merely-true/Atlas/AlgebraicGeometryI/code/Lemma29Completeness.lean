/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Lemma29Completeness

universe u


/-- The DVR valuative criterion: every injective map from a DVR to the
function field of `X` extends to a local ring map at some specialization
of the generic point (Lemma 29, completeness setting). -/
def SatisfiesDVRCriterion (X : Scheme.{u}) [IrreducibleSpace X] : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (φ : CommRingCat.of R ⟶ X.functionField) (_ : Function.Injective φ),
    ∃ (x : X) (hx : (genericPoint (X : TopCat) : X) ⤳ x),
      ∃ ψ : X.presheaf.stalk x ⟶ CommRingCat.of R,
        ψ ≫ φ = X.presheaf.stalkSpecializes hx





end Lemma29Completeness
