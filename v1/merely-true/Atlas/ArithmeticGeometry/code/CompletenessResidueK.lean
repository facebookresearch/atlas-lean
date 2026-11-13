/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
universe u

open AlgebraicGeometry.CompletenessValuationCriterion

def HasResidueFieldK {k : Type u} [Field k] {V : AlgVariety k} (R : ValRingOver V) : Prop :=
  ∃ (Φ : R.valSub →+* k),
    (RingHom.ker Φ = IsLocalRing.maximalIdeal R.valSub) ∧
    Function.Surjective Φ

def SatisfiesValuationCriterionResidueK {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    HasResidueFieldK R →
    ∃ P : Z.toVariety.carrier, localRing_le P R

