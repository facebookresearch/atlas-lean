/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory
import Atlas.TensorCategories.code.FittingLemmaLocalEnd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

/-- Derives the `HasLocalEndomorphismRings` structure on `C` from the Fitting-lemma hypothesis
that endomorphism rings of indecomposable objects are local, together with the assumption that
every projective object is indecomposable. -/
@[reducible]
def hasLocalEndRings_of_fitting
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Abelian C] [Linear k C]
    [inst : FiniteAbelianCategory.HasLocalEndOfIndecomposable k C]
    (h_indecomp : ∀ (P : C) [Projective P], Indecomposable P) :
    HasLocalEndomorphismRings C where
  isLocalRing_end P := inst.isLocalRing_end_of_indecomposable P (h_indecomp P)

/-- Derives the existence of projective covers of simple objects from the Fitting-lemma
hypothesis on local endomorphism rings of indecomposable projectives. -/
@[reducible]
def hasProjectiveCoversOfSimples_of_fitting
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Abelian C] [Linear k C]
    [FiniteAbelianCategory.HasLocalEndOfIndecomposable k C]
    (h_indecomp : ∀ (P : C) [Projective P], Indecomposable P) :
    HasProjectiveCoversOfSimples C :=
  @hasProjectiveCoversOfSimples_of_localEnd C _ _
    (hasLocalEndRings_of_fitting k C h_indecomp)

end CategoryTheory
