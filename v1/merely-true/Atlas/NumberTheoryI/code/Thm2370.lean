/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Ext

open CategoryTheory CochainComplex HomComplex Abelian

universe w v u

noncomputable def ext_well_defined
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {M A : C} (P Q : ProjectiveResolution M) (n : ℕ) :
    CohomologyClass P.cochainComplex ((singleFunctor C 0).obj A) n ≃+
    CohomologyClass Q.cochainComplex ((singleFunctor C 0).obj A) n :=
  P.extAddEquivCohomologyClass.symm.trans Q.extAddEquivCohomologyClass
