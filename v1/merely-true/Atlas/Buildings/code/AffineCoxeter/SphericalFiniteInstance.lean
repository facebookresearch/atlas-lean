/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsCone

set_option linter.unusedSectionVars false

/-- The empty Coxeter matrix (no simple reflections) yields the trivial group, which is spherical
and finite. This is the base case of the `SphericalFiniteProperty` typeclass. -/
instance sphericalFiniteProperty_of_isEmpty {B : Type*} [DecidableEq B] [Fintype B]
    [IsEmpty B] (M : CoxeterMatrix B) : SphericalFiniteProperty M where
  finite_of_pos_def := fun _ => by
    unfold CoxeterMatrix.Group CoxeterMatrix.relationsSet
    apply Finite.of_surjective (QuotientGroup.mk' _)
    exact QuotientGroup.mk'_surjective _

/-- The trivial Coxeter type $A_0$ is spherical and finite (zero generators). -/
instance sphericalFiniteProperty_A0 : SphericalFiniteProperty (CoxeterMatrix.A 0) :=
  sphericalFiniteProperty_of_isEmpty _
