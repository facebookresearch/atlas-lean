/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.BlowupDefinition

open AlgebraicGeometry

namespace Blowup

variable {R : Type*} [CommRing R] (I : Ideal R)


/-- The exceptional locus `π⁻¹(C)` is a closed subset of `X`. -/
theorem exceptionalLocus_isClosed {X Y : Scheme} (π : X ⟶ Y)
    (C : TopologicalSpace.Closeds Y.toTopCat) :
    IsClosed ((exceptionalLocusSet π C : Set X.toTopCat)) :=
  (exceptionalLocusSet π C).isClosed'

/-- The proper transform unfolds to the closure of the preimage of `Z \ C`. -/
theorem properTransform_eq_closure {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    (properTransformSet π Z C : Set X.toTopCat) =
      closure (π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat))) :=
  rfl

/-- The proper transform is a closed subset of `X`. -/
theorem properTransform_isClosed {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    IsClosed (properTransformSet π Z C : Set X.toTopCat) :=
  (properTransformSet π Z C).isClosed'

/-- The underlying set of the exceptional locus is exactly the preimage of the center. -/
theorem exceptionalLocus_eq_preimage {X Y : Scheme} (π : X ⟶ Y)
    (C : TopologicalSpace.Closeds Y.toTopCat) :
    (exceptionalLocusSet π C : Set X.toTopCat) =
      π.base ⁻¹' (C : Set Y.toTopCat) :=
  rfl

end Blowup
