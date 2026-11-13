/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.PivotalSpherical
import Atlas.TensorCategories.code.VecInstances

import Atlas.TensorCategories.code.VecPivotalConcrete
import Atlas.TensorCategories.code.VecSphericalConcrete

open CategoryTheory Module TensorCategories VecInstances MonoidalCategory Category

universe u

/-- The canonical double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`,
realized via the linear-algebraic evaluation equivalence. -/
noncomputable def vecDoubleDualIso (k : Type u) [Field k] (V : FGModuleCat k) :
    V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

variable (k : Type u) [Field k]

section PivotalSphericalInstances

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory
attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory
attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000 in
/-- `Vec k = FGModuleCat k` is a pivotal category, with pivotal structure given by
the canonical double-dual isomorphism (Definition 1.38.2). -/
noncomputable instance : PivotalCategory (Vec k) :=
  vecPivotalCategoryInstance k

set_option maxHeartbeats 800000 in
/-- `Vec k` is a spherical category (Definition 1.39.1): the pivotal dimension of any
object equals the pivotal dimension of its dual. -/
noncomputable instance : SphericalCategory (Vec k) where
  spherical := fun V => by

    show TensorCategories.pivotalDimension (Vec k) V =
         TensorCategories.pivotalDimension (Vec k) (Vᘁ)

    change TensorCategories.leftQuantumTrace (Vec k) (PivotalCategory.pivotalIso V).hom =
           TensorCategories.leftQuantumTrace (Vec k) (PivotalCategory.pivotalIso (Vᘁ)).hom

    exact vec_spherical_condition k V

end PivotalSphericalInstances
