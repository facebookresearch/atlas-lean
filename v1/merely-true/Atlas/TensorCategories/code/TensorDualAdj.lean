/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u

namespace TensorDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]




/-- Proposition 1.10.9(i), first equation: the natural Hom-adjunction
`Hom(U ⊗ V, W) ≃ Hom(U, W ⊗ Vᘁ)` when `V` has a right dual. -/
noncomputable def prop_1_10_9_i_eq1 (V : C) [HasRightDual V] (U W : C) :
    (U ⊗ V ⟶ W) ≃ (U ⟶ W ⊗ Vᘁ) :=
  tensorRightHomEquiv U V Vᘁ W

/-- Proposition 1.10.9(i), second equation: the natural Hom-adjunction
`Hom(Vᘁ ⊗ U, W) ≃ Hom(U, V ⊗ W)` when `V` has a right dual. -/
noncomputable def prop_1_10_9_i_eq2 (V : C) [HasRightDual V] (U W : C) :
    (Vᘁ ⊗ U ⟶ W) ≃ (U ⟶ V ⊗ W) :=
  tensorLeftHomEquiv U V Vᘁ W

/-- Proposition 1.10.9(i): the functor `- ⊗ V` is left adjoint to `- ⊗ Vᘁ` when `V` has a right dual. -/
noncomputable def prop_1_10_9_i_adj_right (V : C) [HasRightDual V] :
    tensorRight V ⊣ tensorRight Vᘁ :=
  tensorRightAdjunction V Vᘁ

/-- Proposition 1.10.9(i): the functor `Vᘁ ⊗ -` is left adjoint to `V ⊗ -` when `V` has a right dual. -/
noncomputable def prop_1_10_9_i_adj_left (V : C) [HasRightDual V] :
    tensorLeft Vᘁ ⊣ tensorLeft V :=
  tensorLeftAdjunction V Vᘁ

/-- Proposition 1.10.9(ii), first equation: the natural Hom-adjunction
`Hom(U ⊗ ᘁV, W) ≃ Hom(U, W ⊗ V)` when `V` has a left dual. -/
noncomputable def prop_1_10_9_ii_eq1 (V : C) [HasLeftDual V] (U W : C) :
    (U ⊗ (ᘁV) ⟶ W) ≃ (U ⟶ W ⊗ V) :=
  tensorRightHomEquiv U (ᘁV) V W

/-- Proposition 1.10.9(ii), second equation: the natural Hom-adjunction
`Hom(V ⊗ U, W) ≃ Hom(U, ᘁV ⊗ W)` when `V` has a left dual. -/
noncomputable def prop_1_10_9_ii_eq2 (V : C) [HasLeftDual V] (U W : C) :
    (V ⊗ U ⟶ W) ≃ (U ⟶ (ᘁV) ⊗ W) :=
  tensorLeftHomEquiv U (ᘁV) V W

/-- Proposition 1.10.9(ii): the functor `- ⊗ ᘁV` is left adjoint to `- ⊗ V` when `V` has a left dual. -/
noncomputable def prop_1_10_9_ii_adj_right (V : C) [HasLeftDual V] :
    tensorRight (ᘁV) ⊣ tensorRight V :=
  tensorRightAdjunction (ᘁV) V

/-- Proposition 1.10.9(ii): the functor `V ⊗ -` is left adjoint to `ᘁV ⊗ -` when `V` has a left dual. -/
noncomputable def prop_1_10_9_ii_adj_left (V : C) [HasLeftDual V] :
    tensorLeft V ⊣ tensorLeft (ᘁV) :=
  tensorLeftAdjunction (ᘁV) V

/-- Proposition 1.10.9: the pair of tensor-dual adjunctions associated to a right dualizable object,
packaging both the right-tensor and left-tensor adjunctions in a single statement. -/
noncomputable def prop_1_10_9 (V : C) [HasRightDual V] :
    (tensorRight V ⊣ tensorRight Vᘁ) × (tensorLeft Vᘁ ⊣ tensorLeft V) :=
  ⟨tensorRightAdjunction V Vᘁ, tensorLeftAdjunction V Vᘁ⟩

end TensorDual
