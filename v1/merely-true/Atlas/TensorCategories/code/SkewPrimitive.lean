/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CoradicalFiltration

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R] [AddCommGroup H] [Module R H] [Coalgebra R H]

/-- Definition 1.24.6: an element `x` in a coalgebra is `(g, h)`-skew-primitive when its
comultiplication satisfies `Δ x = x ⊗ g + h ⊗ x`. -/
abbrev def_1_24_6 (g h x : H) : Prop :=
  IsSkewPrimitive (R := R) g h x
