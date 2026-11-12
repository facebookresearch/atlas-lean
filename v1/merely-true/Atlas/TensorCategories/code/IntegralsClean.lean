/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra

set_option autoImplicit false

universe u v

namespace Def1521

variable (k : Type u) [CommRing k]

/-- A left integral in `H` is an element `I` such that `x * I = ε(x) • I` for every
`x ∈ H`, where `ε` is the counit (Definition 1.52.1). -/
structure IsLeftIntegral (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H] (I : H) : Prop where
  integral_prop : ∀ (x : H), x * I = Coalgebra.counit (R := k) x • I

/-- A right integral in `H` is an element `I` such that `I * x = ε(x) • I` for every
`x ∈ H` (Definition 1.52.1). -/
structure IsRightIntegral (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H] (I : H) : Prop where
  integral_prop : ∀ (x : H), I * x = Coalgebra.counit (R := k) x • I

/-- Named alias for Definition 1.52.1 (left integrals in an algebra with counit). -/
def Def_1_52_1_IsLeftIntegral := @IsLeftIntegral

/-- Named alias for Definition 1.52.1 (right integrals in an algebra with counit). -/
def Def_1_52_1_IsRightIntegral := @IsRightIntegral

end Def1521
