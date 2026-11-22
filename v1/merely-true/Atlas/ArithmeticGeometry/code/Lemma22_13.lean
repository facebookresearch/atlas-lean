/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Theorem22_11

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

section Lemma22_13
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]


end Lemma22_13
