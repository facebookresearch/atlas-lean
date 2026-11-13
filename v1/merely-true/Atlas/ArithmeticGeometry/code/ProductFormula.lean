/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.ProductFormula

namespace NumberField

open NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem product_formula {x : K} (hx : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 :=
  prod_abs_eq_one hx

end NumberField
