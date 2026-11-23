/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace RealNumbers

/-- Triangle inequality for the absolute value on `ℝ`: `|x + y| ≤ |x| + |y|`
for all real numbers `x` and `y`. -/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le x y

end RealNumbers
