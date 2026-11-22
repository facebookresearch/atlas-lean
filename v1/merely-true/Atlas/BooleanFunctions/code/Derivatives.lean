/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Definitions
import Mathlib.Data.Fin.Tuple.Basic

namespace BooleanFourier

noncomputable def discreteDerivative {n : ℕ} (f : BoolFn (n + 1))
    (i : Fin (n + 1)) : BoolFn n :=
  fun y => (1 / 2 : ℝ) * (f (Fin.insertNth i true y) - f (Fin.insertNth i false y))

end BooleanFourier
