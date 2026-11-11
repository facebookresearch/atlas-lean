/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff

noncomputable section

open scoped Classical

namespace WalkCountFormula

theorem iterU_liftU_comm (n : ℕ) (f : YoungDiagram →₀ ℤ) :
    iterU n (liftU f) = liftU (iterU n f) := by
  show (liftU ^ n : Module.End ℤ _) (liftU f) =
      liftU ((liftU ^ n : Module.End ℤ _) f)
  have h : (liftU ^ n : Module.End ℤ _) * liftU =
      liftU * (liftU ^ n : Module.End ℤ _) :=
    pow_mul_comm' liftU n
  show ((liftU ^ n : Module.End ℤ _) * liftU) f =
      (liftU * (liftU ^ n : Module.End ℤ _)) f
  rw [h]

end WalkCountFormula

end
