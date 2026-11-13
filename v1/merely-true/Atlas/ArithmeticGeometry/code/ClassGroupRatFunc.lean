/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped nonZeroDivisors

variable (k : Type*) [Field k]

/-- The polynomial ring $k[t]$ is a PID, so its ideal class group is trivial: $\mathrm{Cl}(k[t]) = 0$. -/
noncomputable instance Polynomial.classGroup_subsingleton :
    Subsingleton (ClassGroup (Polynomial k)) :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq card_classGroup_eq_one)
