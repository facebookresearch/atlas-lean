/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Rings

theorem zero_eq_one_of_zero_isUnit (R : Type*) [Ring R] (h : IsUnit (0 : R)) :
    (0 : R) = 1 := by
  obtain ⟨u, hu⟩ := h
  have : (0 : R) * ↑u⁻¹ = 1 := by
    rw [← hu]
    exact u.val_inv
  rwa [zero_mul] at this
