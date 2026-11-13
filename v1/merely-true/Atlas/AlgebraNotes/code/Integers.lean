/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Integers

theorem ideal_span_pair_eq_span_gcd (a b : ℤ) :
    Ideal.span {a, b} = Ideal.span {(Int.gcd a b : ℤ)} := by
  rw [Int.coe_gcd]
  exact (span_gcd a b).symm
