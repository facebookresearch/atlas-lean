/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers

namespace Definition_5_1

variable (p : ℕ) [Fact p.Prime]

/-- Definition 5.1: the field of $p$-adic numbers $\mathbb{Q}_p$ is the field of fractions of the
ring of $p$-adic integers $\mathbb{Z}_p$. Witnessed by `PadicInt.isFractionRing`. -/
theorem padic_isFractionRing : IsFractionRing ℤ_[p] ℚ_[p] :=
  PadicInt.isFractionRing


end Definition_5_1
