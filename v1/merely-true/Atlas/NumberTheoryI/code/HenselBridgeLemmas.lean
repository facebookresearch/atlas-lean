/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.KroneckerWeber
import Mathlib.NumberTheory.Wilson

noncomputable section

open scoped Padic
open KroneckerWeber

namespace KroneckerWeber

lemma isPrimitiveRoot_mem_integralClosure
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    {L : Type*} [Field L] [Algebra ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    ζ ∈ integralClosure ℤ_[p] L :=
  (hζ.isIntegral hp.out.pos).tower_top




lemma geom_sum_prod_mem_integralClosure
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    {L : Type*} [Field L] [Algebra ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    geom_sum_prod ζ p ∈ integralClosure ℤ_[p] L := by
  simp only [geom_sum_prod]
  apply Subalgebra.prod_mem
  intro k _
  apply Subalgebra.sum_mem
  intro i _
  exact Subalgebra.pow_mem _ (isPrimitiveRoot_mem_integralClosure hζ) _

end KroneckerWeber
end
