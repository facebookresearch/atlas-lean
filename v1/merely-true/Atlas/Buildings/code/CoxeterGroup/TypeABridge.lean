/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Matrix
import Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem
import Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper

namespace TypeABridge

/-- The explicit numeric matrix for the type-$A$ Coxeter system on $\operatorname{Fin}(n)$. -/
def glnCoxeterMatrixA (n : ℕ) : Matrix (Fin n) (Fin n) ℕ := fun i j =>
  if i = j then 1
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3
  else 2

/-- The bare matrix `glnCoxeterMatrixA n` agrees with the underlying matrix of
`CoxeterMatrix.A n`. -/
theorem glnCoxeterMatrixA_eq_typeA (n : ℕ) :
    glnCoxeterMatrixA n = (CoxeterMatrix.A n).M := by
  ext i j
  simp only [glnCoxeterMatrixA, CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
      simp [hadj, hadj']
    · have hadj' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        intro h; exact hadj h.symm
      simp [hadj, hadj']

end TypeABridge
