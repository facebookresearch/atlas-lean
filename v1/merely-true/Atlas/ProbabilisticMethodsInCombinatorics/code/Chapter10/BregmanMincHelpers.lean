/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Real.Basic

open Finset Matrix BigOperators Equiv Classical

noncomputable section

namespace BregmanMinc

/-- $N_i(A, \sigma, \tau)$: number of columns $j$ such that $A_{ij} = 1$ and no earlier
row in the $\tau$-ordering (i.e., $\tau^{-1}(m) < \tau^{-1}(i)$) has $\sigma(m) = j$.
This counts the available choices at row $i$ in the Brégman-Minc proof. -/
def N_i {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ τ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n =>
    A i j = 1 ∧ ∀ m : Fin n, τ.symm m < τ.symm i → σ m ≠ j)).card

section PermanentCounting

end PermanentCounting

section TreeIdentity


end TreeIdentity

end BregmanMinc
end
