/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness

noncomputable section

open IsLocalRing



/-- Helper: linear independence of the gradient vectors `(∂f_i/∂x_j(x))_j` implies
the Jacobian matrix has full row rank `m`. -/
theorem jacobian_rank_eq_of_linearIndependent
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hf_indep : LinearIndependent k
      (fun i : Fin m => (fun j : Fin n =>
        MvPolynomial.eval x (MvPolynomial.pderiv j (f i))))) :
    (jacobianMatrix f x).rank = m := by
  have h : LinearIndependent k (jacobianMatrix f x).row := by
    simp only [Matrix.row]
    exact hf_indep
  rw [LinearIndependent.rank_matrix h, Fintype.card_fin]

end
