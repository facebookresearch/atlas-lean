/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.AdjoinRoot

/-- Algebra isomorphism resolving a nodal singularity: the quotient
`k[X][Y] / ⟨Y - C(X² - 1)⟩` is isomorphic (over `k[X]`) to `k[X]`. -/
noncomputable def nodeResolveIso (k : Type*) [CommRing k] :
    (Polynomial (Polynomial k) ⧸ Ideal.span
      {Polynomial.X - Polynomial.C ((Polynomial.X : Polynomial k) ^ 2 - 1)})
    ≃ₐ[Polynomial k] Polynomial k :=
  Polynomial.quotientSpanXSubCAlgEquiv (Polynomial.X ^ 2 - 1)

/-- The dimension of the fibre over the origin of the node `X² - 1 = 0` is `2`. -/
theorem fiber_origin_dim (k : Type*) [Field k] :
    Module.finrank k
      (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2 - 1}) = 2 := by
  rw [finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_X_pow_sub_C
