/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

open scoped Pointwise

namespace PlunneckeInequality

/-- The set `poly_K(A) = (A^K)^{⊕K} - (A^K)^{⊕K}`, i.e. the difference of the
`K`-fold iterated sumset of the `K`-fold product set `A^K`. This is the auxiliary
polynomial-growth set used in the Plünnecke / Bourgain–Katz–Tao expansion arguments. -/
def poly_k {G : Type*} [CommRing G] [DecidableEq G] (K : ℕ) (A : Finset G) : Finset G :=
  K • (A ^ K) - K • (A ^ K)

end PlunneckeInequality
