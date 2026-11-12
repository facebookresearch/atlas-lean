/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic

open scoped LinearAlgebra.Projectivization

/-- Projective `n`-space `P^n(k)` as the projectivization of `k^{n+1}`. -/
def ProjectiveSpace (k : Type*) [DivisionRing k] (n : ℕ) : Type _ :=
  Projectivization k (Fin (n + 1) → k)

namespace ProjectiveSpace

variable {k : Type*} [DivisionRing k] {n : ℕ}

/-- Form the projective point `[v]` in `P^n(k)` from a nonzero vector `v ∈ k^{n+1}`. -/
def mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : ProjectiveSpace k n :=
  Projectivization.mk k v hv

/-- The quotient map `(k^{n+1} \ {0}) → P^n(k)` sending a nonzero vector to its line. -/
def quotientMap : { v : Fin (n + 1) → k // v ≠ 0 } → ProjectiveSpace k n :=
  Projectivization.mk' k

/-- Two nonzero vectors define the same projective point iff they differ by a nonzero
scalar (unit version). -/
theorem mk_eq_mk_iff (v w : Fin (n + 1) → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ a : kˣ, a • w = v :=
  Projectivization.mk_eq_mk_iff k v w hv hw

/-- Two nonzero vectors define the same projective point iff they differ by a scalar
(field-element version). -/
theorem mk_eq_mk_iff' (v w : Fin (n + 1) → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ a : k, a • w = v :=
  Projectivization.mk_eq_mk_iff' k v w hv hw

/-- The quotient map `(k^{n+1} \ {0}) → P^n(k)` is surjective. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap (k := k) (n := n)) :=
  Quotient.mk''_surjective

/-- A choice of representative vector for a projective point. -/
noncomputable def rep (p : ProjectiveSpace k n) : Fin (n + 1) → k :=
  Projectivization.rep p

/-- The chosen representative of a projective point is nonzero. -/
theorem rep_nonzero (p : ProjectiveSpace k n) : rep p ≠ 0 :=
  Projectivization.rep_nonzero p

/-- Forming a projective point from its chosen representative recovers the original point. -/
@[simp]
theorem mk_rep (p : ProjectiveSpace k n) : mk (rep p) (rep_nonzero p) = p :=
  Projectivization.mk_rep p

/-- Projective `n`-space `P^n(k)` is nonempty. -/
instance : Nonempty (ProjectiveSpace k n) := by
  have : Nontrivial (Fin (n + 1) → k) := Pi.nontrivial
  exact inferInstanceAs (Nonempty (Projectivization k (Fin (n + 1) → k)))

end ProjectiveSpace
