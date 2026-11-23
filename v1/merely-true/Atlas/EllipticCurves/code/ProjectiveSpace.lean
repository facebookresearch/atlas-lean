/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ProjectiveSpace

variable (n : ℕ) (k : Type*) [Field k]

/-- $n$-dimensional projective space $\mathbb{P}^n(k)$ over $k$, realised as the projectivization
of $k^{n+1}$. -/
abbrev Space : Type _ := Projectivization k (Fin (n + 1) → k)

/-- The projective point $[v_0 : \cdots : v_n] \in \mathbb{P}^n(k)$ associated to a nonzero
vector $v \in k^{n+1}$. -/
def mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : Space n k :=
  Projectivization.mk k v hv

/-- A choice of homogeneous coordinates representing a projective point. -/
def coord (P : Space n k) : Fin (n + 1) → k := P.rep

/-- Homogeneous coordinates of a projective point are nonzero. -/
theorem coord_ne_zero (P : Space n k) : coord n k P ≠ 0 :=
  Projectivization.rep_nonzero P

/-- Two nonzero vectors in $k^{n+1}$ determine the same projective point iff they differ
by a nonzero scalar. -/
theorem mk_eq_mk_iff (v w : Fin (n + 1) → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk n k v hv = mk n k w hw ↔ ∃ a : kˣ, a • w = v :=
  Projectivization.mk_eq_mk_iff k v w hv hw

/-- Variant of `mk_eq_mk_iff` allowing the scalar to range over $k$; since $w \neq 0$, the
scalar is automatically a unit. -/
theorem mk_eq_mk_iff' (v w : Fin (n + 1) → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk n k v hv = mk n k w hw ↔ ∃ a : k, a • w = v :=
  Projectivization.mk_eq_mk_iff' k v w hv hw

/-- Taking representative coordinates and forming a projective point recovers the original
projective point. -/
@[simp]
theorem mk_coord (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    Projectivization.mk k (coord n k (mk n k v hv)) (coord_ne_zero n k (mk n k v hv)) =
      mk n k v hv :=
  Projectivization.mk_rep (mk n k v hv)

end ProjectiveSpace

namespace ProjectiveSpace

variable (k : Type*) [Field k]

/-- The projective plane $\mathbb{P}^2(k)$. -/
abbrev Plane : Type _ := Space 2 k

/-- The projective line $\mathbb{P}^1(k)$. -/
abbrev Line : Type _ := Space 1 k


end ProjectiveSpace

end
