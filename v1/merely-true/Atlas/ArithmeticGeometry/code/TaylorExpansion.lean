/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Taylor

noncomputable section

open Polynomial

/-- Definition 8.5 (Taylor expansion): given a polynomial $f \in R[x]$ over a commutative
ring $R$ and a point $a \in R$, the Taylor expansion at $a$ is the polynomial obtained by
re-expanding $f$ in powers of $X - a$. Thin wrapper around `Polynomial.taylor`. -/
def taylorExpansion {R : Type*} [CommRing R] (a : R) (f : R[X]) : R[X] :=
  Polynomial.taylor a f


end
