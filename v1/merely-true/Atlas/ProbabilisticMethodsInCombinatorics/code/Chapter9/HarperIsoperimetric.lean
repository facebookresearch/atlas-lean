/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
set_option maxHeartbeats 800000

open Finset

namespace HarperIsoperimetric

/-- The Hamming cube $\{0,1\}^n$, modeled as functions `Fin n → Bool`. -/
abbrev HammingCube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Hamming distance between two points of $\{0,1\}^n$: number of coordinates at which they differ. -/
def hammingDist (x y : HammingCube n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- The closed Hamming ball of radius $r$ centered at $c$: the set of points $x$ with
$d_H(x, c) \leq r$. -/
def hammingBallFinset (c : HammingCube n) (r : ℕ) : Finset (HammingCube n) :=
  Finset.univ.filter fun x => hammingDist x c ≤ r

/-- A subset $B$ of the Hamming cube is a Hamming ball if $B = B(c, r)$ for some center $c$
and radius $r$. -/
def IsHammingBall (B : Finset (HammingCube n)) : Prop :=
  ∃ c : HammingCube n, ∃ r : ℕ, B = hammingBallFinset c r

/-- The $t$-Hamming expansion of $A$: all points at Hamming distance at most $t$ from some
element of $A$, i.e. $A_t = \{x : d_H(x, A) \leq t\}$. -/
def hammingExpansion (A : Finset (HammingCube n)) (t : ℕ) : Finset (HammingCube n) :=
  Finset.univ.filter fun x => ∃ a ∈ A, hammingDist x a ≤ t



end HarperIsoperimetric
