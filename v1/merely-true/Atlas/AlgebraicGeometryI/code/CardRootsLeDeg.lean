/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card

open Polynomial
open scoped Classical

/-- A polynomial of degree `d` over an integral domain has at most `d` distinct roots. -/
theorem card_roots_le_deg {K : Type*} [CommRing K] [IsDomain K]
    (p : K[X]) : (p.roots.toFinset.card : ℕ) ≤ p.natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)
