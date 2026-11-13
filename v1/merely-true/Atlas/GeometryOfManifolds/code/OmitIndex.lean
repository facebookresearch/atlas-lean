/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.Fin.Basic

/-- Given a $(p+1)$-tuple `vs` and an index $i$, returns the $p$-tuple obtained by
omitting the $i$-th entry, used in defining the alternating expansions of forms. -/
def omitIndex {α : Type*} {p : ℕ} (i : Fin (p + 1)) (vs : Fin (p + 1) → α) : Fin p → α :=
  vs ∘ i.succAbove

/-- The alternating sign $(-1)^i$ appearing in the Koszul/Cartan formulas for
exterior derivative, Lie derivative, and similar antisymmetric expansions. -/
def alternatingSign {p : ℕ} (i : Fin (p + 1)) : ℤ := (-1) ^ (i : ℕ)
