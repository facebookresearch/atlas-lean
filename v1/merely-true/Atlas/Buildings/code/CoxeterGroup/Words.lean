/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

set_option linter.unusedSectionVars false

namespace CoxeterWords

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Convenience abbreviation for the Coxeter group associated to a Coxeter matrix $M$. -/
noncomputable abbrev CoxGroup (M : CoxeterMatrix B) := M.Group

/-- Convenience abbreviation for the canonical Coxeter system on `M.Group`. -/
noncomputable abbrev coxeterSystem (M : CoxeterMatrix B) : CoxeterSystem M M.Group :=
  M.toCoxeterSystem

/-- The $i$-th simple Coxeter generator $s_i$ of the Coxeter group. -/
noncomputable abbrev gen (M : CoxeterMatrix B) (i : B) : M.Group :=
  M.toCoxeterSystem.simple i

/-- The product $s_{i_1} \cdots s_{i_k}$ of the simple generators specified by the word $w$. -/
noncomputable abbrev wordProd (M : CoxeterMatrix B) (w : List B) : M.Group :=
  M.toCoxeterSystem.wordProd w

/-- The Coxeter length $\ell(w)$ of a group element. -/
noncomputable abbrev wordLength (M : CoxeterMatrix B) (w : M.Group) : ℕ :=
  M.toCoxeterSystem.length w

end CoxeterWords
