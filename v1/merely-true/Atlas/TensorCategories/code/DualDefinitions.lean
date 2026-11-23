/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

open CategoryTheory MonoidalCategory

/-- Definition 1.10.1 (EGNO): A right dual of an object `X` in a monoidal category `C`
is an object `X*` equipped with evaluation and coevaluation morphisms satisfying the
triangle identities. -/
abbrev Definition_1_10_1 {C : Type*} [Category C] [MonoidalCategory C] (X : C) :=
  HasRightDual X

/-- Definition 1.10.2 (EGNO): A left dual of an object `X` in a monoidal category `C`
is an object `*X` equipped with evaluation and coevaluation morphisms satisfying the
triangle identities. -/
abbrev Definition_1_10_2 {C : Type*} [Category C] [MonoidalCategory C] (X : C) :=
  HasLeftDual X

/-- Definition 1.10.11 (EGNO): A monoidal category `C` is called rigid if every object
has both a right dual and a left dual. -/
abbrev Definition_1_10_11 (C : Type*) [Category C] [MonoidalCategory C] :=
  RigidCategory C

/-- Short alias for `Definition_1_10_2` (left dual). -/
abbrev def_1_10_2 := @Definition_1_10_2

/-- Short alias for `Definition_1_10_11` (rigid monoidal category). -/
abbrev def_1_10_11 := @Definition_1_10_11
