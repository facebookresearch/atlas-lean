/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans

namespace AlgebraicTopologyI

/-- **Definition 3.2 (Isomorphism).**  An isomorphism in a category `C`, in
the sense of Miller's *Lectures on Algebraic Topology I*: a morphism with a
two-sided inverse, packaged as a structure recording both the morphism and
its inverse together with the inversion equations.  This is a thin wrapper
around Mathlib's `CategoryTheory.Iso`. -/
abbrev Iso := @CategoryTheory.Iso

/-- The Mathlib class witnessing that a morphism `f` *is* an isomorphism in
the sense of Definition 3.2, i.e. there exists a two-sided inverse.  This is
a thin wrapper around `CategoryTheory.IsIso`. -/
abbrev IsIso := @CategoryTheory.IsIso

open CategoryTheory

/-- **Definition 3.5 (Natural transformation).**  A natural transformation
`θ : F ⟶ G` between two functors `F, G : C ⥤ D`, in the sense of Miller's
*Lectures on Algebraic Topology I*: a family of morphisms `θ_X : F X ⟶ G X`
satisfying the naturality squares.  This is a thin wrapper around Mathlib's
`CategoryTheory.NatTrans`. -/
abbrev NatTrans := @CategoryTheory.NatTrans

end AlgebraicTopologyI
