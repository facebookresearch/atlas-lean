/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal

open CategoryTheory MonoidalCategory AlgebraicTopology

noncomputable section

namespace EilenbergZilber

universe u

/-- The singular chain complex of a topological space $X$ with coefficients in an
$R$-module $M$, viewed as a chain complex of $R$-modules. -/
noncomputable def singularChainComplex
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).obj X










end EilenbergZilber
