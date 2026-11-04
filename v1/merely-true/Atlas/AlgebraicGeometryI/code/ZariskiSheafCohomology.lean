/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Category.Ring.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace

noncomputable section

namespace ZariskiSheafCohomology

/-- The lattice of open subsets of a topological space has a top element
(the whole space). -/
instance opensOrderTop (T : Type*) [TopologicalSpace T] : OrderTop (Opens T) where
  top := ⊤
  le_top _ := by simp

/-- Forgetful functor from commutative rings to additive abelian groups,
factored through the category of rings. -/
abbrev commRingToAddCommGrp : CommRingCat ⥤ AddCommGrpCat :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The structure sheaf of a scheme viewed as a sheaf of additive abelian
groups on the Zariski site. -/
def schemeAbSheaf (X : Scheme) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat :=
  (Sheaf.composeAndSheafify
    (Opens.grothendieckTopology X.toTopCat) commRingToAddCommGrp).obj X.sheaf

/-- The `n`-th Zariski sheaf cohomology of the structure sheaf of `X`. -/
def sheafCohomology (X : Scheme) (n : ℕ) : Type :=
  (schemeAbSheaf X).H n

/-- The sheaf cohomology groups inherit an additive abelian group structure. -/
instance sheafCohomology_addCommGroup (X : Scheme) (n : ℕ) :
    AddCommGroup (sheafCohomology X n) := by
  unfold sheafCohomology; infer_instance

/-- Specialization to affine schemes: the `n`-th Zariski cohomology of
`Spec R`. -/
def specCohomology (R : CommRingCat) (n : ℕ) : Type :=
  sheafCohomology (Scheme.Spec.obj (Opposite.op R)) n

/-- The affine sheaf cohomology groups carry an additive abelian group
structure. -/
instance specCohomology_addCommGroup (R : CommRingCat) (n : ℕ) :
    AddCommGroup (specCohomology R n) := by
  unfold specCohomology; infer_instance

/-- Degree-zero cohomology is identified with `Hom`-out of the constant sheaf
on `ℤ`, via the `Ext⁰` formalism. -/
def h0AddEquivHom (X : Scheme) :
    sheafCohomology X 0 ≃+
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ schemeAbSheaf X) :=
  Ext.addEquiv₀

/-- Adjunction equivalence: morphisms from the constant sheaf on `ℤ` to a
sheaf correspond to global sections of that sheaf. -/
def h0EquivSections (X : Scheme) :
    ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ schemeAbSheaf X) ≃
      (AddCommGrpCat.of (ULift ℤ) ⟶
        ((sheafSections (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
          (Opposite.op ⊤)).obj (schemeAbSheaf X)) :=
  (constantSheafAdj (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat
    Limits.isTerminalTop).homEquiv _ _

/-- The functor `F ↦ Hⁿ(X, F)` taking a sheaf to its `n`-th Zariski sheaf
cohomology. -/
def zariskiCohomologyFunctor (X : Scheme) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat ⥤ AddCommGrpCat :=
  Sheaf.cohomologyFunctor (Opens.grothendieckTopology X.toTopCat) n

/-- The Zariski cohomology functor is additive in its sheaf argument. -/
instance zariskiCohomologyFunctor_additive (X : Scheme) (n : ℕ) :
    (zariskiCohomologyFunctor X n).Additive := by
  unfold zariskiCohomologyFunctor; infer_instance

/-- If `F` is the zero sheaf, then all of its sheaf cohomology groups are
trivial. -/
theorem subsingleton_cohomology_of_isZero (X : Scheme)
    {F : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat}
    (h : Limits.IsZero F) (n : ℕ) : Subsingleton (F.H n) :=
  Sheaf.subsingleton_H_of_isZero h n

/-- The dimension `hⁿ(X) = dim_k Hⁿ(X, O_X)` of sheaf cohomology when the
cohomology group carries a `k`-vector-space structure. -/
def specH (k : Type*) [Field k] (X : Scheme) (n : ℕ)
    [Module k (sheafCohomology X n)] : ℕ :=
  Module.finrank k (sheafCohomology X n)

end ZariskiSheafCohomology

end
