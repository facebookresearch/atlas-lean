/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.ApartmentsCoxeter
import Atlas.Buildings.code.BNPair.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedSectionVars false

open ChamberComplex

namespace CoxeterMatrix

variable {B : Type*}

/-- A Coxeter matrix is indecomposable if its Coxeter graph (with edges
$\{s,t\}$ whenever $M_{st} \ne 2$) is connected: any partition of the
generating set into two nonempty subsets is joined by a non-commuting
generator pair. -/
def IsIndecomposable (M : CoxeterMatrix B) : Prop :=
  ∀ (S₁ S₂ : Set B),
    (∀ b, b ∈ S₁ ∨ b ∈ S₂) →
    (∀ b, ¬(b ∈ S₁ ∧ b ∈ S₂)) →
    S₁.Nonempty →
    S₂.Nonempty →
    ∃ s₁ ∈ S₁, ∃ s₂ ∈ S₂, M.M s₁ s₂ ≠ 2

/-- The cosine matrix $C$ of a Coxeter matrix $M$:
$C_{ij} = -\cos(\pi / M_{ij})$. This is the matrix of the standard symmetric
bilinear form used to test sphericity/affineness of $M$. -/
noncomputable def cosineMatrix (M : CoxeterMatrix B) : Matrix B B ℝ :=
  fun i j => -Real.cos (Real.pi / (M.M i j : ℝ))

/-- A Coxeter matrix $M$ is affine if its cosine matrix is positive semidefinite
but not positive definite. This characterises the affine Coxeter types
$\tilde A_n, \tilde B_n, \tilde C_n, \tilde D_n$, etc. -/
noncomputable def IsAffine (M : CoxeterMatrix B) : Prop :=
  M.cosineMatrix.PosSemidef ∧ ¬M.cosineMatrix.PosDef

end CoxeterMatrix

variable {V : Type*} [DecidableEq V]

namespace Building

/-- A building is affine if it has a Coxeter type whose Coxeter matrix is
indecomposable and affine. -/
def IsAffineBuilding (b : Building V) : Prop :=
  ∃ (ct : CoxeterTypeOfBuilding b),
    ct.matrix.IsIndecomposable ∧ ct.matrix.IsAffine

/-- A building is a tree if it is an affine building of rank one (a single
generator), i.e. type $\tilde A_1$. -/
def IsTree (b : Building V) : Prop :=
  ∃ (ct : CoxeterTypeOfBuilding b),
    ct.matrix.IsIndecomposable ∧ ct.matrix.IsAffine ∧
    Nonempty (ct.B_idx ≃ Fin 1)

end Building

/-- The Iwahori subgroup of a group $G$ from a BN-pair with indecomposable
affine Coxeter type: bundled data consisting of the BN-pair together with
the indecomposable affine hypotheses on its Coxeter matrix. -/
structure IwahoriSubgroup (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  indecomposable : M.IsIndecomposable
  affine : M.IsAffine

/-- The underlying subgroup of an Iwahori datum: the distinguished subgroup $B$
of the BN-pair. -/
def IwahoriSubgroup.toSubgroup {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (I : IwahoriSubgroup G M) : Subgroup G :=
  I.bnpair.B
