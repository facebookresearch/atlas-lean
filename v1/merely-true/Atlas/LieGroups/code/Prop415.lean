/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

noncomputable section

open scoped Manifold Topology
open MeasureTheory

structure ContinuousRepresentation (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] where
  toMonoidHom : G →* (V →L[ℂ] V)
  continuous_action : Continuous (fun p : G × V => (toMonoidHom p.1) p.2)

namespace ContinuousRepresentation

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable [ChartedSpace H G] [LieGroup I ⊤ G]

def orbitMap (π : ContinuousRepresentation G F) (v : F) : G → F :=
  fun g => (π.toMonoidHom g) v

def IsSmoothVector (π : ContinuousRepresentation G F) (v : F) : Prop :=
  ContMDiff I (modelWithCornersSelf ℝ F) ⊤ (π.orbitMap v)

def smoothVectors (π : ContinuousRepresentation G F) : Set F :=
  { v : F | π.IsSmoothVector I v }

def IsGFiniteVector (π : ContinuousRepresentation G F) (v : F) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun g : G => (π.toMonoidHom g) v)))

def gFiniteVectors (π : ContinuousRepresentation G F) : Set F :=
  { v : F | π.IsGFiniteVector v }

end ContinuousRepresentation

section Prop415

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable [ChartedSpace H G] [LieGroup I ⊤ G]





end Prop415

end
