/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.UniqueRetraction
import Atlas.Buildings.code.Building.Labels

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A map $\varphi : V \to V$ is *label-preserving* on apartment $A$ relative to a given labelling
$\mathrm{lab}$ if it preserves the label of every face of $A$. -/
def IsLabelPreservingMap
    {L : Type*} [DecidableEq L]
    (b : Building V) (A : SimplicialComplex V)
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (φ : V → V) : Prop :=
  ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s

/-- A map $\varphi : V \to V$ is *universally label-preserving* on $A$ if it is label-preserving
relative to every labelling of the building. -/
def IsUniversallyLabelPreserving
    (b : Building V) (A : SimplicialComplex V)
    (φ : V → V) : Prop :=
  ∀ (L : Type*) [DecidableEq L] (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
    IsLabelPreservingMap b A lab φ

