/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- $\sigma$ is *gate-convex* in apartment $A$ if its chambers are maximal in $A$ and every
maximal chamber $D$ of $A$ has a gate inside $\sigma$. -/
def IsGateConvexInApartment (K : SimplicialComplex V)
    (A : SimplicialComplex V) (σ : Set (Finset V)) : Prop :=
  (∀ C ∈ σ, C ∈ A.faces ∧ A.IsMaximal C) ∧
  ∀ D, A.IsMaximal D → ∃ G ∈ σ, IsGate K σ D G

/-- A *half-apartment* of $K$ is the set of fixed chambers of some folding $f$. -/
def IsHalfApartment (K : ChamberComplex V) (_A : SimplicialComplex V)
    (H : Set (Finset V)) : Prop :=
  ∃ f : ChamberComplex.Folding K, H = f.fixedChambers

/-- Hypotheses asserting that every gate-convex subset of an apartment is a fixed-chamber set of
some folding strictly avoiding a chosen outside chamber $D$. -/
structure GateConvexHypotheses {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) where
  folding_from_gate :
    ∀ (σ : Set (Finset V)),
      IsGateConvexInApartment b.toSimplicialComplex A σ →
      ∀ D, A.IsMaximal D → D ∉ σ →
      ∃ (K_A : ChamberComplex V) (_hK : K_A.toSimplicialComplex = A)
        (f : ChamberComplex.Folding K_A),
        (∀ C ∈ σ, C ∈ f.fixedChambers) ∧ D ∉ f.fixedChambers

end CombinatorialGeometry
