/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The structure map making an open subscheme of `X` into a scheme over `Spec k`, obtained
by composing the open immersion with the structure map of `X`. -/
noncomputable instance openSubschemeOverSpec (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (U : X.Opens) :
    (↑U : Scheme.{u}).Over (Spec (.of k)) :=
  OverClass.ofHom (U.ι ≫ (X ↘ Spec (.of k)))

/-- Lecture 2, Corollary 4: an open subspace `U` of an algebraic variety `X` over `k` is itself
an algebraic variety over `k`. -/
theorem isAlgebraicVariety_openSubscheme (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [hX : IsAlgebraicVariety k X] (U : X.Opens) :
    IsAlgebraicVariety k (↑U : Scheme.{u}) where
  isReduced := isReduced_of_isOpenImmersion U.ι
  locallyOfFiniteType := by
    show LocallyOfFiniteType (U.ι ≫ (X ↘ Spec (.of k)))
    exact locallyOfFiniteType_comp U.ι (X ↘ Spec (.of k))
  hasFiniteAffineCover := by

    haveI : IsLocallyNoetherian X :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ (X ↘ Spec (.of k))
        hX.locallyOfFiniteType inferInstance

    haveI : CompactSpace X := by
      obtain ⟨ι, hfin, V, haffine, hcov⟩ := hX.hasFiniteAffineCover
      rw [← isCompact_univ_iff]
      rw [← show (⋃ i, (V i : Set X)) = Set.univ from by
        rw [← Opens.coe_iSup]; simp [hcov]]
      exact isCompact_iUnion fun i => by
        haveI : IsNoetherianRing Γ(X, V i) :=
          IsLocallyNoetherian.component_noetherian ⟨V i, haffine i⟩
        haveI : NoetherianSpace (V i) := noetherianSpace_of_isAffineOpen (V i) (haffine i)
        rw [isCompact_iff_compactSpace]
        haveI : NoetherianSpace ((V i).1 : Set X) := ‹NoetherianSpace (V i)›
        infer_instance

    haveI : IsNoetherian X := ⟨⟩
    haveI : NoetherianSpace X := IsNoetherian.noetherianSpace

    haveI : NoetherianSpace (↑U : Scheme.{u}) := NoetherianSpace.set (U : Set X)

    haveI : CompactSpace (↑U : Scheme.{u}) := NoetherianSpace.compactSpace _

    let 𝒰 := (↑U : Scheme.{u}).affineCover.finiteSubcover
    refine ⟨𝒰.I₀, Fintype.ofFinite _, fun i => (𝒰.f i).opensRange,
      fun i => ?_, 𝒰.iSup_opensRange⟩

    have : IsAffine (𝒰.X i) := by
      rw [(↑U : Scheme.{u}).affineCover.finiteSubcover_X i]
      exact Scheme.isAffine_affineCover _ _
    exact isAffineOpen_opensRange (𝒰.f i)

end AlgebraicGeometry.Scheme
