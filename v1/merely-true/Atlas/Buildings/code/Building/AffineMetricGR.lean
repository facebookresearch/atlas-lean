/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineMetric
import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.UniqueRetraction
import Atlas.Buildings.code.Building.DiscreteFibers

set_option linter.unusedSectionVars false

open Classical
open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- Distance between two points $p$, $q$ of the geometric realisation of an
apartment, obtained by linearly extending the vertex distance using the
barycentric weights of $p$ and $q$. -/
noncomputable def aptDistGR (b : Building V) (md : ApartmentMetricData b)
    (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
    (p q : DiscreteFibers.PointF A.val) : ℝ :=
  ∑ u ∈ p.face, ∑ v ∈ q.face, p.wt u * q.wt v * md.dist_fn A u v

/-- Variant of `aptDistGR` taking weight functions and faces directly, useful for
proofs that bypass the bundled `PointF` structure. -/
noncomputable def aptDistGR' (b : Building V) (md : ApartmentMetricData b)
    (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
    (wtp wtq : V → ℝ) (σ τ : Finset V) : ℝ :=
  ∑ u ∈ σ, ∑ v ∈ τ, wtp u * wtq v * md.dist_fn A u v

/-- Well-definedness of the building distance via the apartment-isomorphism /
fix-of-intersection principle: the distance $d(v, w)$ measured inside any
apartment containing both vertices is independent of the chosen apartment. -/
theorem buildingDist_wellDefined_via_iso_fix (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
    (v w : V)
    (hv₁ : ∃ s ∈ A₁.val.faces, v ∈ s) (hw₁ : ∃ s ∈ A₁.val.faces, w ∈ s)
    (hv₂ : ∃ s ∈ A₂.val.faces, v ∈ s) (hw₂ : ∃ s ∈ A₂.val.faces, w ∈ s) :
    md.dist_fn A₁ v w = md.dist_fn A₂ v w := by

  obtain ⟨sv₁, hsv₁, hv_sv₁⟩ := hv₁
  have hv_sing₁ : {v} ∈ A₁.val.faces :=
    A₁.val.down_closed hsv₁ (Finset.singleton_subset_iff.mpr hv_sv₁) (Finset.singleton_nonempty v)
  obtain ⟨sw₁, hsw₁, hw_sw₁⟩ := hw₁
  have hw_sing₁ : {w} ∈ A₁.val.faces :=
    A₁.val.down_closed hsw₁ (Finset.singleton_subset_iff.mpr hw_sw₁) (Finset.singleton_nonempty w)
  obtain ⟨sv₂, hsv₂, hv_sv₂⟩ := hv₂
  have hv_sing₂ : {v} ∈ A₂.val.faces :=
    A₂.val.down_closed hsv₂ (Finset.singleton_subset_iff.mpr hv_sv₂) (Finset.singleton_nonempty v)
  obtain ⟨sw₂, hsw₂, hw_sw₂⟩ := hw₂
  have hw_sing₂ : {w} ∈ A₂.val.faces :=
    A₂.val.down_closed hsw₂ (Finset.singleton_subset_iff.mpr hw_sw₂) (Finset.singleton_nonempty w)
  exact buildingDist_well_defined_clean b md v w A₁ A₂ hv_sing₁ hw_sing₁ hv_sing₂ hw_sing₂

/-- A point of the geometric realisation of a building, abbreviating
`DiscreteFibers.PointF` of the underlying simplicial complex. -/
abbrev BuildingPointF (b : Building V) : Type :=
  DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex

/-- A point of the building lies in some apartment if its supporting face is a
face of one of the apartments of the system. -/
def pointInApartment (b : Building V) (p : BuildingPointF b) :=
  ∃ (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments }),
    p.face ∈ A.val.faces

end AffineBuilding
