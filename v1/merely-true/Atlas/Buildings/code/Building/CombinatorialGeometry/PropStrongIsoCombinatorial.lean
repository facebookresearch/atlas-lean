/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.CombinatorialGeometry.RetractionHalfApartments

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- Retraction dichotomy: for two retractions $\rho, \rho'$ associated to adjacent chambers
$C, C'$ and a target chamber $D$, either $\rho D = \rho' D$ or $\rho D$ and $\rho' D$ are related
by the wall reflection $s$ across $\{C, C'\}$ and lie in opposite half-apartments. -/
theorem retraction_dichotomy (b : Building V)
    (cfg : RetractionHalfApartmentConfig b) :

    cfg.ρ cfg.D = cfg.ρ' cfg.D ∨

    (cfg.ρ cfg.D = cfg.s_reflection (cfg.ρ' cfg.D) ∧
     cfg.ρ cfg.D ∈ cfg.H' ∧ cfg.ρ' cfg.D ∈ cfg.H) := by

  rcases Nat.lt_trichotomy
    (galleryDist b.toSimplicialComplex cfg.C' cfg.D)
    (galleryDist b.toSimplicialComplex cfg.C cfg.D) with hlt | heq | hgt
  ·
    exact Or.inl (retraction_case_closer b cfg hlt).1
  ·
    have h := retraction_case_equal b cfg heq
    right
    refine ⟨?_, h.1, h.2.1⟩

    have hs_eq : cfg.s_reflection (cfg.ρ cfg.D) = cfg.ρ' cfg.D := h.2.2


    rw [← hs_eq, cfg.s_invol]
  ·
    exact Or.inl (retraction_case_further b cfg hgt).1

end CombinatorialGeometry
