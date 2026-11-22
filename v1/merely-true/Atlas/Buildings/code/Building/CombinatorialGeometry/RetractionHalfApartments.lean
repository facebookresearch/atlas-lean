/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- Configuration of data needed for the half-apartment retraction analysis: two adjacent
chambers $C, C'$, a third chamber $D$, an apartment $A$ containing $C, C'$, two retractions
$\rho, \rho'$ onto $A$ centered at $C, C'$, the two half-apartments $H, H'$ on either side of the
wall, plus the wall reflection $s$. -/
structure RetractionHalfApartmentConfig (b : Building V) where
  C : Finset V
  C' : Finset V
  D : Finset V
  hC : b.toSimplicialComplex.IsMaximal C
  hC' : b.toSimplicialComplex.IsMaximal C'
  hD : b.toSimplicialComplex.IsMaximal D
  hCC' : C ≠ C'
  hCD : C ≠ D
  hC'D : C' ≠ D
  adj : b.toSimplicialComplex.Adjacent C C'
  A : SimplicialComplex V
  hA : A ∈ b.apartmentSystem.apartments
  hCA : C ∈ A.faces
  hC'A : C' ∈ A.faces
  ρ : Finset V → Finset V
  ρ' : Finset V → Finset V
  ρ_maps_to_A : ∀ E, b.toSimplicialComplex.IsMaximal E → ρ E ∈ A.faces
  ρ'_maps_to_A : ∀ E, b.toSimplicialComplex.IsMaximal E → ρ' E ∈ A.faces
  ρ_preserves_dist_C : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C (ρ E) = galleryDist b.toSimplicialComplex C E
  ρ'_preserves_dist_C' : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C' (ρ' E) = galleryDist b.toSimplicialComplex C' E
  ρ_diminishes_dist_C' : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C' (ρ E) ≤ galleryDist b.toSimplicialComplex C' E
  ρ'_diminishes_dist_C : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C (ρ' E) ≤ galleryDist b.toSimplicialComplex C E
  H : Set (Finset V)
  H' : Set (Finset V)
  hC_in_H : C ∈ H
  hC'_in_H' : C' ∈ H'
  H_char : ∀ E ∈ A.faces, A.IsMaximal E →
    (E ∈ H ↔ galleryDist b.toSimplicialComplex C E < galleryDist b.toSimplicialComplex C' E)
  H'_char : ∀ E ∈ A.faces, A.IsMaximal E →
    (E ∈ H' ↔ galleryDist b.toSimplicialComplex C' E < galleryDist b.toSimplicialComplex C E)
  ρ_maximal : ∀ E, b.toSimplicialComplex.IsMaximal E → A.IsMaximal (ρ E)
  ρ'_maximal : ∀ E, b.toSimplicialComplex.IsMaximal E → A.IsMaximal (ρ' E)
  retraction_agree_on_common_apt :
    (∃ B ∈ b.apartmentSystem.apartments, C ∈ B.faces ∧ C' ∈ B.faces ∧ D ∈ B.faces) →
    ρ D = ρ' D
  adj_A : A.Adjacent C C'
  adj_dist : galleryDist b.toSimplicialComplex C C' = 1
  adj_dist' : galleryDist b.toSimplicialComplex C' C = 1
  adj_triangle : galleryDist b.toSimplicialComplex C' D ≤
    galleryDist b.toSimplicialComplex C D + 1
  adj_triangle' : galleryDist b.toSimplicialComplex C D ≤
    galleryDist b.toSimplicialComplex C' D + 1
  coxeter_dist_ne : ∀ E ∈ A.faces, A.IsMaximal E →
    galleryDist b.toSimplicialComplex C' E ≠ galleryDist b.toSimplicialComplex C E
  s_reflection : Finset V → Finset V
  s_swap_C : s_reflection C = C'
  s_swap_C' : s_reflection C' = C
  s_invol : ∀ E, s_reflection (s_reflection E) = E
  s_swaps_H : ∀ E ∈ H, s_reflection E ∈ H'
  s_reflection_eq_of_equal_dist :
    galleryDist b.toSimplicialComplex C' D = galleryDist b.toSimplicialComplex C D →
    s_reflection (ρ D) = ρ' D

/-- Case "further": if $d(C', D) > d(C, D)$, then $\rho D = \rho' D$ and this common image lies in
the near half-apartment $H$. -/
theorem retraction_case_further (b : Building V)
    (cfg : RetractionHalfApartmentConfig b)
    (hfurther : galleryDist b.toSimplicialComplex cfg.C' cfg.D >
                galleryDist b.toSimplicialComplex cfg.C cfg.D) :
    cfg.ρ cfg.D = cfg.ρ' cfg.D ∧ cfg.ρ cfg.D ∈ cfg.H := by


  have hcollinear : galleryDist b.toSimplicialComplex cfg.C' cfg.D =
      galleryDist b.toSimplicialComplex cfg.C' cfg.C +
      galleryDist b.toSimplicialComplex cfg.C cfg.D := by
    have hbound := cfg.adj_triangle
    rw [cfg.adj_dist']
    omega
  have hyp := threeChamberHypotheses_of_building b
  have hcommon := three_chambers_common_apartment b hyp cfg.C' cfg.C cfg.D cfg.hC' cfg.hC cfg.hD
    hcollinear

  have hcommon' : ∃ B ∈ b.apartmentSystem.apartments,
      cfg.C ∈ B.faces ∧ cfg.C' ∈ B.faces ∧ cfg.D ∈ B.faces := by
    obtain ⟨B, hB, hC'B, hCB, hDB⟩ := hcommon
    exact ⟨B, hB, hCB, hC'B, hDB⟩
  constructor
  ·
    exact cfg.retraction_agree_on_common_apt hcommon'
  ·
    have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    have hdist_C : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) =
        galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ_preserves_dist_C cfg.D cfg.hD
    rw [cfg.H_char (cfg.ρ cfg.D) hρD_face hρD_max, hdist_C]

    have hρ_eq := cfg.retraction_agree_on_common_apt hcommon'
    rw [hρ_eq, cfg.ρ'_preserves_dist_C' cfg.D cfg.hD]
    exact hfurther

/-- Case "closer": if $d(C', D) < d(C, D)$, then $\rho D = \rho' D$ and this common image lies in
the far half-apartment $H'$. -/
theorem retraction_case_closer (b : Building V)
    (cfg : RetractionHalfApartmentConfig b)
    (hcloser : galleryDist b.toSimplicialComplex cfg.C' cfg.D <
               galleryDist b.toSimplicialComplex cfg.C cfg.D) :
    cfg.ρ cfg.D = cfg.ρ' cfg.D ∧ cfg.ρ cfg.D ∈ cfg.H' := by


  have hcollinear : galleryDist b.toSimplicialComplex cfg.C cfg.D =
      galleryDist b.toSimplicialComplex cfg.C cfg.C' +
      galleryDist b.toSimplicialComplex cfg.C' cfg.D := by
    have hbound := cfg.adj_triangle'
    rw [cfg.adj_dist]
    omega
  have hyp := threeChamberHypotheses_of_building b
  have hcommon := three_chambers_common_apartment b hyp cfg.C cfg.C' cfg.D cfg.hC cfg.hC' cfg.hD
    hcollinear

  have hcommon' : ∃ B ∈ b.apartmentSystem.apartments,
      cfg.C ∈ B.faces ∧ cfg.C' ∈ B.faces ∧ cfg.D ∈ B.faces := by
    obtain ⟨B, hB, hCB, hC'B, hDB⟩ := hcommon
    exact ⟨B, hB, hCB, hC'B, hDB⟩
  constructor
  · exact cfg.retraction_agree_on_common_apt hcommon'
  · have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    rw [cfg.H'_char (cfg.ρ cfg.D) hρD_face hρD_max]
    have hρ_eq := cfg.retraction_agree_on_common_apt hcommon'
    rw [hρ_eq, cfg.ρ'_preserves_dist_C' cfg.D cfg.hD,
        ← hρ_eq, cfg.ρ_preserves_dist_C cfg.D cfg.hD]
    exact hcloser

/-- Case "equal": if $d(C', D) = d(C, D)$, then $\rho D \in H'$, $\rho' D \in H$, and the wall
reflection $s$ swaps them: $s(\rho D) = \rho' D$. -/
theorem retraction_case_equal (b : Building V)
    (cfg : RetractionHalfApartmentConfig b)
    (hequal : galleryDist b.toSimplicialComplex cfg.C' cfg.D =
              galleryDist b.toSimplicialComplex cfg.C cfg.D) :
    cfg.ρ cfg.D ∈ cfg.H' ∧ cfg.ρ' cfg.D ∈ cfg.H ∧
    cfg.s_reflection (cfg.ρ cfg.D) = cfg.ρ' cfg.D := by

  have hρD_in_H' : cfg.ρ cfg.D ∈ cfg.H' := by
    have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    rw [cfg.H'_char (cfg.ρ cfg.D) hρD_face hρD_max]

    have hdist_C : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) =
        galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ_preserves_dist_C cfg.D cfg.hD

    have hdist_C'_le : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ cfg.D) ≤
        galleryDist b.toSimplicialComplex cfg.C' cfg.D :=
      cfg.ρ_diminishes_dist_C' cfg.D cfg.hD
    have h_le : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ cfg.D) ≤
        galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) := by
      rw [hdist_C, ← hequal]; exact hdist_C'_le

    have hne := cfg.coxeter_dist_ne (cfg.ρ cfg.D) hρD_face hρD_max
    exact lt_of_le_of_ne h_le hne

  have hρ'D_in_H : cfg.ρ' cfg.D ∈ cfg.H := by
    have hρ'D_face := cfg.ρ'_maps_to_A cfg.D cfg.hD
    have hρ'D_max := cfg.ρ'_maximal cfg.D cfg.hD
    rw [cfg.H_char (cfg.ρ' cfg.D) hρ'D_face hρ'D_max]
    have hdist_C' : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) =
        galleryDist b.toSimplicialComplex cfg.C' cfg.D :=
      cfg.ρ'_preserves_dist_C' cfg.D cfg.hD
    have hdist_C_le : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≤
        galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ'_diminishes_dist_C cfg.D cfg.hD
    have h_le : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≤
        galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) := by
      rw [hdist_C', hequal]; exact hdist_C_le
    have hne : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≠
        galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) := by
      intro heq
      exact cfg.coxeter_dist_ne (cfg.ρ' cfg.D) hρ'D_face hρ'D_max heq.symm
    exact lt_of_le_of_ne h_le hne

  exact ⟨hρD_in_H', hρ'D_in_H, cfg.s_reflection_eq_of_equal_dist hequal⟩

end CombinatorialGeometry
