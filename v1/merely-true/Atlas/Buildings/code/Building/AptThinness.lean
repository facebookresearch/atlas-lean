/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsCoxeterProof

open ChamberComplex

variable {V : Type*} [DecidableEq V]

namespace AptIsCoxeterProof

/-- Every face of an apartment $A$ is contained in some maximal chamber of $A$. -/
theorem apt_face_in_chamber {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (s : Finset V) (hs : s ∈ A.faces) :
    ∃ C, A.IsMaximal C ∧ s ⊆ C := by
  obtain ⟨cc, hcc_eq, _⟩ := pre.apt_thin_cc A hA
  have hs' : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
  obtain ⟨C, hCmax, hsC⟩ := cc.exists_maximal s hs'
  exact ⟨C, hcc_eq ▸ hCmax, hsC⟩

/-- Any two maximal chambers of an apartment $A$ are connected by a gallery internal to $A$. -/
theorem apt_gallery_connected {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    ∃ g : Gallery A, g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by
  obtain ⟨cc, hcc_eq, _⟩ := pre.apt_thin_cc A hA
  subst hcc_eq
  exact cc.gallery_connected C D hC hD

/-- The chamber complex structure on an apartment $A$ inherited from `PreApartmentData`. -/
noncomputable def aptChamberComplex {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ChamberComplex V where
  faces := A.faces
  nonempty_of_mem := A.nonempty_of_mem
  down_closed := A.down_closed
  exists_maximal := fun s hs => apt_face_in_chamber pre A hA s hs
  gallery_connected := fun C D hCmax hDmax =>
    apt_gallery_connected pre A hA C D hCmax hDmax

/-- The simplicial complex underlying `aptChamberComplex` is precisely the apartment $A$. -/
theorem aptChamberComplex_eq {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    (aptChamberComplex pre A hA).toSimplicialComplex = A := by
  simp [aptChamberComplex]

/-- The `aptChamberComplex` associated to an apartment is thin. -/
theorem apt_is_thin {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    (aptChamberComplex pre A hA).IsThin := by
  obtain ⟨cc, hcc_eq, hthin⟩ := pre.apt_thin_cc A hA


  have heq : (aptChamberComplex pre A hA).toSimplicialComplex =
      cc.toSimplicialComplex := by
    rw [aptChamberComplex_eq, hcc_eq]

  intro F C hFC hCmax

  have hFC' : cc.toSimplicialComplex.IsFacet F C := by
    have := hFC; rw [heq] at this; exact this
  have hCmax' : cc.toSimplicialComplex.IsMaximal C := by
    have := hCmax; rw [heq] at this; exact this
  obtain ⟨D, ⟨hDne, hDfacet, hDmax⟩, hDuniq⟩ := hthin F C hFC' hCmax'
  refine ⟨D, ⟨hDne, ?_, ?_⟩, ?_⟩
  ·
    have := hDfacet; rw [← heq] at this; exact this
  ·
    have := hDmax; rw [← heq] at this; exact this
  ·
    intro D' ⟨hD'ne, hD'facet, hD'max⟩
    apply hDuniq
    refine ⟨hD'ne, ?_, ?_⟩
    · have := hD'facet; rw [heq] at this; exact this
    · have := hD'max; rw [heq] at this; exact this

/-- In a thick chamber complex, every apartment admits an underlying thin chamber complex. -/
theorem apt_thinness_from_thickness
    (K : ChamberComplex V) (_hThick : K.IsThick)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin :=
  ⟨aptChamberComplex pre A hA,
   aptChamberComplex_eq pre A hA,
   apt_is_thin pre A hA⟩

end AptIsCoxeterProof
