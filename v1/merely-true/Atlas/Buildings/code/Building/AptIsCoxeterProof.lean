/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 0

open ChamberComplex

variable {V : Type*} [DecidableEq V]

namespace AptIsCoxeterProof

/-- A bundle of structural properties an apartment system must satisfy in order to apply the
Tits theorem and conclude that apartments are Coxeter complexes. Captures simplicial isomorphism
existence, gallery convexity, thinness, and bijectivity of intertwining maps. -/
structure PreApartmentData (K : ChamberComplex V) where
  apartments : Set (SimplicialComplex V)
  nonempty_apartments : ∃ A, A ∈ apartments
  sub : ∀ A ∈ apartments, IsSubcomplex A K.toSimplicialComplex
  contains_pair : ∀ C D,
    K.toSimplicialComplex.IsMaximal C →
    K.toSimplicialComplex.IsMaximal D →
    ∃ A ∈ apartments, C ∈ A.faces ∧ D ∈ A.faces
  iso_exists : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ x, x ∈ A.faces → x ∈ A'.faces →
    ∀ C, A.IsMaximal C → C ∈ A'.faces →
    ∃ φ : SimplicialMap A A',
      (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v)
  maximal_in_apt_is_maximal :
    ∀ A ∈ apartments, ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal C
  gallery_convex :
    ∀ A ∈ apartments, ∀ C D : Finset V,
      C ∈ A.faces → K.toSimplicialComplex.IsMaximal C →
      D ∈ A.faces → K.toSimplicialComplex.IsMaximal D →
      ∀ g : Gallery K.toSimplicialComplex,
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        ∀ E ∈ g.chambers, E ∈ A.faces
  building_maximal_in_apt_is_apt_maximal :
    ∀ A ∈ apartments, ∀ C, C ∈ A.faces →
      K.toSimplicialComplex.IsMaximal C → A.IsMaximal C
  apt_nonempty :
    ∀ A ∈ apartments, ∃ s, s ∈ A.faces
  iso_bijective : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ C, C ∈ A.faces → C ∈ A'.faces → A.IsMaximal C →
    ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
  apt_thin_cc : ∀ A ∈ apartments,
    ∃ cc : ChamberComplex V, cc.toSimplicialComplex = A ∧ cc.IsThin
  apt_automorphism : ∀ A ∈ apartments, ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D →
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C



/-- A chamber complex $cc$ has *sufficient foldings* if every pair of adjacent chambers $C, C'$
admits a pair of foldings whose images contain the corresponding chamber. -/
def HasSufficientFoldings (cc : ChamberComplex V) : Prop :=
  ∀ C C' : Finset V,
    cc.toSimplicialComplex.Adjacent C C' →
    ∃ (f f' : Folding cc),
      C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C ∧
      C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C'

/-- Hypothesis statement of Tits' theorem: every thin chamber complex with sufficient foldings is
isomorphic to a Coxeter complex. -/
def TitsTheoremHyp (V : Type*) [DecidableEq V] : Prop :=
  ∀ (cc : ChamberComplex V),
    cc.IsThin → HasSufficientFoldings cc →
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
      (φ : Finset V → M.Group),
      (∀ C, cc.toSimplicialComplex.IsMaximal C →
        ∀ D, cc.toSimplicialComplex.IsMaximal D →
          φ C = φ D → C = D) ∧
      (∀ w : M.Group, ∃ C, cc.toSimplicialComplex.IsMaximal C ∧ φ C = w) ∧
      (∀ C C', cc.toSimplicialComplex.Adjacent C C' →
        CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))

/-- Hypothesis statement: in a thick chamber complex, every apartment carries a thin chamber
structure with sufficient foldings. -/
def ThicknessImpliesAptStructureHyp (V : Type*) [DecidableEq V] : Prop :=
  ∀ (K : ChamberComplex V),
    K.IsThick →
    ∀ (pre : PreApartmentData K) (A : SimplicialComplex V),
      A ∈ pre.apartments →
      ∃ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A ∧
        cc.IsThin ∧
        HasSufficientFoldings cc




end AptIsCoxeterProof
