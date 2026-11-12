/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.Building.Labels

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace Gallery

/-- A gallery is *non-stuttering* if consecutive chambers are always distinct. -/
def IsNonStuttering {K : SimplicialComplex V} (g : Gallery K) : Prop :=
  ∀ i : Fin (g.chambers.length - 1),
    g.chambers[i.val] ≠ g.chambers[i.val + 1]

end Gallery

/-- The *type* of a gallery under a labelling: the list of label-sets of the shared codim-$1$
faces along consecutive chambers. -/
def GalleryType {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (g : Gallery K.toSimplicialComplex) : List (Finset L) :=
  (List.zip g.chambers g.chambers.tail).map
    fun p => lab.labelMap (p.1 ∩ p.2)

namespace ChamberComplex

/-- $K$ is *Coxeter-characterized*: it is thin and every adjacent pair has a folding that
separates them (one fixed, one moved). -/
structure IsCoxeterCharacterized (K : ChamberComplex V) : Prop where
  thin : K.IsThin
  wallSeparation : ∀ C D, K.toSimplicialComplex.Adjacent C D →
    ∃ f : Folding K,
      (C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∨
      (D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C)

/-- The *type-deletion condition* for galleries: any non-minimal non-stuttering gallery admits a
shorter gallery whose type is obtained by deleting two letters at positions $i < j$ from the
original type, mirroring the Coxeter deletion condition. -/
def HasTypeDeletion {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L) : Prop :=
  ∀ (g : Gallery K.toSimplicialComplex) (C D : Finset V),
    g.IsNonStuttering →
    g.Connects C D →
    g.length > galleryDist K.toSimplicialComplex C D →
    ∃ (g' : Gallery K.toSimplicialComplex),
      g'.Connects C D ∧
      g'.length < g.length ∧
      ∃ (i j : ℕ), i < j ∧ j < (GalleryType K lab g).length ∧
        GalleryType K lab g' =
          (GalleryType K lab g).take i ++
          ((GalleryType K lab g).drop (i + 1)).take (j - i - 1) ++
          (GalleryType K lab g).drop (j + 1)

end ChamberComplex
