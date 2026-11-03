/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.Building.Convexity

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace Gallery

/-- The gallery $g$ *crosses the wall of $f$* at edge $i$ if $g_i$ and $g_{i+1}$ lie on opposite
sides of the wall. -/
def CrossesWallAt {K : ChamberComplex V}
    (g : Gallery K.toSimplicialComplex) (f : ChamberComplex.Folding K)
    (i : Fin (g.chambers.length - 1)) : Prop :=
  ChamberComplex.OppositeSides f g.chambers[i.val] g.chambers[i.val + 1]

/-- The set of edges along $g$ at which the gallery crosses the wall of $f$. -/
def WallCrossings {K : ChamberComplex V}
    (g : Gallery K.toSimplicialComplex) (f : ChamberComplex.Folding K) :
    Set (Fin (g.chambers.length - 1)) :=
  { i | g.CrossesWallAt f i }

end Gallery

namespace ChamberComplex

/-- *Wall-crossing properties*: in a minimal gallery, two same-side endpoints give no wall
crossings, opposite-side endpoints give at least one wall crossing, and minimal galleries cross
each wall at most once. -/
structure WallCrossingProperties (K : ChamberComplex V) where
  both_fixed_no_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      C.image f.morph.toFun = C →
      D.image f.morph.toFun = D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        g.WallCrossings f = ∅
  both_moved_no_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      C.image f.morph.toFun ≠ C →
      D.image f.morph.toFun ≠ D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        g.WallCrossings f = ∅
  opposite_at_least_one :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      OppositeSides f C D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        ∃ i, i ∈ g.WallCrossings f
  at_most_one_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        ∀ i j : Fin (g.chambers.length - 1),
          i ∈ g.WallCrossings f →
          j ∈ g.WallCrossings f →
          i = j

end ChamberComplex
