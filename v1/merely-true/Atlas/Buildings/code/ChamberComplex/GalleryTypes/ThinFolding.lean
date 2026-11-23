/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.Building.Convexity

set_option maxHeartbeats 400000

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- *Thin folding propagation property*: in a thin chamber complex, if two foldings $f, g$ agree
on the image of a chamber $C$ (with both pinning a common adjacent pair), then they agree on the
image of any adjacent chamber — i.e. agreement on images propagates along adjacency. -/
structure ThinFoldingProperties (K : ChamberComplex V) where
  agree_propagates_adj :
    ∀ (f g : Folding K) (C C' : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      C ≠ C' →
      C.image f.morph.toFun = C → C'.image f.morph.toFun = C →
      C.image g.morph.toFun = C → C'.image g.morph.toFun = C →
      ∀ E D : Finset V,
        K.toSimplicialComplex.IsMaximal E →
        K.toSimplicialComplex.IsMaximal D →
        K.toSimplicialComplex.Adjacent E D →
        E.image f.morph.toFun = E.image g.morph.toFun →
        D.image f.morph.toFun = D.image g.morph.toFun

end ChamberComplex
