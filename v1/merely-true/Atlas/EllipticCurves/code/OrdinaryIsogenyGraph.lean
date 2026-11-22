/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.IsogenyVolcano

noncomputable section

open VolcanoStructure

namespace OrdinaryIsogenyGraph

/-- Surface vertices of an ordinary $\ell$-isogeny volcano have degree $1 + (D_0 / \ell)$
in the crater (Kohel's theorem, Theorem 22.11(ii)). -/
theorem crater_degree_eq_jacobi {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)
    (v : K.volcano.V) (hv : K.volcano.isSurface v) :
    (K.volcano.craterGraph.degree v : ℤ) = 1 + jacobiSym C.D₀ C.ℓ :=
  crater_degree_eq_jacobiSym K v hv

/-- Vertices on the surface ($V_0$) of an ordinary $\ell$-volcano have endomorphism ring of
conductor $f_0$ (Theorem 22.11(i), (v)). -/
theorem surface_conductor {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)
    (v : K.volcano.V)
    (hv : (K.volcano.level v : ℕ) = 0) :
    K.conductor v = C.f₀ :=
  surface_conductor_eq K v hv

/-- Vertices on the floor ($V_d$) of an ordinary $\ell$-volcano of depth $d$ have endomorphism
ring of conductor $f_0 \cdot \ell^d$ (Theorem 22.11(iv), (v)). -/
theorem floor_conductor {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)
    (v : K.volcano.V)
    (hv : (K.volcano.level v : ℕ) = K.volcano.depth) :
    K.conductor v = C.f₀ * C.ℓ ^ K.volcano.depth :=
  floor_conductor_eq K v hv

end OrdinaryIsogenyGraph

end
