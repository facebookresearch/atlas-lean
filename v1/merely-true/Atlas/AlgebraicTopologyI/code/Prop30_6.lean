/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.BilinFormClassification

open Matrix

namespace SymmetricBilinearForms

/-- **The standard normal form (matrix presentation) of Proposition 30.6.**
The Gram matrix of the block-diagonal form on `(ZMod 2)^{a+2b}` consisting
of `a` copies of the rank-one form `[1]` followed by `b` copies of the
hyperbolic plane `⎡⎣0 1 / 1 0⎤⎦`.  Indices `0,…,a-1` form the diagonal
block; indices `a, a+1, a+2, a+3, …` form pairs `(a+2k, a+2k+1)` each
giving a hyperbolic plane.  This is the matrix appearing on the right-hand
side of the classification theorem below. -/
def standardFormF2 (a b : ℕ) :
    Matrix (Fin (a + 2 * b)) (Fin (a + 2 * b)) (ZMod 2) :=
  fun i j =>
    let iv := i.val
    let jv := j.val
    if iv < a ∧ jv < a then
      if iv = jv then 1 else 0
    else if iv ≥ a ∧ jv ≥ a then
      let iv' := iv - a
      let jv' := jv - a
      if iv' / 2 = jv' / 2 then
        if iv' % 2 ≠ jv' % 2 then 1 else 0
      else 0
    else 0

/-- **Proposition 30.6 (Classification of nondegenerate symmetric bilinear
forms over `F₂`).**  Every nondegenerate symmetric bilinear form `B` on a
finite-dimensional vector space `V` over `F₂ = ZMod 2` is isometric to a
standard block-diagonal form: there exist natural numbers `a, b` and a
linear isomorphism `e : V ≃ₗ (F₂)^a × (F₂²)^b` carrying `B` to
`standardF2Form a b`, the orthogonal direct sum of `a` copies of the
rank-one form `⟨1⟩` with `b` copies of the hyperbolic plane.  This is the
mod-2 analogue of the classical real / complex classification of symmetric
bilinear forms and underlies the Wu–formula description of the intersection
form on a closed 4-manifold's middle cohomology with `F₂` coefficients. -/
theorem nondegenerate_symm_bilinearForm_F2_classification
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB_symm : B.IsSymm) (hB_nondeg : B.Nondegenerate) :
    ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)),
      (LinearMap.BilinForm.congr e) B = BilinFormZMod2.standardF2Form a b :=
  BilinFormZMod2.exists_isometry_standardF2Form B hB_symm hB_nondeg

end SymmetricBilinearForms
