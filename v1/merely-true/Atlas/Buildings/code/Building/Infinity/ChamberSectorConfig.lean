/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.Sectors
import Atlas.Buildings.code.ChamberComplex.Uniqueness

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding


/-- A simplicial map that fixes a simplex pointwise leaves its image equal to itself. -/
lemma simplex_image_eq_of_fixes {K L : SimplicialComplex V}
    (φ : SimplicialMap K L) (s : Finset V)
    (hfix : ∀ v ∈ s, φ.toFun v = v) :
    s.image φ.toFun = s := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [hfix y hy]
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

/-- If a simplicial map fixes a simplex pointwise, the simplex lies in the codomain complex. -/
lemma face_in_codomain_of_fixes {K L : SimplicialComplex V}
    (φ : SimplicialMap K L) (s : Finset V) (hs : s ∈ K.faces)
    (hfix : ∀ v ∈ s, φ.toFun v = v) :
    s ∈ L.faces := by
  have h := φ.map_face s hs
  rw [simplex_image_eq_of_fixes φ s hfix] at h
  exact h

/-- Strict inclusion of simplices is preserved by the image under an injective map. -/
lemma image_ssubset_of_ssubset_of_injective
    {K L : SimplicialComplex V}
    (φ : SimplicialMap K L)
    (hinj : Function.Injective φ.toFun)
    {s t : Finset V} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ⊂ t) :
    s.image φ.toFun ⊂ t.image φ.toFun :=
  (Finset.image_ssubset_image hinj).mpr hst

/-- Predicate: $v$ is a vertex of $K$ (lies in some face). -/
def IsVertexOf (K : SimplicialComplex V) (v : V) : Prop :=
  ∃ s ∈ K.faces, v ∈ s

end AffineBuilding
