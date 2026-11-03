/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Defs

noncomputable section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Zariski cotangent space (Def 35, Lec 18): for a local ring `R` with
maximal ideal `m`, it is `m/m²` as a vector space over the residue field. -/
abbrev ZariskiCotangentSpace : Type u := CotangentSpace R

/-- The Zariski cotangent space is naturally a module over the residue field. -/
instance ZariskiCotangentSpace.instModule :
    Module (ResidueField R) (ZariskiCotangentSpace R) :=
  inferInstance

/-- The Zariski tangent space, defined as the residue-field dual of the
Zariski cotangent space; equivalently, derivations `R → k`. -/
abbrev ZariskiTangentSpace : Type u :=
  Module.Dual (ResidueField R) (ZariskiCotangentSpace R)

/-- Residue-field module structure on the Zariski tangent space. -/
instance ZariskiTangentSpace.instModule :
    Module (ResidueField R) (ZariskiTangentSpace R) :=
  inferInstance

/-- Unfolding: the Zariski cotangent space is exactly the cotangent module
`m/m²` of the maximal ideal. -/
theorem ZariskiCotangentSpace.eq_maximalIdeal_cotangent :
    ZariskiCotangentSpace R = (maximalIdeal R).Cotangent := rfl

/-- Unfolding: the Zariski tangent space is the residue-field dual of the
cotangent space `m/m²`. -/
theorem ZariskiTangentSpace.eq_dual :
    ZariskiTangentSpace R = Module.Dual (ResidueField R) (CotangentSpace R) := rfl

end
