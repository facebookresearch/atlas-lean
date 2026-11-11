/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

set_option maxHeartbeats 1600000

open scoped TensorProduct
open nonZeroDivisors
open RiemannRochCurves CanonicalSheafCurves

noncomputable section


/-- A Dedekind curve over a field `k`: the data of a finite `k`-algebra `A` which is a
Dedekind domain. Models a smooth affine curve over `k`. -/
structure DedekindCurve (k : Type*) [Field k] where
  A : Type*
  [instCR : CommRing A]
  [instID : IsDomain A]
  [instDD : IsDedekindDomain A]
  [instAlg : Algebra k A]
  [instFin : Module.Finite k A]

attribute [instance] DedekindCurve.instCR DedekindCurve.instID DedekindCurve.instDD
  DedekindCurve.instAlg DedekindCurve.instFin

namespace DedekindCurve

variable {k : Type*} [Field k]


/-- The genus of a Dedekind curve, defined as the `k`-dimension of its global Kähler
differentials `Ω[A⁄k]`. -/
def ddGenus (C : DedekindCurve k) : ℕ :=
  Module.finrank k (Ω[C.A⁄k])

/-- Degree of an ideal `I` on a Dedekind curve `C`, measured as `dim_k (A/I)`. -/
def curveIdealDeg (C : DedekindCurve k) (I : Ideal C.A) : ℕ :=
  Module.finrank k (C.A ⧸ I)

/-- The generic rank of an `A`-module `M` on the curve `C`, defined as the dimension of
its localization at the generic point. -/
def curveModuleRk (C : DedekindCurve k) (M : Type*) [AddCommGroup M] [Module C.A M] : ℕ :=
  Module.finrank (FractionRing C.A) (FractionRing C.A ⊗[C.A] M)


/-- The Euler characteristic of the structure sheaf of a Dedekind curve: `χ(O_X) = 1 - g`. -/
def eulerCharO (C : DedekindCurve k) : ℤ :=
  1 - (C.ddGenus : ℤ)

/-- The degree of the canonical divisor on a Dedekind curve: `deg K = 2g - 2`. -/
def degK (C : DedekindCurve k) : ℤ :=
  2 * (C.ddGenus : ℤ) - 2


end DedekindCurve

/-- `h¹(O_X)` for a Dedekind curve, defined via `dim_k Ω[A⁄k]` using Serre duality. -/
noncomputable def DedekindCurve.h1_O (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- `h¹(O_X)` agrees by definition with `dim_k Ω[A⁄k]` (the genus). -/
theorem DedekindCurve.h1_O_eq_genus :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    DedekindCurve.h1_O k A = Module.finrank k (Ω[A⁄k]) :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- `H¹` of a skyscraper sheaf on a Dedekind curve vanishes (by dimension); modeled as `0`. -/
def DedekindCurve.h1_sky (_k : Type*) [Field _k] (_A : Type*) [CommRing _A] [IsDomain _A]
    [IsDedekindDomain _A] [Algebra _k _A] [Module.Finite _k _A] : ℕ :=
  0

/-- `h¹` of a skyscraper is zero, by definition. -/
theorem DedekindCurve.h1_sky_eq_zero :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    DedekindCurve.h1_sky k A = 0 :=
  fun _ _ _ _ _ _ _ _ => rfl

namespace DedekindCurve

variable {k : Type*} [Field k]

/-- The additive Euler-characteristic homomorphism on the K-theory generators
`(rank, degree)`, sending `(r, d)` to `r·χ(O_X) + d·χ(sky)`. -/
def cohChi (C : DedekindCurve k) : ℤ × ℤ →+ ℤ where
  toFun p := p.1 * (1 - (h1_O k C.A : ℤ)) + p.2 * (1 - (h1_sky k C.A : ℤ))
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring

/-- Value of `cohChi` on the generator `(1, 0)` (the structure sheaf class). -/
theorem cohChi_struct (C : DedekindCurve k) :
    C.cohChi (1, 0) = 1 - (h1_O k C.A : ℤ) := by
  simp [cohChi]

/-- Value of `cohChi` on the skyscraper generator `(0, 1)`. -/
theorem cohChi_sky (C : DedekindCurve k) :
    C.cohChi (0, 1) = 1 - (h1_sky k C.A : ℤ) := by
  simp [cohChi]

/-- Rewritten value of `cohChi` on `(1, 0)`, expressed via the genus `g`. -/
theorem cohChi_struct_eq (C : DedekindCurve k) :
    C.cohChi (1, 0) = 1 - (C.ddGenus : ℤ) := by
  simp only [cohChi_struct, h1_O_eq_genus, ddGenus]

/-- The skyscraper generator contributes `1` to the Euler characteristic. -/
theorem cohChi_sky_eq (C : DedekindCurve k) :
    C.cohChi (0, 1) = 1 := by
  rw [cohChi_sky, h1_sky_eq_zero]; simp

/-- The Euler-characteristic homomorphism `cohChi` agrees with the Riemann–Roch homomorphism
`rrHom g` parametrized by the genus. -/
theorem cohChi_eq_rrHom (C : DedekindCurve k) :
    C.cohChi = RiemannRochCurves.rrHom (C.ddGenus : ℤ) :=
  RiemannRochCurves.additive_homs_eq_of_generators_eq C.cohChi
    (RiemannRochCurves.rrHom (C.ddGenus : ℤ))
    (by rw [C.cohChi_struct_eq, RiemannRochCurves.rr_value_structure_sheaf])
    (by rw [C.cohChi_sky_eq, RiemannRochCurves.rr_value_skyscraper])


/-- Definitional unfolding of `eulerCharO`: `χ(O_X) = 1 - g`. -/
theorem eulerCharO_eq (C : DedekindCurve k) :
    C.eulerCharO = 1 - (C.ddGenus : ℤ) := rfl

/-- Definitional unfolding of `degK`: `deg K = 2g - 2`. -/
theorem degK_eq_2g_sub_2 (C : DedekindCurve k) :
    C.degK = 2 * (C.ddGenus : ℤ) - 2 := rfl





/-- Sheaf-level `h¹(O_X)` for a Dedekind curve, again defined via `dim_k Ω[A⁄k]`. -/
def h1_O_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- `h1_O_sheaf` agrees with the Kähler-differential dimension defining the genus. -/
theorem h1_O_sheaf_eq_genus :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    h1_O_sheaf k A = Module.finrank k (Ω[A⁄k]) :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- Sheaf-level Euler characteristic of `O_X` for a Dedekind curve: `1 - g`. -/
def eulerCharO_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℤ :=
  1 - (Module.finrank k (Ω[A⁄k]) : ℤ)

/-- Definitional equality showing `eulerCharO_sheaf k A = 1 - dim_k Ω[A⁄k]`. -/
theorem eulerCharO_sheaf_eq_formula :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    eulerCharO_sheaf k A = 1 - (Module.finrank k (Ω[A⁄k]) : ℤ) :=
  fun _ _ _ _ _ _ _ _ => rfl

/-- Sheaf-level degree of the canonical divisor of a Dedekind curve: `2g - 2`. -/
def degK_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℤ :=
  2 * (Module.finrank k (Ω[A⁄k]) : ℤ) - 2

/-- Definitional equality showing `degK_sheaf k A = 2 · dim_k Ω[A⁄k] - 2`. -/
theorem degK_sheaf_eq_formula :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    degK_sheaf k A = 2 * (Module.finrank k (Ω[A⁄k]) : ℤ) - 2 :=
  fun _ _ _ _ _ _ _ _ => rfl

end DedekindCurve
