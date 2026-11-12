/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

set_option maxHeartbeats 400000

noncomputable section

open KaehlerDifferential TensorProduct

namespace SmoothClosedSubvariety

section Corollary25

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- Corollary 25 of Lecture 20: For a formally smooth `k`-algebra `R`, the quotient `R ⧸ I` is
formally smooth iff the kernel-to-cotangent map `kerCotangentToTensor k R (R ⧸ I)` splits. -/
theorem corollary25_smooth_closed_subvariety_criterion
    [Algebra.FormallySmooth k R] :
    Algebra.FormallySmooth k (R ⧸ I) ↔
      ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
  Algebra.FormallySmooth.iff_split_injection Ideal.Quotient.mk_surjective

end Corollary25

section Proposition35

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- Proposition 35 (right exactness): The conormal sequence
`I/I² → (R⧸I) ⊗_R Ω[R/k] → Ω[(R⧸I)/k] → 0` is exact at the middle term. -/
theorem proposition35_conormal_right_exact :
    Function.Exact
      (kerCotangentToTensor k R (R ⧸ I))
      (mapBaseChange k R (R ⧸ I)) :=
  exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) Ideal.Quotient.mk_surjective

/-- Proposition 35 (surjectivity): The base-change map
`(R⧸I) ⊗_R Ω[R/k] → Ω[(R⧸I)/k]` is surjective. -/
theorem proposition35_conormal_surjective :
    Function.Surjective (mapBaseChange k R (R ⧸ I)) :=
  mapBaseChange_surjective k R (R ⧸ I) Ideal.Quotient.mk_surjective

end Proposition35

section Corollary26

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- Corollary 26 (injectivity): When both `R` and `R ⧸ I` are formally smooth over `k`,
the conormal map `I/I² → (R⧸I) ⊗_R Ω[R/k]` is injective. -/
theorem corollary26_conormal_ses_injective
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    Function.Injective (kerCotangentToTensor k R (R ⧸ I)) := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := R) (A := R ⧸ I) Ideal.Quotient.mk_surjective).mp inferInstance
  exact Function.HasLeftInverse.injective ⟨l, fun x => LinearMap.ext_iff.mp hl x⟩

/-- Corollary 26 (exactness): The conormal sequence is exact at `(R⧸I) ⊗_R Ω[R/k]`. -/
theorem corollary26_conormal_ses_exact :
    Function.Exact
      (kerCotangentToTensor k R (R ⧸ I))
      (mapBaseChange k R (R ⧸ I)) :=
  exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) Ideal.Quotient.mk_surjective

/-- Corollary 26 (surjectivity): The base-change map in the conormal sequence is surjective. -/
theorem corollary26_conormal_ses_surjective :
    Function.Surjective (mapBaseChange k R (R ⧸ I)) :=
  mapBaseChange_surjective k R (R ⧸ I) Ideal.Quotient.mk_surjective

/-- Corollary 26 (splitting): When both `R` and `R ⧸ I` are formally smooth over `k`,
the conormal short exact sequence splits. -/
theorem corollary26_conormal_ses_split
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
  (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := R) (A := R ⧸ I) Ideal.Quotient.mk_surjective).mp inferInstance

/-- Corollary 26 (direct summand form): In the smooth case, `I/I²` is a locally free direct
summand of `(R⧸I) ⊗_R Ω[R/k]`, realised by an injective map that admits a left inverse. -/
theorem corollary26_conormal_locally_free_direct_summand
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id ∧
      Function.Injective (kerCotangentToTensor k R (R ⧸ I)) := by
  obtain ⟨l, hl⟩ := corollary26_conormal_ses_split k R I
  exact ⟨l, hl, by
    exact Function.HasLeftInverse.injective ⟨l, fun x => LinearMap.ext_iff.mp hl x⟩⟩

/-- Corollary 26 (canonical bundle formula): For a smooth closed subvariety of codimension `c`
in a smooth `d`-dimensional variety, the top exterior power of the ambient cotangent bundle
restricted to `Z` decomposes as the top wedge of `Ω[Z/k]` tensor the wedge of `I/I²`. -/
theorem corollary26_canonical_bundle_formula
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)]
    [Nontrivial (R ⧸ I)]
    [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Free (R ⧸ I) I.Cotangent]
    [Module.Finite (R ⧸ I) I.Cotangent]
    (d c : ℕ)
    (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
    (hc : Module.finrank (R ⧸ I) I.Cotangent = c)
    (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - c) :
    Nonempty (
      ↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I]
      (↥(⋀[R ⧸ I]^(d - c) (Ω[R ⧸ I⁄k]))) ⊗[R ⧸ I]
        (↥(⋀[R ⧸ I]^c I.Cotangent))) := by
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [exteriorPower.finrank_eq (R ⧸ I) d, hd]
  rw [Module.finrank_tensorProduct,
      exteriorPower.finrank_eq (R ⧸ I) (d - c), hdc,
      exteriorPower.finrank_eq (R ⧸ I) c, hc]
  simp [Nat.choose_self]

/-- Corollary 26 (adjunction formula): The divisor case (`c = 1`) of the canonical bundle
formula relating the determinant of the cotangent bundle on `Z` to the conormal line bundle. -/
theorem corollary26_adjunction_formula
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)]
    [Nontrivial (R ⧸ I)]
    [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Free (R ⧸ I) I.Cotangent]
    [Module.Finite (R ⧸ I) I.Cotangent]
    (d : ℕ)
    (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
    (hc : Module.finrank (R ⧸ I) I.Cotangent = 1)
    (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - 1) :
    Nonempty (
      ↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I]
      (↥(⋀[R ⧸ I]^(d - 1) (Ω[R ⧸ I⁄k]))) ⊗[R ⧸ I]
        (↥(⋀[R ⧸ I]^1 I.Cotangent))) :=
  corollary26_canonical_bundle_formula k R I d 1 hd hc hdc

end Corollary26

section AdjunctionTwisting

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- The normal module `N_{Z/X} = Hom_{R⧸I}(I/I², R⧸I)`, dual to the conormal module `I/I²`. -/
abbrev NormalModule (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  Module.Dual (R ⧸ I) I.Cotangent

/-- Adjunction formula with twisting: rewrites the canonical bundle of the subvariety as
the restriction of the ambient canonical bundle twisted by the wedge of the normal bundle. -/
theorem adjunction_formula_with_twisting
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)]
    [Nontrivial (R ⧸ I)]
    [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Free (R ⧸ I) I.Cotangent]
    [Module.Finite (R ⧸ I) I.Cotangent]
    (d c : ℕ)
    (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
    (hc : Module.finrank (R ⧸ I) I.Cotangent = c)
    (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - c) :
    Nonempty (
      ↥(⋀[R ⧸ I]^(d - c) (Ω[R ⧸ I⁄k])) ≃ₗ[R ⧸ I]
      (↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k]))) ⊗[R ⧸ I]
        (↥(⋀[R ⧸ I]^c (NormalModule R I)))) := by
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [exteriorPower.finrank_eq (R ⧸ I) (d - c), hdc]
  rw [Module.finrank_tensorProduct,
      exteriorPower.finrank_eq (R ⧸ I) d, hd,
      exteriorPower.finrank_eq (R ⧸ I) c]
  rw [show Module.finrank (R ⧸ I) (NormalModule R I) = c from by
    rw [Module.finrank_linearMap_self (R ⧸ I) (R ⧸ I) I.Cotangent, hc]]
  simp [Nat.choose_self]

/-- Adjunction formula with twisting for divisors: the special case `c = 1` expressing
the canonical bundle of a smooth divisor in terms of the ambient canonical bundle and
the normal line bundle. -/
theorem adjunction_formula_divisor_twisting
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)]
    [Nontrivial (R ⧸ I)]
    [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
    [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
    [Module.Free (R ⧸ I) I.Cotangent]
    [Module.Finite (R ⧸ I) I.Cotangent]
    (d : ℕ)
    (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
    (hc : Module.finrank (R ⧸ I) I.Cotangent = 1)
    (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - 1) :
    Nonempty (
      ↥(⋀[R ⧸ I]^(d - 1) (Ω[R ⧸ I⁄k])) ≃ₗ[R ⧸ I]
      (↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k]))) ⊗[R ⧸ I]
        (↥(⋀[R ⧸ I]^1 (NormalModule R I)))) :=
  adjunction_formula_with_twisting k R I d 1 hd hc hdc

end AdjunctionTwisting

end SmoothClosedSubvariety

end
