/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent

noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The property of being a standard smooth `R`-algebra of relative dimension `n`. -/
abbrev IsSmoothMorphismOfRelDim (n : ℕ) (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Algebra.IsStandardSmoothOfRelativeDimension n R S


/-- If `S` is a standard smooth `R`-algebra of relative dimension `n`, then the module of Kähler
differentials `Ω[S⁄R]` has rank `n` over `S`. -/
theorem smooth_relDim_rank_kaehler (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Nontrivial S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Module.rank S (Ω[S⁄R]) = n :=
  Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

/-- For a standard smooth `R`-algebra `S`, the Kähler differential module `Ω[S⁄R]` is free. -/
theorem smooth_kaehler_free (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Module.Free S (Ω[S⁄R]) :=
  Algebra.IsStandardSmooth.free_kaehlerDifferential


/-- An `Algebra k A` is smooth of dimension `d` when its module of Kähler differentials
`Ω[A⁄k]` is free, finite, and has rank `d` over `A`. -/
class IsSmoothOfDimension (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] (d : ℕ) : Prop where
  free : Module.Free A (Ω[A⁄k])
  finite : Module.Finite A (Ω[A⁄k])
  finrank_eq : Module.finrank A (Ω[A⁄k]) = d


/-- The canonical module ω_X = ∧^d Ω_X (Def 37, Lec 19): the `d`-th exterior power of the
module of Kähler differentials. -/
def canonicalModule (k : Type u) (A : Type v) [CommRing k] [CommRing A]
    [Algebra k A] (d : ℕ) : Submodule A (ExteriorAlgebra A (Ω[A⁄k])) :=
  ⋀[A]^d (Ω[A⁄k])


/-- The canonical module of a smooth `k`-algebra of dimension `d` is free over `A`. -/
theorem canonicalModule_free (k : Type u) (A : Type v) [CommRing k]
    [CommRing A] [Algebra k A] (d : ℕ)
    [h : IsSmoothOfDimension k A d] :
    Module.Free A (↥(canonicalModule k A d)) := by
  haveI := h.free
  haveI := h.finite
  show Module.Free A ↥(⋀[A]^d (Ω[A⁄k]))
  exact inferInstance

/-- The canonical module of a smooth `k`-algebra of dimension `d` is locally free of rank one,
matching the line bundle interpretation of ω_X. -/
theorem canonicalModule_finrank_eq_one (k : Type u) (A : Type v) [CommRing k]
    [CommRing A] [Algebra k A] [Nontrivial A] (d : ℕ)
    [h : IsSmoothOfDimension k A d] :
    Module.finrank A (↥(canonicalModule k A d)) = 1 := by
  haveI := h.free
  haveI := h.finite
  show Module.finrank A ↥(⋀[A]^d (Ω[A⁄k])) = 1
  rw [exteriorPower.finrank_eq, h.finrank_eq, Nat.choose_self]


/-- The conormal module of an ideal `I ⊆ A`, namely `I / I²`. -/
abbrev conormalModule (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  I.Cotangent


/-- The conormal module of an ideal in a Noetherian ring is Noetherian. -/
theorem conormalModule_isNoetherian (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    IsNoetherian A (conormalModule A I) := by
  change IsNoetherian A (↥I ⧸ (I • ⊤ : Submodule A ↥I))
  exact isNoetherian_quotient _

/-- The conormal module of an ideal in a Noetherian ring is finitely generated. -/
theorem conormalModule_finite_of_noetherian (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    Module.Finite A (conormalModule A I) := by
  haveI := conormalModule_isNoetherian A I
  infer_instance

end CanonicalSheafDef

end
