/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Atlas.AlgebraicGeometryI.code.CanonicalSheafDef
import Atlas.AlgebraicGeometryI.code.TwistSheaf

noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section KahlerMvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/-- Abbreviation for the polynomial ring `k[x₀, …, x_n]` over `k` in `n + 1` variables. -/
abbrev PolyRing := MvPolynomial (Fin (n + 1)) k

/-- Canonical basis of `Ω[k[x₀,…,x_n]⁄k]` given by the `dxᵢ`. -/
def kahlerBasis_mvPolynomial :
    Basis (Fin (n + 1)) (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  mvPolynomialBasis k (Fin (n + 1))

/-- The Kähler differential module of a polynomial ring is free. -/
theorem kahler_mvPolynomial_free :
    Module.Free (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  inferInstance

/-- The rank of the Kähler differential module of `k[x₀,…,x_n]` is `n + 1`. -/
theorem kahler_mvPolynomial_finrank :
    Module.finrank (PolyRing k n) (Ω[PolyRing k n⁄k]) = n + 1 := by
  rw [Module.finrank_eq_card_basis (kahlerBasis_mvPolynomial k n), Fintype.card_fin]

/-- The Kähler differential module of `k[x₀,…,x_n]` is finitely generated. -/
instance kahler_mvPolynomial_finite :
    Module.Finite (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  Module.Finite.of_basis (kahlerBasis_mvPolynomial k n)

/-- Coordinate isomorphism between Kähler differentials of `k[x₀,…,x_n]` and the rank-`(n+1)`
free module. -/
def kahler_mvPolynomial_equivFun :
    Ω[PolyRing k n⁄k] ≃ₗ[PolyRing k n] (Fin (n + 1) → PolyRing k n) :=
  (kahlerBasis_mvPolynomial k n).equivFun

end KahlerMvPolynomial

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- A polynomial ring `k[x₀, …, x_n]` is smooth of dimension `n + 1` over `k`. -/
instance polyRing_isSmoothOfDimension :
    IsSmoothOfDimension k (PolyRing k n) (n + 1) where
  free := inferInstance
  finite := Module.Finite.of_basis (kahlerBasis_mvPolynomial k n)
  finrank_eq := kahler_mvPolynomial_finrank k n

/-- The canonical module of `k[x₀,…,x_n]` in dimension `n + 1` is the top exterior power of
the Kähler differentials. -/
theorem canonicalModule_polyRing_eq :
    canonicalModule k (PolyRing k n) (n + 1) = ⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k]) :=
  rfl

/-- The canonical module of `k[x₀,…,x_n]` in dimension `n + 1` has rank `1`. -/
theorem canonicalModule_polyRing_finrank :
    Module.finrank (PolyRing k n)
      (↥(canonicalModule k (PolyRing k n) (n + 1))) = 1 :=
  canonicalModule_finrank_eq_one k (PolyRing k n) (n + 1)

/-- The canonical module of `k[x₀,…,x_n]` is a free module. -/
theorem canonicalModule_polyRing_free :
    Module.Free (PolyRing k n)
      (↥(canonicalModule k (PolyRing k n) (n + 1))) :=
  canonicalModule_free k (PolyRing k n) (n + 1)

end MvPolynomialSmooth

section CanonicalBundle

variable (k : Type u) [Field k] (n : ℕ)

/-- The top exterior power of Kähler differentials has rank `1`. -/
theorem topExteriorPower_kahler_finrank :
    Module.finrank (PolyRing k n)
      (⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k])) = 1 := by
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank, Nat.choose_self]

/-- The top exterior power of Kähler differentials is a free module. -/
theorem topExteriorPower_kahler_free :
    Module.Free (PolyRing k n)
      (⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k])) :=
  inferInstance

/-- Exterior powers above the dimension vanish: `Λ^p Ω = 0` for `p > n + 1`. -/
theorem exteriorPower_kahler_finrank_zero (p : ℕ) (hp : n + 1 < p) :
    Module.finrank (PolyRing k n)
      (⋀[PolyRing k n]^p (Ω[PolyRing k n⁄k])) = 0 := by
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank, Nat.choose_eq_zero_of_lt hp]

/-- Rank of the `p`-th exterior power of Kähler differentials: `(n + 1 choose p)`. -/
theorem exteriorPower_kahler_finrank (p : ℕ) :
    Module.finrank (PolyRing k n)
      (⋀[PolyRing k n]^p (Ω[PolyRing k n⁄k])) = Nat.choose (n + 1) p := by
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank]

end CanonicalBundle

section DirectSumRank

variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

/-- The free `R`-module `Fin (n + 1) → R` has rank `n + 1`. -/
theorem finrank_direct_sum_free :
    Module.finrank R (Fin (n + 1) → R) = n + 1 := by
  rw [Module.finrank_fin_fun]

/-- The top exterior power of the rank-`(n+1)` free `R`-module has rank `1`. -/
theorem finrank_top_exterior_direct_sum :
    Module.finrank R (⋀[R]^(n + 1) (Fin (n + 1) → R)) = 1 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun, Nat.choose_self]

end DirectSumRank

namespace CanonicalBundleProj

open QCohProjective TwistSheaf

variable (k : Type u) [Field k] (n : ℕ)

/-- Type of graded `k`-linear maps in fixed degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinMap (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearMap k k _ _ (RingHom.id k) (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- Type of graded `k`-linear equivalences in degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinEquiv (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k)
    ⟨RingHom.id_comp _, RingHom.comp_id _⟩ ⟨RingHom.id_comp _, RingHom.comp_id _⟩
    (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- A short exact sequence of graded `k`-modules on `P^n`, given by maps in every degree
together with proofs of injectivity, surjectivity and exactness in the middle. -/
structure GradedSES where
  left : GradedModuleData.{u, u} k n
  middle : GradedModuleData.{u, u} k n
  right : GradedModuleData.{u, u} k n
  f : ∀ d : ℤ, GrLinMap k n left middle d
  g : ∀ d : ℤ, GrLinMap k n middle right d
  f_injective : ∀ d : ℤ, Function.Injective (f d)
  g_surjective : ∀ d : ℤ, Function.Surjective (g d)
  exact_middle : ∀ (d : ℤ) (x : middle.component d),
    @Eq (right.component d) (g d x)
      (@Zero.zero (right.component d) (right.instACG d).toAddCommMonoid.toZero) ↔
    ∃ a : left.component d, (f d) a = x

/-- Middle term of the Euler sequence on `P^n`: the direct sum `O(-1)^{n+1}`. -/
def directSumTwist : GradedModuleData.{u, u} k n where
  component d := Fin (n + 1) → (serreTwist k n (-1)).component d
  instACG _d := Pi.addCommGroup
  instMod d := @Pi.module (Fin (n + 1)) (fun _ => (serreTwist k n (-1)).component d) k _
    (fun _ => ((serreTwist k n (-1)).instACG d).toAddCommMonoid)
    (fun _ => (serreTwist k n (-1)).instMod d)
  gsmul i j s v := fun idx =>
    (serreTwist k n (-1)).gsmul i j s (v idx)

/-- The structure sheaf provides a default graded module on `P^n`, giving inhabitedness. -/
instance : Nonempty (GradedModuleData.{u, u} k n) :=
  ⟨structureSheafData k n⟩




/-- Determinant of `O(-1)^{n+1}` is `O(-(n+1))`: the integer identity `(n+1) · (-1) = -(n+1)`. -/
theorem det_direct_sum_twist :
    (n + 1 : ℤ) * (-1 : ℤ) = -(↑n + 1 : ℤ) := by ring


/-- Numerical identity `-(n + 1) = -(↑(n + 1))` used when rewriting the canonical twist. -/
theorem canonical_twist_eq : (-(↑n + 1 : ℤ)) = -(↑(n + 1) : ℤ) := by
  push_cast; ring


/-- Predicate: a graded module `M` on `P^n` is isomorphic to the twisted sheaf `O(d)`. -/
def HasTwistDegree (M : GradedModuleData.{u, u} k n) (d : ℤ) : Prop :=
  ∀ i : ℤ, Nonempty (GrLinEquiv k n M (serreTwist k n d) i)


end CanonicalBundleProj

end
