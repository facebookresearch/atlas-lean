/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Trace

set_option maxHeartbeats 400000

open KaehlerDifferential Module

noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]

/-- Proposition 35(a). For a formally smooth `R`-algebra `A`, the module of Kähler
differentials `Ω_{A/R}` is projective. -/
theorem prop35a_smooth_kahler_projective [Algebra.FormallySmooth R A] :
    Module.Projective A (Ω[A⁄R]) :=
  Algebra.FormallySmooth.projective_kaehlerDifferential

/-- Proposition 35(b) — exactness of the conormal sequence at the middle term: for a
surjection `A → B`, the image of `I/I² → B ⊗_A Ω_{A/R}` is the kernel of the map to
`Ω_{B/R}`. -/
theorem prop35b_conormal_exact (B : Type w) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    (hAB : Function.Surjective (algebraMap A B)) :
    LinearMap.range (kerCotangentToTensor R A B) =
      (LinearMap.ker (mapBaseChange R A B)).restrictScalars A :=
  range_kerCotangentToTensor R A B hAB

/-- Proposition 35(b) — the map `Ω_{A/R} ⊗_A B → Ω_{B/R}` is surjective. -/
theorem prop35b_conormal_surjective (B : Type w) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    Function.Surjective (KaehlerDifferential.map R A B B) :=
  KaehlerDifferential.map_surjective R A B

/-- Proposition 35(b) — exactness of the Jacobi-Zariski sequence
`B ⊗_A Ω_{A/R} → Ω_{B/R}` at `Ω_{B/R}`. -/
theorem prop35b_jacobi_zariski_exact (B : Type w) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    Function.Exact (mapBaseChange R A B) (KaehlerDifferential.map R A B B) :=
  exact_mapBaseChange_map R A B

/-- Proposition 35(c). For a formally smooth `R`-algebra `A` with a formally smooth
presentation `P`, the conormal map `P.cotangentComplex` is injective. -/
theorem prop35c_smooth_conormal_injective
    [Algebra.FormallySmooth R A] (P : Algebra.Extension R A)
    [Algebra.FormallySmooth R P.Ring] :
    Function.Injective P.cotangentComplex := by
  rw [P.cotangentComplex_injective_iff]
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

end Proposition35

section Corollary25

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]

/-- Corollary 25 (Lecture 20). A `R`-algebra `B` is formally smooth iff `Ω_{B/R}` is
projective over `B` and the first cotangent cohomology `H¹(L_{B/R})` vanishes. -/
theorem cor25_smooth_criterion (B : Type w) [CommRing B] [Algebra R B] :
    Algebra.FormallySmooth R B ↔
      (Module.Projective B (Ω[B⁄R]) ∧ Subsingleton (Algebra.H1Cotangent R B)) :=
  Algebra.formallySmooth_iff R B

/-- Corollary 25 — conormal injectivity: for a formally smooth `A` and surjection `A → B`,
the conormal map is injective iff `H¹(L_{B/R})` vanishes. -/
theorem cor25_conormal_injective_iff_h1_vanishes
    [Algebra.FormallySmooth R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    (hAB : Function.Surjective (algebraMap A B)) :
    Function.Injective (kerCotangentToTensor R A B) ↔
      Subsingleton (Algebra.H1Cotangent R B) :=
  Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hAB

end Corollary25

section EulerSequence

variable (k : Type u) [Field k] (n : ℕ)

/-- Shorthand for the polynomial ring `k[x_0, …, x_n]` used in the Euler sequence section. -/
abbrev PolyRingLec20 := MvPolynomial (Fin (n + 1)) k

/-- The standard basis `(dx_0, …, dx_n)` of `Ω_{k[x_0,…,x_n]/k}` as a free module of
rank `n + 1`. -/
def euler_seq_kahler_basis :
    Basis (Fin (n + 1)) (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  KaehlerDifferential.mvPolynomialBasis k (Fin (n + 1))

/-- The module of Kähler differentials of `k[x_0,…,x_n]` has rank `n + 1`. -/
theorem euler_seq_kahler_rank :
    Module.finrank (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) = n + 1 := by
  rw [Module.finrank_eq_card_basis (euler_seq_kahler_basis k n), Fintype.card_fin]

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is free. -/
instance euler_seq_kahler_free :
    Module.Free (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  inferInstance

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is finitely generated. -/
instance euler_seq_kahler_finite :
    Module.Finite (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  Module.Finite.of_basis (euler_seq_kahler_basis k n)

/-- The top exterior power `∧^{n+1} Ω` of the Kähler differentials of `k[x_0,…,x_n]` is
free of rank one (the canonical module on affine `(n+1)`-space). -/
theorem euler_seq_canonical_rank :
    Module.finrank (PolyRingLec20 k n) (⋀[PolyRingLec20 k n]^(n + 1) (Ω[PolyRingLec20 k n⁄k])) = 1 := by
  rw [exteriorPower.finrank_eq]
  rw [Module.finrank_eq_card_basis (euler_seq_kahler_basis k n)]
  simp [Fintype.card_fin, Nat.choose_self]

end EulerSequence

section TautologicalBundle

variable (F : Type u) [Field F]
variable (W : Type v) [AddCommGroup W] [Module F W]

/-- The tautological subspace `V ⊂ W` associated to a point `V ∈ Gr(k, W)`. -/
def tautologicalSubspace (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Submodule F W :=
  V.toSubmodule

/-- The tautological subspace is, by definition, just `V.toSubmodule`. -/
@[simp]
theorem tautologicalSubspace_eq (kk : ℕ) (V : Module.Grassmannian F W kk) :
    tautologicalSubspace F W kk V = V.toSubmodule :=
  rfl

/-- The tautological quotient bundle fibre `W/V` at a point `V ∈ Gr(k, W)`. -/
abbrev tautologicalQuotient (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  W ⧸ V.toSubmodule

/-- The tautological quotient `W/V` is a finite `F`-module. -/
instance tautologicalQuotient_finite (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.Finite F (tautologicalQuotient F W kk V) :=
  V.finite_quotient

/-- The tautological quotient `W/V` is a projective `F`-module. -/
instance tautologicalQuotient_projective (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.Projective F (tautologicalQuotient F W kk V) :=
  V.projective_quotient

/-- The tautological quotient bundle has constant rank `k` at every prime of the base. -/
theorem tautological_rank_constant (kk : ℕ) (V : Module.Grassmannian F W kk) :
    ∀ p, rankAtStalk (R := F) (W ⧸ V.toSubmodule) p = kk :=
  V.rankAtStalk_eq

/-- The quotient `W/V` at a point `V ∈ Gr(k, W)` has dimension `k`. -/
theorem grassmannian_quotient_finrank (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.finrank F (W ⧸ V.toSubmodule) = kk := by
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  have h1 := Module.rankAtStalk_eq_finrank_of_free (R := F) (M := W ⧸ V.toSubmodule)
  have h2 := V.rankAtStalk_eq (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  rw [h1] at h2
  exact Nat.cast_injective h2

/-- The dimension of `V ⊂ W` at a point `V ∈ Gr(k, W)` is `dim W - k`. -/
theorem grassmannian_submodule_finrank [FiniteDimensional F W]
    (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.finrank F (↥V.toSubmodule) = Module.finrank F W - kk := by
  have hQ := grassmannian_quotient_finrank F W kk V
  have := Submodule.finrank_quotient_add_finrank V.toSubmodule
  omega

end TautologicalBundle

section Proposition37

variable (F : Type u) [Field F]
variable (W : Type v) [AddCommGroup W] [Module F W]

/-- Tangent space of the Grassmannian at a point `V`, identified with `Hom(V, W/V)`. -/
abbrev grassmannianTangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)

/-- Cotangent space of the Grassmannian at a point `V`, identified with `Hom(W/V, V)`. -/
abbrev grassmannianCotangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  (W ⧸ V.toSubmodule) →ₗ[F] V.toSubmodule

/-- Proposition 37 (Lecture 20). The tangent space `Hom(V, W/V)` of `Gr(k, W)` at `V` has
dimension `dim V · dim(W/V)`. -/
theorem prop37_grassmannian_tangent_dim
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule]
    [FiniteDimensional F (W ⧸ V.toSubmodule)] :
    Module.finrank F (grassmannianTangentSpace F W kk V) =
      Module.finrank F (↥V.toSubmodule) * Module.finrank F (W ⧸ V.toSubmodule) := by
  change Module.finrank F (↥V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)) = _
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  exact Module.finrank_linearMap F F (↥V.toSubmodule) (W ⧸ V.toSubmodule)

/-- Proposition 37 (Lecture 20). The cotangent space `Hom(W/V, V)` of `Gr(k, W)` at `V` has
dimension `dim(W/V) · dim V`. -/
theorem prop37_grassmannian_cotangent_dim
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule]
    [FiniteDimensional F (W ⧸ V.toSubmodule)] :
    Module.finrank F (grassmannianCotangentSpace F W kk V) =
      Module.finrank F (W ⧸ V.toSubmodule) * Module.finrank F (↥V.toSubmodule) := by
  change Module.finrank F ((W ⧸ V.toSubmodule) →ₗ[F] ↥V.toSubmodule) = _
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  exact Module.finrank_linearMap F F (W ⧸ V.toSubmodule) (↥V.toSubmodule)

/-- The tangent and cotangent spaces of the Grassmannian have equal dimension. -/
theorem prop37_tangent_eq_cotangent_dim
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule]
    [FiniteDimensional F (W ⧸ V.toSubmodule)] :
    Module.finrank F (grassmannianTangentSpace F W kk V) =
    Module.finrank F (grassmannianCotangentSpace F W kk V) := by
  rw [prop37_grassmannian_tangent_dim, prop37_grassmannian_cotangent_dim]
  ring

/-- Specialisation to `Gr(1, W) = ℙ(W)`: the tangent space at `V` has dimension
`dim V · dim(W/V)`. -/
theorem prop37_euler_specialization_dim
    [FiniteDimensional F W] (V : Module.Grassmannian F W 1)
    [FiniteDimensional F V.toSubmodule]
    [FiniteDimensional F (W ⧸ V.toSubmodule)] :
    Module.finrank F (grassmannianTangentSpace F W 1 V) =
      Module.finrank F (↥V.toSubmodule) * Module.finrank F (W ⧸ V.toSubmodule) :=
  prop37_grassmannian_tangent_dim F W 1 V

/-- The tangent space of `ℙⁿ` at every point has dimension `n`. -/
theorem prop37_projective_space_dim
    (n : ℕ) [FiniteDimensional F W]
    (hW : Module.finrank F W = n + 1)
    (V : Module.Grassmannian F W 1) :
    Module.finrank F (grassmannianTangentSpace F W 1 V) = n := by
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule :=
    Submodule.finiteDimensional_of_le le_top
  rw [prop37_grassmannian_tangent_dim]
  have hQ : Module.finrank F (W ⧸ V.toSubmodule) = 1 :=
    grassmannian_quotient_finrank F W 1 V
  have hV : Module.finrank F (↥V.toSubmodule) = n := by
    have := grassmannian_submodule_finrank F W 1 V
    omega
  rw [hV, hQ]
  ring

end Proposition37

end
