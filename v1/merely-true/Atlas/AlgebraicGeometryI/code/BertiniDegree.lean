/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Length
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

noncomputable section

open MvPolynomial Finset

section Bertini

/-- Partial derivative of a pure power of a variable: `∂_i (X_j^d) = d·X_j^{d-1}` if `i = j`,
otherwise `0`. -/
lemma pderiv_X_pow {k : Type*} [CommRing k] {σ : Type*} [DecidableEq σ]
    (i j : σ) (d : ℕ) :
    (pderiv (R := k) i) ((X j : MvPolynomial σ k) ^ d) =
      if i = j then (d : MvPolynomial σ k) * X j ^ (d - 1) else 0 := by
  rw [Derivation.leibniz_pow, pderiv_X, nsmul_eq_mul]
  split
  · next h => subst h; simp [Pi.single_eq_same]
  · next h => simp [Pi.single, Function.update, Ne.symm h]

/-- Euler's identity: for a homogeneous polynomial `f` of degree `d`, the sum
`∑ xᵢ ∂_i f = d·f`. If all partials vanish at `x`, then `d · f(x) = 0`. -/
theorem homogeneous_euler_vanishing {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d)
    (x : Fin (n + 1) → k)
    (hpd : ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0) :
    (d : k) * MvPolynomial.eval x f = 0 := by
  have euler := hf.sum_X_mul_pderiv
  have h := congr_arg (MvPolynomial.eval x) euler
  simp [map_sum, map_mul, eval_X] at h
  rw [Finset.sum_eq_zero] at h
  · simpa [nsmul_eq_mul] using h
  · intro i _
    simp [hpd i]

/-- When `d ≠ 0` in `k`, vanishing of all partial derivatives at `x` forces `f(x) = 0` for a
homogeneous polynomial of degree `d`. -/
theorem homogeneous_singular_implies_zero {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d)
    (hd : (d : k) ≠ 0) (x : Fin (n + 1) → k)
    (hpd : ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0) :
    MvPolynomial.eval x f = 0 := by
  have h := homogeneous_euler_vanishing f d hf x hpd
  exact (mul_eq_zero.mp h).resolve_left hd

/-- A point `x` is a *singular zero* of `f` if `f(x) = 0` and all partial derivatives vanish at
`x`. These are the singular points of the hypersurface `V(f)`. -/
def IsSingularZero {k : Type*} [CommRing k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (x : Fin (n + 1) → k) : Prop :=
  MvPolynomial.eval x f = 0 ∧
    ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0

/-- For a homogeneous polynomial of degree `d` with `d ≠ 0` in `k`, being a singular zero is
equivalent to all partial derivatives vanishing (Euler's identity makes `f(x) = 0` automatic). -/
theorem singular_zero_iff_partials_vanish {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ) (hf : f.IsHomogeneous d)
    (hd : (d : k) ≠ 0) (x : Fin (n + 1) → k) :
    IsSingularZero f x ↔
      ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0 := by
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro hpd
    exact ⟨homogeneous_singular_implies_zero f d hf hd x hpd, hpd⟩

/-- The *Fermat polynomial* of degree `d` in `n+1` variables: `x₀^d + x₁^d + … + xₙ^d`. -/
def fermatPoly (k : Type*) [CommSemiring k] (n d : ℕ) :
    MvPolynomial (Fin (n + 1)) k :=
  ∑ i : Fin (n + 1), X i ^ d

/-- The Fermat polynomial of degree `d` is homogeneous of degree `d`. -/
theorem fermatPoly_isHomogeneous (k : Type*) [CommSemiring k] (n d : ℕ) :
    (fermatPoly k n d).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro i _
  have h := (isHomogeneous_X k i).pow d
  simp [one_mul] at h
  exact h

/-- Partial derivative of the Fermat polynomial: `∂_i (Σ x_j^d) = d · x_i^{d-1}`. -/
lemma pderiv_fermatPoly {k : Type*} [CommRing k] {n : ℕ} (d : ℕ) (i : Fin (n + 1)) :
    (pderiv i) (fermatPoly k n d) =
      (d : MvPolynomial (Fin (n + 1)) k) * X i ^ (d - 1) := by
  simp only [fermatPoly, map_sum, pderiv_X_pow]
  simp [Finset.mem_univ]

/-- The Fermat hypersurface of degree `d ≥ 2` (with `d ≠ 0` in `k`) has no nonzero singular
points, providing an explicit smooth member of the family of degree-`d` hypersurfaces. -/
theorem fermat_no_nontrivial_singular {k : Type*} [Field k] {n : ℕ} {d : ℕ}
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d)
    (x : Fin (n + 1) → k) (hx : x ≠ 0)
    (hpd : ∀ i, MvPolynomial.eval x (pderiv i (fermatPoly k n d)) = 0) :
    False := by
  have hxi : ∀ i, x i = 0 := by
    intro i
    have hi := hpd i
    rw [pderiv_fermatPoly] at hi
    rw [map_mul, map_natCast, map_pow, eval_X] at hi
    rcases mul_eq_zero.mp hi with h | h
    · exact absurd h hd
    · exact pow_eq_zero_iff (by omega : d - 1 ≠ 0) |>.mp h
  exact hx (funext hxi)

/-- The discriminant locus (where the hypersurface is singular) is a proper subset of the space
of degree-`d` homogeneous polynomials: not every such polynomial is singular. -/
theorem discriminant_locus_proper {k : Type*} [Field k] {n : ℕ} {d : ℕ}
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d) :
    ¬∀ (f : MvPolynomial (Fin (n + 1)) k), f.IsHomogeneous d →
      ∃ x : Fin (n + 1) → k, x ≠ 0 ∧ IsSingularZero f x := by
  intro hall
  obtain ⟨x, hx, _, hpd⟩ := hall (fermatPoly k n d) (fermatPoly_isHomogeneous k n d)
  exact fermat_no_nontrivial_singular hd hd2 x hx hpd

/-- Existence of a smooth degree-`d` hypersurface: there is a homogeneous polynomial of degree `d`
whose partial derivatives do not all vanish simultaneously at any nonzero point. The Fermat
polynomial provides such an example. -/
theorem bertini_smooth_exists {k : Type*} [Field k] {n : ℕ} {d : ℕ}
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d) :
    ∃ f : MvPolynomial (Fin (n + 1)) k,
      f.IsHomogeneous d ∧
      ∀ x : Fin (n + 1) → k, x ≠ 0 →
        ¬∀ i, MvPolynomial.eval x (pderiv i f) = 0 :=
  ⟨fermatPoly k n d, fermatPoly_isHomogeneous k n d,
    fun x hx hpd => fermat_no_nontrivial_singular hd hd2 x hx hpd⟩

/-- The space of smooth hypersurfaces of degree `d ≥ 2` is non-empty: there exists a homogeneous
degree-`d` polynomial with no nonzero singular zeros. -/
theorem smooth_hypersurface_nonempty {k : Type*} [Field k] {n : ℕ} {d : ℕ}
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d) :
    ∃ f : MvPolynomial (Fin (n + 1)) k,
      f.IsHomogeneous d ∧
      ∀ x : Fin (n + 1) → k, x ≠ 0 → ¬IsSingularZero f x := by
  obtain ⟨f, hfhom, hfsmooth⟩ := bertini_smooth_exists hd hd2
  exact ⟨f, hfhom, fun x hx hsing => hfsmooth x hx hsing.2⟩

/-- The *discriminant locus*: the set of degree-`d` homogeneous polynomials whose hypersurface
has a singular point. -/
def discriminantLocus (k : Type*) [Field k] (n d : ℕ) :
    Set (MvPolynomial (Fin (n + 1)) k) :=
  {f | f.IsHomogeneous d ∧ ∃ x : Fin (n + 1) → k, x ≠ 0 ∧ IsSingularZero f x}

/-- Unfolding lemma for `IsSingularZero`. -/
theorem isSingularZero_iff {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (x : Fin (n + 1) → k) :
    IsSingularZero f x ↔
      MvPolynomial.eval x f = 0 ∧
      ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0 := Iff.rfl

/-- The discriminant locus is a proper subset of the space of homogeneous polynomials of degree
`d ≥ 2`: it does not contain the Fermat polynomial. -/
theorem discriminantLocus_ne_univ (k : Type*) [Field k] (n d : ℕ)
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d) :
    discriminantLocus k n d ≠ Set.univ := by
  intro h
  have := Set.mem_univ (fermatPoly k n d)
  rw [← h] at this
  obtain ⟨_, x, hx, _, hpd⟩ := this
  exact fermat_no_nontrivial_singular hd hd2 x hx hpd

/-- The vanishing condition `f(x) = 0` is preserved by `k`-linear combinations. -/
theorem vanishing_at_point_subspace {k : Type*} [Field k] {n : ℕ}
    (x : Fin (n + 1) → k) :
    ∀ (f g : MvPolynomial (Fin (n + 1)) k) (c : k),
      MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0 →
      MvPolynomial.eval x (f + c • g) = 0 := by
  intro f g c hf hg
  simp [map_add, hf, hg]

/-- The set of polynomials having `x` as a singular zero is closed under linear combinations:
if `f` and `g` are both singular at `x`, then so is `f + c·g`. -/
theorem singular_at_point_linear {k : Type*} [Field k] {n : ℕ}
    (x : Fin (n + 1) → k) (f g : MvPolynomial (Fin (n + 1)) k) (c : k) :
    IsSingularZero f x → IsSingularZero g x →
    IsSingularZero (f + c • g) x := by
  intro ⟨hf, hpf⟩ ⟨hg, hpg⟩
  exact ⟨by simp [map_add, hf, hg],
         fun i => by simp [map_add, hpf i, hpg i]⟩

/-- Bertini generic smoothness ingredients: there exists a smooth degree-`d` hypersurface (e.g.
the Fermat polynomial), and the locus of polynomials singular at a fixed point is a linear
subspace. Together these support the standard genericity argument. -/
theorem bertini_generic_smooth {k : Type*} [Field k] {n d : ℕ}
    (hd : (d : k) ≠ 0) (hd2 : 2 ≤ d) :

    (∃ f : MvPolynomial (Fin (n + 1)) k,
      f.IsHomogeneous d ∧ ∀ x, x ≠ 0 → ¬IsSingularZero f x) ∧

    (∀ x : Fin (n + 1) → k,
      ∀ f g : MvPolynomial (Fin (n + 1)) k,
      ∀ c : k,
      IsSingularZero f x → IsSingularZero g x →
      IsSingularZero (f + c • g) x) := by
  exact ⟨⟨fermatPoly k n d, fermatPoly_isHomogeneous k n d,
    fun x hx hsing => fermat_no_nontrivial_singular hd hd2 x hx hsing.2⟩,
    fun x f g c => singular_at_point_linear x f g c⟩

end Bertini

section DegreeAdditivity

/-- Additivity of length on short exact sequences from a submodule:
`length(M) = length(N) + length(M/N)`. -/
theorem length_additive_submodule {R : Type*} {M : Type*}
    [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ
    (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
    (LinearMap.exact_subtype_mkQ N)

/-- Additivity of length on an arbitrary short exact sequence
`0 → N → M → P → 0`: `length(M) = length(N) + length(P)`. -/
theorem length_additive_exact {R : Type*} [Ring R]
    {N M P : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup P]
    [Module R N] [Module R M] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Module.length R M = Module.length R N + Module.length R P :=
  Module.length_eq_add_of_exact f g hf hg hex

/-- A module that is both Artinian and Noetherian has finite length. -/
theorem length_finite_of_artinian_noetherian {R : Type*} {M : Type*}
    [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsNoetherian R M] :
    Module.length R M ≠ ⊤ :=
  Module.length_ne_top

end DegreeAdditivity

section K0DegreeMap

variable (R : Type*) [Ring R]

/-- Two `R`-modules are *equivalent* in `K₀` (with the length map) if they have the same length. -/
def K0LengthRelation (M M' : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] : Prop :=
  Module.length R M = Module.length R M'

/-- Length is invariant under `R`-linear isomorphism. -/
theorem degree_map_respects_iso {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N :=
  e.length_eq

/-- The length map descends to a well-defined map on `K₀`: it is additive on short exact
sequences. -/
theorem degree_map_wellDefined_on_K0
    {N M P : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup P]
    [Module R N] [Module R M] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Module.length R M = Module.length R N + Module.length R P :=
  Module.length_eq_add_of_exact f g hf hg hex

/-- Length is additive on direct products: `length(M × N) = length(M) + length(N)`. -/
theorem degree_map_additive_prod (M N : Type*)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (M × N) = Module.length R M + Module.length R N :=
  Module.length_prod R M N

/-- Length is finite for any module that is both Artinian and Noetherian. -/
theorem degree_map_finite {M : Type*}
    [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsNoetherian R M] :
    Module.length R M ≠ ⊤ :=
  Module.length_ne_top

/-- The zero module has length `0`. -/
theorem degree_map_zero : Module.length R (PUnit : Type) = 0 := by
  have : Subsingleton PUnit := inferInstance
  exact Module.length_eq_zero

/-- A simple `R`-module has length `1`. -/
theorem degree_map_simple (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.length R M = 1 :=
  Module.length_eq_one R M

end K0DegreeMap

end
