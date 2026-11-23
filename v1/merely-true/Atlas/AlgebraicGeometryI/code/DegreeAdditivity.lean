/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.ExteriorPower.Basis

noncomputable section

open Submodule

namespace DegreeAdditivity

/-- The "torsion degree" of a module `M` over a domain `R`, defined as the length of its
torsion submodule. Plays the role of `ℓ(𝒯)` in the degree additivity statement. -/
def torsionDegree (R : Type*) (M : Type*)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (torsion R M)

/-- The length of a module decomposes as the sum of its torsion length and the length of
the torsion-free quotient, via the short exact sequence `0 → 𝒯 → M → M/𝒯 → 0`. -/
theorem length_eq_torsionDegree_add {R : Type*} {M : Type*}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Module.length R M = torsionDegree R M + Module.length R (M ⧸ torsion R M) :=
  Module.length_eq_add_of_exact
    (torsion R M).subtype (torsion R M).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

/-- For a torsion module, the torsion degree equals the full length. -/
theorem torsionDegree_of_torsion {R : Type*} {M : Type*}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (htor : Module.IsTorsion R M) :
    torsionDegree R M = Module.length R M := by
  unfold torsionDegree
  have h : torsion R M = ⊤ := by
    ext x; simp only [mem_top, iff_true]
    exact (mem_torsion_iff x).mpr (@htor x)
  rw [h, Module.length_top]

/-- A torsion-free module has torsion degree zero. -/
theorem torsionDegree_of_torsionFree {R : Type*} {M : Type*}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (htf : Module.IsTorsionFree R M) :
    torsionDegree R M = 0 := by
  unfold torsionDegree
  rw [isTorsionFree_iff_torsion_eq_bot.mp htf, Module.length_bot]

/-- The trivial module `PUnit` has torsion degree zero. -/
theorem torsionDegree_zero (R : Type*) [CommRing R] [IsDomain R] :
    torsionDegree R PUnit = 0 := by
  unfold torsionDegree
  exact Module.length_eq_zero

/-- A linear map sends torsion elements to torsion elements. -/
theorem LinearMap.map_torsion_mem {R : Type*} {N M : Type*}
    [CommRing R] [IsDomain R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (f : N →ₗ[R] M) {x : N} (hx : x ∈ torsion R N) :
    f x ∈ torsion R M := by
  rw [mem_torsion_iff] at hx ⊢
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  refine ⟨⟨a, ha⟩, ?_⟩
  show (a : R) • f x = 0
  rw [← f.map_smul]
  have : (a : R) • x = (0 : N) := hax
  rw [this, map_zero]

/-- Lemma 34 (Lecture 22): Length is additive on short exact sequences: for
`0 → N → M → P → 0`, we have `ℓ(M) = ℓ(N) + ℓ(P)`. -/
theorem lemma34_ses_length_additive {R : Type*} [Ring R]
    {N M P : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup P]
    [Module R N] [Module R M] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Module.length R M = Module.length R N + Module.length R P :=
  Module.length_eq_add_of_exact f g hf hg hex

/-- Instantiation of Lemma 34 to a submodule: `ℓ(M) = ℓ(N) + ℓ(M/N)`. -/
theorem lemma34_submodule {R : Type*} {M : Type*}
    [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ
    (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
    (LinearMap.exact_subtype_mkQ N)

/-- Length is monotone with respect to submodule inclusion. -/
theorem length_le_of_submodule {R : Type*} {M : Type*}
    [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) :
    Module.length R N ≤ Module.length R M := by
  rw [lemma34_submodule N]
  exact le_self_add

/-- A uniformizer of a DVR has order one. -/
theorem dvr_ord_uniformizer (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) :
    Ring.ord R π = 1 := by
  unfold Ring.ord
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  exact ⟨Ideal.span {π},
    by rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R,
    ⟨LinearEquiv.refl R _⟩⟩

/-- A power of a uniformizer has order equal to the exponent. -/
theorem dvr_ord_uniformizer_pow (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) (n : ℕ) :
    Ring.ord R (π ^ n) = n := by
  induction n with
  | zero => simp [Ring.ord]
  | succ k ih =>
    have hπ_nzd : π ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero
    rw [pow_succ, Ring.ord_mul R hπ_nzd, ih, dvr_ord_uniformizer R hπ]
    simp [Nat.cast_succ]

/-- Multiplicativity of the order/length on non-zero-divisor products. -/
theorem dvr_determinant_length (R : Type*) [CommRing R] [IsDomain R]
    {a b : R} (hb : b ∈ nonZeroDivisors R) :
    Ring.ord R (a * b) = Ring.ord R a + Ring.ord R b :=
  Ring.ord_mul R hb

/-- The top exterior power `Λⁿ Rⁿ` is free of rank one. -/
theorem top_exterior_power_rank_one (R : Type*) [CommRing R] [Nontrivial R]
    [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (⋀[R]^n (Fin n → R)) = 1 := by
  rw [exteriorPower.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_self, Nat.choose_self]

/-- The `p`-th exterior power of `Rⁿ` vanishes when `p > n`. -/
theorem exterior_power_vanishes_above_rank (R : Type*) [CommRing R] [Nontrivial R]
    [StrongRankCondition R] {n p : ℕ} (hp : n < p) :
    Module.finrank R (⋀[R]^p (Fin n → R)) = 0 := by
  rw [exteriorPower.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_self, Nat.choose_eq_zero_of_lt hp]

/-- Data of a short exact sequence of `R`-modules `0 → N → M → P → 0`, suitable as a defining
relation in `K₀(R)`. -/
structure K0SESRelation (R : Type*) [Ring R] where
  N : Type*
  M : Type*
  P : Type*
  [instN : AddCommGroup N]
  [modN : Module R N]
  [instM : AddCommGroup M]
  [modM : Module R M]
  [instP : AddCommGroup P]
  [modP : Module R P]
  f : N →ₗ[R] M
  g : M →ₗ[R] P
  f_inj : Function.Injective f
  g_surj : Function.Surjective g
  exact : Function.Exact f g

attribute [instance] K0SESRelation.instN K0SESRelation.modN
  K0SESRelation.instM K0SESRelation.modM K0SESRelation.instP K0SESRelation.modP

/-- Module length respects the `K₀` short-exact-sequence relations: it is additive on
sequences `0 → N → M → P → 0`. -/
theorem degree_respects_K0 {R : Type*} [Ring R] (rel : K0SESRelation R) :
    Module.length R rel.M = Module.length R rel.N + Module.length R rel.P :=
  Module.length_eq_add_of_exact rel.f rel.g rel.f_inj rel.g_surj rel.exact

/-- Module length is an isomorphism invariant. -/
theorem degree_respects_iso {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N :=
  e.length_eq

/-- Length is additive on direct products. -/
theorem degree_additive_prod (R : Type*) [Ring R]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (M × N) = Module.length R M + Module.length R N :=
  Module.length_prod R M N

/-- The trivial module has length zero. -/
theorem degree_zero (R : Type*) [Ring R] :
    Module.length R PUnit = 0 := by
  haveI : Subsingleton PUnit := inferInstance
  exact Module.length_eq_zero

/-- A simple module has length one. -/
theorem degree_simple (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Module.length R M = 1 :=
  Module.length_eq_one R M

/-- Modules that are both Artinian and Noetherian have finite length. -/
theorem degree_finite {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsNoetherian R M] :
    Module.length R M ≠ ⊤ :=
  Module.length_ne_top

/-- The localization of a Dedekind domain at a nonzero prime is a DVR. -/
theorem dedekind_localization_is_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] {P : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _

/-- Over a DVR, every finitely generated torsion-free module is free. -/
theorem dvr_torsionFree_is_free (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free R M :=
  inferInstance

end DegreeAdditivity

end
