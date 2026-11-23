/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.GBSplittingExistence

open BigOperators

namespace GBGeometric

/-- A vector bundle on `P^1` of positive rank, presented by its Grothendieck-Birkhoff
splitting `⊕ O(d_i)` with a decreasing tuple of integer degrees. -/
structure P1VectorBundle (k : Type*) [Field k] where
  rank : ℕ
  splittingType : Fin rank → ℤ
  sorted : ∀ i j : Fin rank, i ≤ j → splittingType j ≤ splittingType i
  hrank_pos : 0 < rank

/-- Total degree of `E = ⊕ O(d_i)` on `P^1`: `deg E = ∑ d_i`. -/
def P1VectorBundle.degree {k : Type*} [Field k] (E : P1VectorBundle k) : ℤ :=
  ∑ i, E.splittingType i

/-- Forget the positivity of the rank and recover the abstract `SplittingType` record. -/
def P1VectorBundle.toSplittingType {k : Type*} [Field k]
    (E : P1VectorBundle k) : GBExistence.SplittingType E.rank where
  degrees := E.splittingType
  sorted := E.sorted

/-- `k[x]` is a principal ideal domain (used to access the structure theorem on `P^1`). -/
instance polynomial_pid (k : Type*) [Field k] :
    IsPrincipalIdealRing (Polynomial k) :=
  inferInstance

set_option maxHeartbeats 400000 in
/-- PID structure theorem: a finite free module over `k[x]` is isomorphic to `(k[x])^r` for some `r`. -/
theorem pid_structure_theorem (k : Type*) [Field k]
    (M : Type*) [AddCommGroup M] [Module (Polynomial k) M]
    [Module.Finite (Polynomial k) M] [Module.Free (Polynomial k) M] :
    ∃ r : ℕ, Nonempty (M ≃ₗ[Polynomial k] (Fin r → Polynomial k)) := by
  haveI : Module.IsTorsionFree (Polynomial k) M :=
    (Module.free_iff_isTorsionFree).mp inferInstance
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := Polynomial k) (M := M)
  exact ⟨n, ⟨b.equivFun⟩⟩

/-- Uniqueness of rank for the PID structure theorem: two trivializations have the same number of summands. -/
theorem pid_rank_unique (k : Type*) [Field k]
    (M : Type*) [AddCommGroup M] [Module (Polynomial k) M]
    [Module.Finite (Polynomial k) M] [Module.Free (Polynomial k) M]
    (r s : ℕ)
    (e₁ : M ≃ₗ[Polynomial k] (Fin r → Polynomial k))
    (e₂ : M ≃ₗ[Polynomial k] (Fin s → Polynomial k)) :
    r = s := by
  have h₁ : Module.finrank (Polynomial k) (Fin r → Polynomial k) = r :=
    Module.finrank_fin_fun (Polynomial k)
  have h₂ : Module.finrank (Polynomial k) (Fin s → Polynomial k) = s :=
    Module.finrank_fin_fun (Polynomial k)
  have := (e₁.symm.trans e₂).finrank_eq
  rw [h₁, h₂] at this; exact this

/-- Build a `P1VectorBundle` from an abstract splitting type once a positive-rank witness is given. -/
def splittingTypeToBundle (k : Type*) [Field k] {n : ℕ} (hn : 0 < n)
    (s : GBExistence.SplittingType n) : P1VectorBundle k where
  rank := n
  splittingType := s.degrees
  sorted := s.sorted
  hrank_pos := hn

/-- Round-trip through `toSplittingType` and `splittingTypeToBundle` recovers the original tuple. -/
theorem roundtrip_splitting {k : Type*} [Field k] (E : P1VectorBundle k) :
    (splittingTypeToBundle k E.hrank_pos E.toSplittingType).splittingType = E.splittingType :=
  rfl

/-- Riemann-Roch for a split bundle on `P^1`: `χ(E) = deg E + rk E`. -/
theorem split_bundle_riemann_roch {k : Type*} [Field k]
    (E : P1VectorBundle k) :
    (E.toSplittingType.h0_twisted 0 : ℤ) - (E.toSplittingType.h1_twisted 0 : ℤ) =
      (∑ i, E.splittingType i) + E.rank := by
  exact GBExistence.split_total_degree E.toSplittingType

/-- Bridge to Čech computation: the sum of `χ(O(d_i))` equals `deg E + rk E`. -/
theorem split_bundle_euler_from_cech (k : Type) [Field k]
    (E : P1VectorBundle k) :
    ∑ i, GrothendieckBirkhoff.eulerCharP1 k (E.splittingType i) =
      E.degree + E.rank := by
  exact GrothendieckBirkhoff.split_bundle_rr_P1 k E.rank E.splittingType

/-- Euler characteristic of `O(n)` on `P^1` via Čech cohomology: `χ(O(n)) = n + 1`. -/
theorem line_bundle_euler_cech (k : Type) [Field k] (n : ℤ) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
  SheafCohomology.euler_characteristic k n

/-- Combinatorial `h^0` matches Čech `H^0` dimension for any integer twist `d`. -/
theorem h0_matches_cech (k : Type) [Field k] (d : ℤ) :
    (GBExistence.h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
  by_cases hd : 0 ≤ d
  · exact GBExistence.h0_dim_matches_cohomology k d hd
  · push Not at hd
    exact GBExistence.h0_dim_matches_cohomology_neg k d hd

/-- Combinatorial `h^1` matches Čech `H^1` dimension for any integer twist `d`. -/
theorem h1_matches_cech (k : Type) [Field k] (d : ℤ) :
    (GBExistence.h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
  by_cases hd : 0 ≤ d
  · exact GBExistence.h1_dim_matches_cohomology k d hd
  · push Not at hd
    exact GBExistence.h1_dim_matches_cohomology_neg k d hd

end GBGeometric
