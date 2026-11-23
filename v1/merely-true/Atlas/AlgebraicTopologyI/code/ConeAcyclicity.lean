/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.CrossProductExistence

open Finset BigOperators

namespace AlgebraicTopologyI

noncomputable section

/-- The chain-level map induced by the identity continuous map is the identity. -/
lemma SingularChains.map_id {n : ℕ} {X : Type} [TopologicalSpace X]
    (c : SingularChains n X) :
    SingularChains.map (ContinuousMap.id X) c = c := by
  show FreeAbelianGroup.map (SingularSimplex.map (ContinuousMap.id X)) c = c
  suffices h : (SingularSimplex.map (ContinuousMap.id X) :
      SingularSimplex n X → SingularSimplex n X) = _root_.id by
    rw [h, FreeAbelianGroup.map_id]; rfl
  funext σ; exact ContinuousMap.id_comp σ

/-- Any two singular `n`-simplices of `PUnit` are equal, since `PUnit` is a subsingleton. -/
lemma singularSimplex_punit_eq (n : ℕ) (σ τ : SingularSimplex n PUnit) : σ = τ :=
  ContinuousMap.ext fun _ => Subsingleton.elim _ _

/-- Any singular `n`-chain on `PUnit` is an integer multiple of the unique generator
`FreeAbelianGroup.of σ₀`. -/
lemma singularChains_punit_eq_smul (n : ℕ) (σ₀ : SingularSimplex n PUnit)
    (c : SingularChains n PUnit) :
    ∃ m : ℤ, c = m • FreeAbelianGroup.of σ₀ := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of a =>
    exact ⟨1, by rw [one_smul, singularSimplex_punit_eq n a σ₀]⟩
  | neg a =>
    exact ⟨-1, by simp [singularSimplex_punit_eq n a σ₀]⟩
  | add a b ha hb =>
    obtain ⟨m, rfl⟩ := ha; obtain ⟨k, rfl⟩ := hb
    exact ⟨m + k, by rw [add_smul]⟩

/-- If `m • FreeAbelianGroup.of a = 0` in a free abelian group, then the scalar `m` is
zero. -/
lemma FreeAbelianGroup.smul_of_eq_zero {T : Type*} (a : T) (m : ℤ)
    (h : m • FreeAbelianGroup.of a = (0 : FreeAbelianGroup T)) : m = 0 := by
  have : (FreeAbelianGroup.lift (fun _ => (1 : ℤ))) (m • FreeAbelianGroup.of a) = 0 := by
    rw [h, map_zero]
  rw [map_zsmul, FreeAbelianGroup.lift_apply_of] at this
  simpa using this

/-- The alternating sum `∑_{i < N} (-1)^i` equals `1` if `N` is odd and `0` otherwise. -/
lemma alternating_sum_range (N : ℕ) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i = if Odd N then 1 else 0 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]; simp only [Nat.odd_add_one]
    by_cases hk : Odd k
    · simp only [hk, not_true_eq_false, ite_true, ite_false]; rw [hk.neg_one_pow]; ring
    · simp only [hk, not_false_eq_true, ite_false, ite_true]
      rw [(Nat.not_odd_iff_even.mp hk).neg_one_pow]; ring

/-- The alternating sum `∑_{i : Fin (n+2)} (-1)^i` equals `1` if `n` is odd and `0`
otherwise — this captures the value of the boundary map on a chain of constant simplices
on `PUnit`. -/
lemma alternating_sum_fin (n : ℕ) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = if Odd n then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range, alternating_sum_range]
  simp only [show Odd (n + 2) ↔ Odd n from
    ⟨fun ⟨k, hk⟩ => ⟨k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨k + 1, by omega⟩⟩]

/-- The boundary of the singular simplex `FreeAbelianGroup.of σ` on `PUnit` equals the
alternating sum of signs times the unique `n`-simplex generator `σ₀`. -/
lemma boundaryMap_punit_generator (n : ℕ) (σ : SingularSimplex (n + 1) PUnit)
    (σ₀ : SingularSimplex n PUnit) :
    boundaryMap n PUnit (FreeAbelianGroup.of σ) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ := by
  show (FreeAbelianGroup.lift (fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i σ)))
    (FreeAbelianGroup.of σ) = _
  erw [FreeAbelianGroup.lift_apply_of]
  conv_rhs => rw [show (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ =
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀
    from by rw [← Finset.sum_smul]]
  simp_rw [singularSimplex_punit_eq n _ σ₀]

/-- Acyclicity of the singular chain complex of `PUnit` in positive degrees: every
`(n+1)`-cycle on `PUnit` is the boundary of some `(n+2)`-chain. This is the cone-style
acyclicity input feeding into the chain-homotopy machinery for star-shaped regions
(Proposition 5.13). -/
theorem punit_acyclic (n : ℕ) (c : SingularChains (n + 1) PUnit)
    (hc : boundaryMap n PUnit c = 0) :
    ∃ d : SingularChains (n + 2) PUnit, boundaryMap (n + 1) PUnit d = c := by
  let σ₁ : SingularSimplex (n + 1) PUnit := ContinuousMap.const _ PUnit.unit
  let σ₀ : SingularSimplex n PUnit := ContinuousMap.const _ PUnit.unit
  let σ₂ : SingularSimplex (n + 2) PUnit := ContinuousMap.const _ PUnit.unit
  obtain ⟨m, rfl⟩ := singularChains_punit_eq_smul (n + 1) σ₁ c
  have hbd := boundaryMap_punit_generator n σ₁ σ₀
  have hc2 : m * (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = 0 := by
    have h1 : (boundaryMap n PUnit) (m • FreeAbelianGroup.of σ₁) =
      m • (boundaryMap n PUnit) (FreeAbelianGroup.of σ₁) := map_zsmul _ m _
    rw [h1, hbd] at hc
    have h2 : (m * (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ))) • FreeAbelianGroup.of σ₀ = 0 := by
      rw [mul_comm, mul_smul]
      have := (smul_comm (m : ℤ)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) (FreeAbelianGroup.of σ₀)).symm
      exact this ▸ hc
    exact FreeAbelianGroup.smul_of_eq_zero σ₀ _ h2
  rw [alternating_sum_fin] at hc2
  by_cases hn : Odd n
  · simp only [hn, ite_true, mul_one] at hc2
    rw [hc2, zero_smul]
    exact ⟨0, map_zero _⟩
  · have hbd2 := boundaryMap_punit_generator (n + 1) σ₂ σ₁
    refine ⟨m • FreeAbelianGroup.of σ₂, ?_⟩
    have h2 : (boundaryMap (n + 1) PUnit) (m • FreeAbelianGroup.of σ₂) =
      m • (boundaryMap (n + 1) PUnit) (FreeAbelianGroup.of σ₂) := map_zsmul _ m _
    rw [h2, hbd2]
    have hodd : Odd (n + 1) := Nat.odd_add_one.mpr hn
    simp only [alternating_sum_fin, hodd, ite_true, one_smul]
    rfl

end

end AlgebraicTopologyI
