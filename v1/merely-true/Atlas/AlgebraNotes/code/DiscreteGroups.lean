/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace DiscreteGroups

abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev M₂ := E2 ≃ᵃⁱ[ℝ] E2

def translationPart (f : M₂) : E2 := f 0

def linearPart (f : M₂) : E2 ≃ₗᵢ[ℝ] E2 := f.linearIsometryEquiv

def IsPureTranslation (f : M₂) : Prop :=
  linearPart f = LinearIsometryEquiv.refl ℝ E2

def rotationAngle (f : M₂) : ℝ :=
  ‖(linearPart f).toLinearIsometry.toContinuousLinearMap - ContinuousLinearMap.id ℝ E2‖

def IsDiscrete (G : Subgroup M₂) : Prop :=
  ∃ ε > 0, (∀ f ∈ G, IsPureTranslation f → f ≠ 1 → ‖translationPart f‖ ≥ ε) ∧
            (∀ f ∈ G, linearPart f ≠ LinearIsometryEquiv.refl ℝ E2 → rotationAngle f ≥ ε)

def pointGroupSet (G : Subgroup M₂) : Set (E2 ≃ₗᵢ[ℝ] E2) :=
  {A | ∃ f ∈ G, linearPart f = A}

def translationLattice (G : Subgroup M₂) : Set E2 :=
  {v : E2 | (AffineIsometryEquiv.constVAdd ℝ E2 v : M₂) ∈ G}

lemma conj_translation (g : M₂) (v : E2) :
    g * (AffineIsometryEquiv.constVAdd ℝ E2 v) * g⁻¹ =
    AffineIsometryEquiv.constVAdd ℝ E2 (g.linearIsometryEquiv v) := by
  apply AffineIsometryEquiv.ext
  intro x
  change (g⁻¹).trans ((AffineIsometryEquiv.constVAdd ℝ E2 v).trans g) x = _
  simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply]
  change g (v +ᵥ (g⁻¹ x)) = (g.linearIsometryEquiv v) +ᵥ x
  rw [g.map_vadd]
  simp [AffineIsometryEquiv.apply_symm_apply]

theorem point_group_preserves_lattice (G : Subgroup M₂)
    (A : E2 ≃ₗᵢ[ℝ] E2) (hA : A ∈ pointGroupSet G)
    (v : E2) (hv : v ∈ translationLattice G) :
    A v ∈ translationLattice G := by
  obtain ⟨g, hg, hgA⟩ := hA
  show (AffineIsometryEquiv.constVAdd ℝ E2 (A v) : M₂) ∈ G
  have hAv : g.linearIsometryEquiv v = A v := by
    simp only [← hgA, linearPart]
  rw [← hAv, ← conj_translation g v]
  exact G.mul_mem (G.mul_mem hg hv) (G.inv_mem hg)

set_option maxHeartbeats 400000 in
theorem discrete_subgroup_R2_classification
    (G : AddSubgroup E2) [DiscreteTopology G] :
    G = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) := by
  set L := G.toIntSubmodule
  haveI hdt : DiscreteTopology L := ‹DiscreteTopology G›
  haveI hfree : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
  haveI hfin : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L

  set_option backward.isDefEq.respectTransparency false in
  have hrank : Module.finrank ℤ L ≤ 2 := by
    have hkey : Set.finrank ℝ (L : Set E2) = Set.finrank ℤ (L : Set E2) :=
      Real.finrank_eq_int_finrank_of_discrete (by rwa [Submodule.span_eq])
    have h1 : Set.finrank ℤ (L : Set E2) = Module.finrank ℤ L := by
      unfold Set.finrank; rw [Submodule.span_eq]
    have h2 : Set.finrank ℝ (L : Set E2) ≤ 2 := by
      unfold Set.finrank
      calc Module.finrank ℝ (Submodule.span ℝ (L : Set _))
          ≤ Module.finrank ℝ E2 := Submodule.finrank_le _
        _ = 2 := by simp [Fintype.card_fin]
    linarith

  have h1case : Module.finrank ℤ L = 1 →
      ∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α := by
    intro h1
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 1 := by
      rw [← Module.finrank_eq_card_chooseBasisIndex]; exact h1
    obtain ⟨g, hg⟩ := Fintype.card_eq_one_iff.mp hcard
    set b := Module.Free.chooseBasis ℤ L
    set α : E2 := (b g).val
    refine ⟨α, ?_, ?_⟩
    · intro heq; exact b.ne_zero g (Subtype.val_injective heq)
    · ext x; constructor
      · intro hx
        have huniv : (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ L)) = {g} := by
          ext i; simp [hg i]
        have heq := b.sum_equivFun ⟨x, hx⟩
        rw [huniv, Finset.sum_singleton] at heq
        rw [AddSubgroup.mem_zmultiples_iff]
        exact ⟨b.equivFun ⟨x, hx⟩ g, by
          have := congr_arg Subtype.val heq
          simp only [Submodule.coe_smul] at this; exact this⟩
      · intro hx
        rw [AddSubgroup.mem_zmultiples_iff] at hx
        obtain ⟨n, rfl⟩ := hx
        exact G.zsmul_mem (b g).2 n

  have h2case : Module.finrank ℤ L = 2 →
      ∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
        G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b := by
    intro h2
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 2 := by
      rw [← Module.finrank_eq_card_chooseBasisIndex]; exact h2
    set B : Module.Basis (Fin 2) ℤ L :=
      (Module.Free.chooseBasis ℤ L).reindex
        (Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin]))

    refine ⟨(B 0).val, (B 1).val, ?_, ?_⟩
    ·


      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      ·
        set S := Submodule.span ℝ (Set.range ![(B 0).val, (B 1).val])
        set_option backward.isDefEq.respectTransparency false in
        have hspan_top : Submodule.span ℝ (L : Set E2) = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          have hk : Set.finrank ℝ (L : Set E2) = Set.finrank ℤ (L : Set E2) :=
            Real.finrank_eq_int_finrank_of_discrete (by rwa [Submodule.span_eq])
          unfold Set.finrank at hk
          rw [Submodule.span_eq] at hk
          linarith [show Module.finrank ℝ E2 = 2 from by simp [Fintype.card_fin]]
        suffices hsub : (L : Set E2) ⊆ (S : Set E2) by
          rw [← hspan_top]; exact Submodule.span_le.mpr hsub
        intro y hy
        have hcoeffs := B.sum_equivFun ⟨y, hy⟩
        have hval := congr_arg Subtype.val hcoeffs
        simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
        rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide] at hval
        simp only [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)] at hval
        rw [← hval]
        have hv0 : (B 0).val ∈ S := Submodule.subset_span (Set.mem_range.mpr ⟨0, rfl⟩)
        have hv1 : (B 1).val ∈ S := Submodule.subset_span (Set.mem_range.mpr ⟨1, rfl⟩)
        have h0 : B.equivFun ⟨y, hy⟩ 0 • (B 0).val ∈ S := by
          rw [show B.equivFun ⟨y, hy⟩ 0 • (B 0).val =
              (B.equivFun ⟨y, hy⟩ 0 : ℝ) • (B 0).val from
            (Int.cast_smul_eq_zsmul ℝ _ _).symm]
          exact S.smul_mem _ hv0
        have h1 : B.equivFun ⟨y, hy⟩ 1 • (B 1).val ∈ S := by
          rw [show B.equivFun ⟨y, hy⟩ 1 • (B 1).val =
              (B.equivFun ⟨y, hy⟩ 1 : ℝ) • (B 1).val from
            (Int.cast_smul_eq_zsmul ℝ _ _).symm]
          exact S.smul_mem _ hv1
        exact S.add_mem h0 h1
      · simp [Fintype.card_fin]

    ·
      ext x
      simp only [AddSubgroup.mem_sup, AddSubgroup.mem_zmultiples_iff]
      constructor
      · intro hx
        have heq := B.sum_equivFun ⟨x, hx⟩
        rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide] at heq
        simp only [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)] at heq
        have hval := congr_arg Subtype.val heq
        simp only [Submodule.coe_add, Submodule.coe_smul] at hval
        exact ⟨_, ⟨B.equivFun ⟨x, hx⟩ 0, rfl⟩, _, ⟨B.equivFun ⟨x, hx⟩ 1, rfl⟩, hval⟩

      · intro ⟨_, ⟨na, rfl⟩, _, ⟨nb, rfl⟩, hsum⟩
        rw [← hsum]
        exact G.add_mem (G.zsmul_mem (B 0).2 na) (G.zsmul_mem (B 1).2 nb)

  rcases Nat.eq_or_lt_of_le hrank with h2 | h12
  · exact Or.inr (Or.inr (h2case h2))

  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h12) with h1 | h01
    · exact Or.inr (Or.inl (h1case h1))
    · left
      have h0 : Module.finrank ℤ L = 0 := by omega
      have hsub : Subsingleton L := (Module.finrank_eq_zero_iff_of_free ℤ L).mp h0
      ext x; simp only [AddSubgroup.mem_bot]
      exact ⟨fun hx => congr_arg Subtype.val (@Subsingleton.elim _ hsub ⟨x, hx⟩ 0),
             fun hx => by rw [hx]; exact G.zero_mem⟩

end DiscreteGroups

end
