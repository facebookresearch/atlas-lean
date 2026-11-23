/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.BGGReciprocity
import Atlas.LieGroups.code.HeckeKL

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def ExtOVanishes
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ} :
    ℕ →
    (X : Type uCatO) → [AddCommGroup X] → [Module R X] →
    [LieRingModule 𝔤 X] → [LieModule R 𝔤 X] →
    (IsCategoryO Δ rd X) →
    (Y : Type uCatO) → [AddCommGroup Y] → [Module R Y] →
    [LieRingModule 𝔤 Y] → [LieModule R 𝔤 Y] →
    (IsCategoryO Δ rd Y) →
    Prop
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => True
  | 1, X, _, _, _, _, _, Y, _, _, _, _, _ =>
    ∀ (E : Type uCatO) [AddCommGroup E] [Module R E]
      [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
      (_ : IsCategoryO Δ rd E)
      (ι : Y →ₗ⁅R, 𝔤⁆ E) (_ : Function.Injective ι)
      (p : E →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ e : E, p e = 0 ↔ ∃ m : Y, ι m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x
  | (n + 2), X, _, _, _, _, _, Y, _, _, _, _, hYO =>
    ∀ (K : Type uCatO) [AddCommGroup K] [Module R K]
      [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
      (hKO : IsCategoryO Δ rd K)
      (P : Type uCatO) [AddCommGroup P] [Module R P]
      [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
      (hPO : IsCategoryO Δ rd P)
      (_ : IsProjectiveInO rd P hPO)
      (ι : K →ₗ⁅R, 𝔤⁆ P) (_ : Function.Injective ι)
      (p : P →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ q, p q = 0 ↔ ∃ k, ι k = q),
      ExtOVanishes (n + 1) K hKO Y hYO






lemma UEA_induction_on
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


noncomputable def lieModuleHomToUEALinearMap
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type uCatO} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat f r m
  }






end
