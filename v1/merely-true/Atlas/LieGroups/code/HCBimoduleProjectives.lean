/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Mathlib.Algebra.Lie.Semisimple.Defs

noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]
variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

abbrev CenterCharacter (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] :=
  ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R

structure IsInHCThetaOne (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  right_annihilated : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = θ z • m

structure HCThetaOneHom (M₁ M₂ : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hM₁ : IsInHCThetaOne M₁ θ) (hM₂ : IsInHCThetaOne M₂ θ) where
  toLinearMap : M₁.carrier →ₗ[R] M₂.carrier
  left_compat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
    toLinearMap (M₁.leftAction u m) = M₂.leftAction u (toLinearMap m)
  right_compat : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
    toLinearMap (M₁.rightAction u m) = M₂.rightAction u (toLinearMap m)

def IsProjectiveInHCThetaOne (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hP : IsInHCThetaOne P θ) : Prop :=
  ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂) (f : HCThetaOneHom P Y₂ θ hP hY₂),
    Function.Surjective g.toLinearMap →
    ∃ (lift : HCThetaOneHom P Y₁ θ hP hY₁),
      ∀ m : P.carrier, g.toLinearMap (lift.toLinearMap m) = f.toLinearMap m

def IsTensorProductBimoduleWithUTheta
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (θ : CenterCharacter R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V] : Prop :=
  ∃ (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤),

    (∃ (f : P.carrier →ₗ[R] T.carrier),
      Function.Bijective f ∧
      (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : P.carrier),
        f (P.leftAction u m) = T.leftAction u (f m)) ∧
      (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : P.carrier),
        f (P.rightAction u m) = T.rightAction u (f m))) ∧

    (∃ (ι : V →ₗ[R] T.carrier),
      ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
        (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
        t = ∑ i, T.rightAction (us i) (ι (vs i))) ∧

    (∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (t : T.carrier),
      T.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) t = θ z • t)


theorem tensor_hom_bimodule_uniqueness
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    (ι : V →ₗ[R] T.carrier)
    (h_gen : ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
      (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
      t = ∑ i, T.rightAction (us i) (ι (vs i)))
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (f₁ f₂ : T.carrier →ₗ[R] Y.carrier)
    (h_f₁_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
      f₁ (T.rightAction u t) = Y.rightAction u (f₁ t))
    (h_f₂_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
      f₂ (T.rightAction u t) = Y.rightAction u (f₂ t))
    (h_agree_on_V : ∀ v : V, f₁ (ι v) = f₂ (ι v)) :
    ∀ t : T.carrier, f₁ t = f₂ t := by
  intro t
  obtain ⟨n, vs, us, ht⟩ := h_gen t
  rw [ht]
  simp only [map_sum]
  congr 1
  ext i
  rw [h_f₁_right, h_f₂_right, h_agree_on_V]







theorem tensor_product_bimodule_surjects_from_generators
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    (ι : V →ₗ[R] Y.carrier)
    (h_gen : ∀ y : Y.carrier, ∃ (n : ℕ) (vs : Fin n → V)
      (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
      y = ∑ i, Y.rightAction (us i) (ι (vs i))) :
    ∃ (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (hP : IsInHCThetaOne P θ),
      IsTensorProductBimoduleWithUTheta P θ V ∧
      ∃ (π : HCThetaOneHom P Y θ hP hY), Function.Surjective π.toLinearMap := by


  refine ⟨Y, hY, ?_, ?_⟩
  ·

    refine ⟨Y, ?_, ?_, ?_⟩
    ·
      exact ⟨LinearMap.id, Function.bijective_id, fun _ _ => rfl, fun _ _ => rfl⟩
    ·
      exact ⟨ι, h_gen⟩
    ·
      exact hY.right_annihilated
  ·
    refine ⟨⟨LinearMap.id, fun _ _ => rfl, fun _ _ => rfl⟩, Function.surjective_id⟩



def LieBimodule.IsFiniteLengthBimodule (M : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) : Prop :=
  ∃ n : ℕ, ∃ (chain : Fin (n + 1) → Submodule R M.carrier),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧

    (∀ i : Fin n,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
        chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧

    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) ∧
    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧


    (∀ i : Fin n, ∀ (W : Submodule R M.carrier), M.IsSubBimodule W →
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ W →
      W ≤ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ →
      W = chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ∨
      W = chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def iteratedKerThetaRightAction (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : M.carrier) : M.carrier :=
  zs.foldl (fun acc z =>
    let θz : R := θ z
    let zVal : UniversalEnvelopingAlgebra R 𝔤 := z
    let kerElem : UniversalEnvelopingAlgebra R 𝔤 := zVal - algebraMap R _ θz
    M.rightAction (MulOpposite.op kerElem) acc) m

structure IsInHCTheta (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  annihilated_by_power : ∃ n : ℕ,
    ∀ (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      zs.length = n →
      ∀ (m : M.carrier), iteratedKerThetaRightAction M θ zs m = 0

def IsInHC (M : LieBimodule R 𝔤) : Prop :=
  IsHarishChandraBimodule M

def LieBimodule.AreIsomorphic (M₁ M₂ : LieBimodule R 𝔤) : Prop :=
  ∃ (f : M₁.carrier →ₗ[R] M₂.carrier),
    Function.Bijective f ∧
    (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
      f (M₁.leftAction u m) = M₂.leftAction u (f m)) ∧
    (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
      f (M₁.rightAction u m) = M₂.rightAction u (f m))

section Corollary_25_7

universe u_𝔤'' u_mod''

variable {𝔤'' : Type u_𝔤''} [LieRing 𝔤''] [LieAlgebra ℂ 𝔤'']
  [LieAlgebra.IsSemisimple ℂ 𝔤''] [Module.Finite ℂ 𝔤'']

def HasFinitelyManySimpleBimodules
    {𝔤 : Type u_𝔤''} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (θ : CenterCharacter ℂ 𝔤) : Prop :=
  ∃ (n : ℕ) (simples : Fin n → LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤),
    (∀ i, (simples i).IsIrreducible) ∧
    (∀ i, IsInHCThetaOne (simples i) θ) ∧
    (∀ (S : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤), S.IsIrreducible → IsInHCThetaOne S θ →
      ∃ i, LieBimodule.AreIsomorphic S (simples i))








end Corollary_25_7

end
