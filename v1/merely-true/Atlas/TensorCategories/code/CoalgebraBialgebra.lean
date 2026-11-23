/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Products.Basic

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section CoalgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A]
variable [Coalgebra R A]

end CoalgebraRecap

abbrev Definition_1_20_1 (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] :=
  Coalgebra R C

structure Subcoalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    extends Submodule R A where
  comul_mem : ∀ a ∈ toSubmodule,
    Coalgebra.comul a ∈ Submodule.map₂ (TensorProduct.mk R A A) toSubmodule toSubmodule

namespace Subcoalgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

instance : SetLike (Subcoalgebra R A) A where
  coe S := S.toSubmodule
  coe_injective' S T h := by
    cases S; cases T; congr 1; exact SetLike.coe_injective h

end Subcoalgebra


class Comodule (R : Type u) (C : Type v) (M : Type*)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] C ⊗[R] M
  coassoc : TensorProduct.assoc R C C M ∘ₗ Coalgebra.comul.rTensor M ∘ₗ coact =
    coact.lTensor C ∘ₗ coact
  counit_coact : Coalgebra.counit.rTensor M ∘ₗ coact = TensorProduct.mk R R M 1

abbrev LeftComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

abbrev Definition_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

instance Coalgebra.regularComodule (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    Comodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.rTensor_counit_comp_comul

class RightComodule (R : Type u) (C : Type v) (M : Type*)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] M ⊗[R] C
  coassoc : (TensorProduct.assoc R M C C) ∘ₗ coact.rTensor C ∘ₗ coact =
    Coalgebra.comul.lTensor M ∘ₗ coact
  counit_coact : Coalgebra.counit.lTensor M ∘ₗ coact = (TensorProduct.mk R M R).flip 1

abbrev RightComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  RightComodule R C M

instance Coalgebra.regularRightComodule (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    RightComodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.lTensor_counit_comp_comul


section BialgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A]

end BialgebraRecap


section Thm_1_21_1

open MonoidalCategory

variable (k : Type u) [CommRing k]
variable (C : Type v) [Category.{w} C] [MonoidalCategory C] [Preadditive C] [Linear k C]
variable (F : C ⥤ ModuleCat.{u} k) [F.Monoidal] [F.Faithful]

set_option synthInstance.maxHeartbeats 400000

lemma unit_endo_comp_eval (f g : 𝟙_ (ModuleCat.{u} k) ⟶ 𝟙_ (ModuleCat.{u} k)) :
    (f ≫ g).hom (1 : k) = f.hom (1 : k) * g.hom (1 : k) := by
  show g.hom (f.hom 1) = f.hom 1 * g.hom 1
  have := g.hom.map_smul (f.hom 1) (1 : k)
  simp only [smul_eq_mul, mul_one] at this
  exact this

/-- The counit `End(F) → k` of the bialgebra `End(F)` of a fiber functor `F`: evaluate the
natural transformation at the unit object and read off its action on `1 ∈ k`. -/
noncomputable def endF_counit_def : End F →ₗ[k] k where
  toFun η :=
    ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
      (Functor.Monoidal.εIso F).inv).hom (1 : k)
  map_add' η₁ η₂ := by
    have : (η₁ + η₂).app (𝟙_ C) = η₁.app (𝟙_ C) + η₂.app (𝟙_ C) := rfl
    simp only [this, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' r η := by
    have h1 : (r • η).app (𝟙_ C) = r • η.app (𝟙_ C) := rfl
    simp only [h1, RingHom.id_apply]
    suffices h : (Functor.Monoidal.εIso F).hom ≫ (r • η.app (𝟙_ C)) ≫
      (Functor.Monoidal.εIso F).inv =
      r • ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
        (Functor.Monoidal.εIso F).inv) by
      simp only [h]; rfl
    rw [show (r • η.app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv =
        r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) from
        Linear.smul_comp _ _ _ _ _ _]
    rw [show (Functor.Monoidal.εIso F).hom ≫
        (r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) =
        r • ((Functor.Monoidal.εIso F).hom ≫
          (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) from
        Linear.comp_smul _ _ _ _ _ _]

/-- The bifunctor `(X, Y) ↦ F(X) ⊗ F(Y)` from `C × C` to `ModuleCat k`, used to express
the multiplicative structure on `End(F)`. -/
noncomputable def functorSelfTensor :
    (C × C) ⥤ ModuleCat.{u} k where
  obj XY := F.obj XY.1 ⊗ F.obj XY.2
  map f := F.map f.1 ⊗ₘ F.map f.2
  map_id XY := by
    change F.map (𝟙 XY.1) ⊗ₘ F.map (𝟙 XY.2) = 𝟙 _
    rw [F.map_id, F.map_id, id_tensorHom_id]
  map_comp f g := by
    change F.map (f.1 ≫ g.1) ⊗ₘ F.map (f.2 ≫ g.2) = _
    rw [F.map_comp, F.map_comp, tensorHom_comp_tensorHom]

/-- The tensor product `End(F) ⊗_k End(F)` is itself a (semi)ring via the tensor product
of algebras. -/
noncomputable instance instSemiringEndTensor :
    Semiring (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instSemiring

/-- The tensor product `End(F) ⊗_k End(F)` is a `k`-algebra. -/
noncomputable instance instAlgebraEndTensor :
    Algebra k (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instAlgebra


/-- Evaluation map sending an endomorphism `η ∈ End F` to its component at `Z`, viewed
as a `k`-linear endomorphism of `F.obj Z`. -/
def evalAtHom (Z : C) : End F →ₗ[k] (↑(F.obj Z) →ₗ[k] ↑(F.obj Z)) where
  toFun η := (η.app Z).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Wrap a `k`-linear endomorphism of the underlying module into the corresponding
endomorphism in `ModuleCat k`. -/
def wrapEnd (M : ModuleCat.{u} k) : (↑M →ₗ[k] ↑M) →ₗ[k] End M where
  toFun f := ModuleCat.ofHom f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical map `End(F) ⊗ End(F) → End(F(X) ⊗ F(Y))` sending `η₁ ⊗ η₂` to
`η₁ ⊗ η₂` evaluated component-wise. -/
noncomputable def endF_tensor_hom (X Y : C) :
    (End F) ⊗[k] (End F) →ₗ[k] End (F.obj X ⊗ F.obj Y) :=
  (wrapEnd k (F.obj X ⊗ F.obj Y)) ∘ₗ
  (TensorProduct.homTensorHomMap (.id k) ↑(F.obj X) ↑(F.obj Y) ↑(F.obj X) ↑(F.obj Y)) ∘ₗ
  (TensorProduct.map (evalAtHom k C F X) (evalAtHom k C F Y))

/-- On a simple tensor `η₁ ⊗ η₂`, `endF_tensor_hom` returns the tensor product of the
component morphisms `η₁.app X ⊗ₘ η₂.app Y`. -/
lemma endF_tensor_hom_tmul (X Y : C) (η₁ η₂ : End F) :
    endF_tensor_hom k C F X Y (η₁ ⊗ₜ[k] η₂) = η₁.app X ⊗ₘ η₂.app Y := by
  simp only [endF_tensor_hom, LinearMap.comp_apply, TensorProduct.map_tmul,
    evalAtHom, wrapEnd, LinearMap.coe_mk, AddHom.coe_mk]
  apply ModuleCat.hom_ext; rfl
















/-- The counit is unital: `ε(1) = 1`. -/
theorem endF_counit_one_proof : endF_counit_def k C F 1 = 1 := by

  show ((Functor.Monoidal.εIso F).hom ≫ (1 : End F).app (𝟙_ C) ≫
    (Functor.Monoidal.εIso F).inv).hom (1 : k) = 1

  rw [show (1 : End F).app (𝟙_ C) = 𝟙 (F.obj (𝟙_ C)) from rfl]

  rw [Category.id_comp, Iso.hom_inv_id]

  rfl

/-- The counit is multiplicative: `ε(a · b) = ε(a) · ε(b)`. -/
theorem endF_mul_compr₂_counit_proof :
    (LinearMap.mul k (End F)).compr₂ (endF_counit_def k C F) =
      (LinearMap.mul k k).compl₁₂ (endF_counit_def k C F) (endF_counit_def k C F) := by
  ext η ν
  simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', endF_counit_def,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compl₁₂_apply]


  have hmul : (η * ν).app (𝟙_ C) = ν.app (𝟙_ C) ≫ η.app (𝟙_ C) := rfl
  rw [hmul]


  have h_reassoc : (Functor.Monoidal.εIso F).hom ≫
      (ν.app (𝟙_ C) ≫ η.app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv =
    ((Functor.Monoidal.εIso F).hom ≫ ν.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) ≫
    ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) := by
    simp only [Category.assoc]; congr 1; congr 1; rw [Iso.inv_hom_id_assoc]
  rw [h_reassoc, unit_endo_comp_eval, mul_comm]



/-- Converse direction for Theorem 1.21.1: a `k`-algebra equipped with algebra maps
`Δ, ε` satisfying the coassociativity and counit axioms is a bialgebra. -/
@[reducible]
def thm_1_21_1_converse (R' : Type*) (H' : Type*) [CommSemiring R'] [Semiring H']
    [Algebra R' H']
    (Δ : H' →ₐ[R'] H' ⊗[R'] H') (ε : H' →ₐ[R'] R')
    (h_coassoc : (Algebra.TensorProduct.assoc R' R' R' H' H' H').toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (.id R' H')).comp Δ) =
      (Algebra.TensorProduct.map (.id R' H') Δ).comp Δ)
    (h_rTensor : (Algebra.TensorProduct.map ε (.id R' H')).comp Δ =
      (Algebra.TensorProduct.lid R' H').symm.toAlgHom)
    (h_lTensor : (Algebra.TensorProduct.map (.id R' H') ε).comp Δ =
      (Algebra.TensorProduct.rid R' R' H').symm.toAlgHom) :
    Bialgebra R' H' :=
  Bialgebra.ofAlgHom Δ ε h_coassoc h_rTensor h_lTensor

end Thm_1_21_1

section Def_1_21_2

/-- A bialgebra over `R` is an algebra equipped with a compatible coalgebra structure. -/
abbrev IsBialgebra (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

/-- Definition 1.21.2: An algebra `H` with comultiplication `Δ` and counit `ε` satisfying
the bialgebra axioms is called a *bialgebra*. -/
abbrev Definition_1_21_2 (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

end Def_1_21_2


section FundamentalTheorem

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Fundamental theorem ingredient: every element `c` of a coalgebra `C` lies in some
finitely generated submodule `V` such that `Δ(c) ∈ C ⊗ V`. -/
theorem Coalgebra.exists_fg_submodule_comul_mem (c : C) :
    ∃ V : Submodule R C, V.FG ∧ c ∈ V ∧
      Coalgebra.comul c ∈ Submodule.map₂ (TensorProduct.mk R C C) ⊤ V := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (Coalgebra.comul c)

  let V := Submodule.span R (Finset.image Prod.snd S : Set C)
  refine ⟨V, ?_, ?_, ?_⟩
  ·
    exact Submodule.fg_span (Finset.image Prod.snd S).finite_toSet
  ·

    have hcounit := Coalgebra.rTensor_counit_comul (R := R) c
    rw [hS] at hcounit
    simp only [map_sum, LinearMap.rTensor_tmul] at hcounit
    have hc : c = ∑ p ∈ S, Coalgebra.counit (R := R) p.1 • p.2 := by
      have := congr_arg (TensorProduct.lid R C) hcounit
      simp only [map_sum, TensorProduct.lid_tmul, one_smul] at this
      exact this.symm
    rw [hc]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hp))
  ·
    rw [hS]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.apply_mem_map₂ _ Submodule.mem_top
      (Submodule.subset_span (Finset.mem_image_of_mem _ hp))

end FundamentalTheorem
