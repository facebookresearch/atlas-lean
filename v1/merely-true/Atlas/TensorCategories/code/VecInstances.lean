/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.TensorCategoryDef

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u

noncomputable section

namespace VecInstances

/-- `Vec k` is the category of finite-dimensional `k`-vector spaces, modeled in
mathlib by `FGModuleCat k`. -/
abbrev Vec (k : Type u) [Ring k] := FGModuleCat.{u} k

/-- `Vec k` has all finite biproducts, obtained from existence of finite products. -/
instance hasFiniteBiproducts_vec (k : Type u) [Field k] :
    HasFiniteBiproducts (Vec k) :=
  HasFiniteBiproducts.of_hasFiniteProducts

section AutomaticInstances

variable (k : Type u) [Field k]


end AutomaticInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- The order embedding from subobjects of `X` in `Vec k` to submodules of the
underlying `k`-module, built by composing the forgetful functor with mathlib's
`subobjectModule` equivalence. -/
def subobjectOrderEmbedding (X : Vec k) :
    Subobject X ↪o Submodule k X :=
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  let ff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F

  let e₁ : Subobject X ↪o Subobject (F.obj X) :=
    OrderEmbedding.ofMapLEIff
      (fun s => Subobject.mk (F.map s.arrow))
      (fun s₁ s₂ => by
        constructor
        ·

          intro h
          let g := Subobject.ofMkLEMk (F.map s₁.arrow) (F.map s₂.arrow) h
          let g' := ff.preimage g
          apply Subobject.le_of_comm g'
          apply F.map_injective
          rw [F.map_comp, ff.map_preimage]
          exact Subobject.ofMkLEMk_comp h
        ·

          intro h
          let g := Subobject.ofLE _ _ h
          refine Subobject.mk_le_mk_of_comm (F.map g) ?_
          rw [← F.map_comp, Subobject.ofLE_arrow])

  e₁.trans (ModuleCat.subobjectModule (F.obj X)).toOrderEmbedding

/-- Every object of `Vec k` has finite length: its subobject lattice is both
well-founded and inverse well-founded. -/
theorem hasFiniteLength_vec (X : Vec k) :
    TensorCategories.HasFiniteLength X :=
  let emb := subobjectOrderEmbedding k X
  ⟨emb.wellFoundedLT, emb.wellFoundedGT⟩

/-- `Vec k` is locally finite (Definition 1.12.1): finite-dimensional hom-spaces and
finite-length objects. -/
instance locallyFiniteCategory_vec :
    TensorCategories.LocallyFiniteCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k

/-- `Vec k` is a multitensor category in the sense of Definition 1.12.3. -/
instance multitensorCategory_vec :
    TensorCategories.MultitensorCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k

/-- Two `k`-linear endomorphisms of `k` are equal iff they agree on the multiplicative
identity. -/
lemma linearMap_eq_of_apply_one (f g : k →ₗ[k] k) (h : f 1 = g 1) : f = g := by
  ext; exact h

/-- The `k`-algebra homomorphism `End(𝟙_ Vec) →ₐ[k] k` sending an endomorphism `f`
to `f(1)`, witnessing the identification of `End(𝟙_ Vec)` with `k`. -/
noncomputable def endUnitAlgHom : End (𝟙_ (FGModuleCat k)) →ₐ[k] k where
  toFun f := f.hom.hom 1
  map_one' := by simp
  map_mul' := by
    intro f g

    change f.hom.hom (g.hom.hom 1) = f.hom.hom 1 * g.hom.hom 1

    set a := g.hom.hom 1
    calc f.hom.hom a = f.hom.hom (a • (1 : k)) := by rw [smul_eq_mul, mul_one]
      _ = a • f.hom.hom 1 := by rw [map_smul]
      _ = a * f.hom.hom 1 := by rw [smul_eq_mul]
      _ = f.hom.hom 1 * a := by ring
  map_zero' := by change (0 : k →ₗ[k] k) 1 = 0; simp
  map_add' := by
    intro f g; change (f.hom.hom + g.hom.hom) 1 = f.hom.hom 1 + g.hom.hom 1; simp
  commutes' := by
    intro c
    show (c • (𝟙 (𝟙_ (FGModuleCat k)))).hom.hom 1 = c
    change c • (𝟙 (𝟙_ (FGModuleCat k)) :
      𝟙_ (FGModuleCat k) ⟶ 𝟙_ (FGModuleCat k)).hom.hom 1 = c
    simp

/-- The `k`-algebra isomorphism `End(𝟙_ Vec) ≃ₐ[k] k`, upgrading `endUnitAlgHom`
into a bijection. This realizes `End(𝟙) ≅ k` for `Vec_k`. -/
noncomputable def endUnitAlgEquiv : End (𝟙_ (FGModuleCat k)) ≃ₐ[k] k :=
  AlgEquiv.ofBijective (endUnitAlgHom k) ⟨by
    intro f g hfg
    simp only [endUnitAlgHom, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk] at hfg
    exact InducedCategory.Hom.ext
      (ModuleCat.Hom.ext (linearMap_eq_of_apply_one k _ _ hfg))
  , by
    intro c
    exact ⟨algebraMap k _ c, by
      simp only [endUnitAlgHom, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk]
      show (c • (𝟙 (𝟙_ (FGModuleCat k)))).hom.hom 1 = c
      change c • (𝟙 (𝟙_ (FGModuleCat k)) :
        𝟙_ (FGModuleCat k) ⟶ 𝟙_ (FGModuleCat k)).hom.hom 1 = c
      simp⟩
  ⟩

/-- `Vec k` is a tensor category in the sense of Definition 1.12.3: a multitensor
category whose unit-endomorphism algebra is `k`. -/
instance tensorCategory_vec :
    TensorCategories.TensorCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k
  endUnit_iso_k := ⟨endUnitAlgEquiv k⟩

/-- Convenient alias for Definition 1.12.3: the canonical isomorphism
`End(𝟙_ Vec_k) ≅ k`. -/
abbrev def_1_12_3_endUnit_iso (k : Type u) [Field k] :=
  endUnitAlgEquiv k

end FiniteLength

end VecInstances

end
