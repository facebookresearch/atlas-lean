/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.TensorCategoryDef
import Atlas.TensorCategories.code.VecInstances

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Module

universe u

noncomputable section

namespace VecSemisimple

variable (k : Type u) [Field k]

/-- The ground field `k`, viewed as a one-dimensional vector space, is a simple
object in `FGModuleCat k`: every monomorphism into it from a nonzero object is an iso. -/
instance simple_of_k : Simple (FGModuleCat.of k k) where
  mono_isIso_iff_nonzero := by
    intro Y f hf
    let F := forget₂ (FGModuleCat k) (ModuleCat k)
    have hFf_mono : Mono (F.map f) := Functor.map_mono F f
    have hSimple : Simple (F.obj (FGModuleCat.of k k)) := by
      change Simple (ModuleCat.of k k); exact simple_of_isSimpleModule
    have h := @Simple.mono_isIso_iff_nonzero _ _ _ _ hSimple _ (F.map f) hFf_mono
    have ff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
    rw [show (f ≠ 0) ↔ (F.map f ≠ 0) from by
      constructor
      · intro hne he; apply hne; exact ff.map_injective (by simp [he])
      · intro hne he; apply hne; simp [he]]
    rw [← h]
    exact ⟨fun hiso => F.map_isIso f, fun hiso => ff.isIso_of_isIso_map f⟩

/-- An object `X` of `FGModuleCat k` that is not categorically zero is nontrivial
as a vector space, i.e. it contains a nonzero element. -/
lemma nontrivial_of_not_isZero (X : FGModuleCat.{u} k) (h : ¬ IsZero X) :
    Nontrivial X := by
  rw [IsZero.iff_id_eq_zero] at h
  by_contra hnt; apply h
  simp only [not_nontrivial_iff_subsingleton] at hnt
  ext x
  have : x = (0 : X) := @Subsingleton.elim _ hnt x 0
  subst this; rfl

/-- The morphism `k ⟶ X` sending `1` to a nonzero vector `v ∈ X` is itself nonzero
in `FGModuleCat k`. -/
lemma ofHom_toSpanSingleton_ne_zero (X : FGModuleCat.{u} k) (v : X) (hv : v ≠ 0) :
    FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) ≠
      (0 : FGModuleCat.of k k ⟶ X) := by
  intro h; apply hv
  have key : LinearMap.toSpanSingleton k (↑X) v = (0 : k →ₗ[k] X) := by
    have := congr_arg (fun f => f.hom.hom) h
    simpa using this
  have := congr_fun (congr_arg DFunLike.coe key) (1 : k)
  simpa [LinearMap.toSpanSingleton_apply] using this

/-- The morphism `k ⟶ X` sending `1` to a nonzero vector `v ∈ X` is a monomorphism
in `FGModuleCat k`, since `c ↦ c • v` is injective when `v ≠ 0`. -/
lemma mono_ofHom_toSpanSingleton (X : FGModuleCat.{u} k) (v : X) (hv : v ≠ 0) :
    Mono (FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) :
      FGModuleCat.of k k ⟶ X) := by
  apply (forget₂ (FGModuleCat k) (ModuleCat k)).mono_of_mono_map
  rw [ModuleCat.mono_iff_injective]
  show Function.Injective (LinearMap.toSpanSingleton k (↑X) v)
  intro a b hab
  simp [LinearMap.toSpanSingleton_apply] at hab
  have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

/-- Every simple object `X` in `FGModuleCat k` is isomorphic to the ground field `k`,
since a nonzero vector spans a one-dimensional subspace which then forces an iso. -/
def simple_iso_of_k (X : FGModuleCat.{u} k) [Simple X] :
    X ≅ FGModuleCat.of k k := by
  haveI hnt : Nontrivial X := nontrivial_of_not_isZero k X (Simple.not_isZero X)
  let v : X := (exists_ne (0 : X)).choose
  have hv : v ≠ 0 := (exists_ne (0 : X)).choose_spec
  let f : FGModuleCat.of k k ⟶ X :=
    FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v)
  have hf_mono : Mono f := mono_ofHom_toSpanSingleton k X v hv
  have hf_ne : f ≠ 0 := ofHom_toSpanSingleton_ne_zero k X v hv
  have hf_iso : IsIso f := (Simple.mono_isIso_iff_nonzero f).mpr hf_ne
  exact (asIso f).symm

/-- The additive map sending a `k`-linear map `X →ₗ[k] Y` to its packaging as
a morphism `X ⟶ Y` in `FGModuleCat k`. -/
def ofHomAddHom (X Y : FGModuleCat.{u} k) : (↑X →ₗ[k] ↑Y) →+ (X ⟶ Y) where
  toFun := FGModuleCat.ofHom
  map_zero' := rfl
  map_add' _ _ := rfl


/-- `FGModuleCat k` has finitely many isomorphism classes of simple objects, in fact
exactly one: every simple object is isomorphic to the ground field `k`. -/
instance hasFinitelyManySimples_vec :
    TensorCategories.HasFinitelyManySimples (FGModuleCat.{u} k) where
  finiteSimples := ⟨1, fun _ => FGModuleCat.of k k, ⟨fun _ => simple_of_k k,
    fun X _hX => ⟨0, ⟨simple_iso_of_k k X⟩⟩⟩⟩

end VecSemisimple

namespace VecInstances

open VecInstances

variable (k : Type u) [Field k]


end VecInstances

end
