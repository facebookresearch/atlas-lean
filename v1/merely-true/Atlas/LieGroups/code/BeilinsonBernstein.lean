/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic

open CategoryTheory

namespace BeilinsonBernstein

noncomputable section

universe u

structure SmoothAlgVariety where
  carrier : Type u

structure CAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

structure AbCat where
  Obj : Type u
  instCat : Category Obj

attribute [instance] AbCat.instCat

structure GradedAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

def filtPred {α : Type*} [AddCommMonoid α] [Module ℂ α]
    (F : ℕ → Submodule ℂ α) : ℕ → Submodule ℂ α
  | 0 => ⊥
  | n + 1 => F n

class IsDaffine (X : SmoothAlgVariety.{u}) (DMod : AbCat.{u}) (DXMod : AbCat.{u})
    (Gamma : DMod.Obj ⥤ DXMod.Obj) (Loc : DXMod.Obj ⥤ DMod.Obj) : Prop where
  equiv : ∃ e : DMod.Obj ≌ DXMod.Obj, e.functor = Gamma ∧ e.inverse = Loc

noncomputable def AlgHom.liftOfSurjectiveNC {R A B C : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (π : A →ₐ[R] B) (hπ : Function.Surjective π) (f : A →ₐ[R] C)
    (hker : ∀ x, π x = 0 → f x = 0) : B →ₐ[R] C where
  toFun b := f (Function.surjInv hπ b)
  map_one' := by
    have hk : π (Function.surjInv hπ 1 - 1) = 0 := by simp [Function.surjInv_eq]
    have := hker _ hk; rwa [map_sub, map_one, sub_eq_zero] at this
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a * π b) - a * b) = 0 by
      rw [← map_mul]; simp [Function.surjInv_eq])
    rw [map_sub, map_mul, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  map_zero' := hker _ (by simp [Function.surjInv_eq])
  map_add' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a + π b) - (a + b)) = 0 by
      rw [← map_add]; simp [Function.surjInv_eq])
    rw [map_sub, map_add, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  commutes' r := by
    have := hker _ (show π (Function.surjInv hπ (algebraMap R B r) - algebraMap R A r) = 0 by
      simp [Function.surjInv_eq, AlgHom.commutes])
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

theorem AlgHom.liftOfSurjectiveNC_apply {R A B C : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (π : A →ₐ[R] B) (hπ : Function.Surjective π) (f : A →ₐ[R] C)
    (hker : ∀ x, π x = 0 → f x = 0) (x : A) :
    AlgHom.liftOfSurjectiveNC π hπ f hker (π x) = f x := by
  show f (Function.surjInv hπ (π x)) = f x
  have := hker _ (show π (Function.surjInv hπ (π x) - x) = 0 by
    simp [Function.surjInv_eq])
  rwa [map_sub, sub_eq_zero] at this

structure BBDataZero where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  FlagVar : SmoothAlgVariety.{u}
  DF : CAlgebra.{u}
  U₀ : CAlgebra.{u}
  proj₀ : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ] U₀.carrier
  actionMap : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ] DF.carrier
  proj₀_surjective : Function.Surjective proj₀
  ker_inclusion : ∀ (x : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    proj₀ x = 0 → actionMap x = 0


  NilpCone : Type u
  CotangentBundle : Type u
  grU₀ : GradedAlgebra.{u}
  grDF : GradedAlgebra.{u}
  O_TstarF : GradedAlgebra.{u}
  gr_a₀ : grU₀.carrier →ₐ[ℂ] grDF.carrier
  p_star : grU₀.carrier →ₐ[ℂ] O_TstarF.carrier
  incl_TstarF : O_TstarF.carrier →ₐ[ℂ] grDF.carrier
  p_star_bijective : Function.Bijective p_star
  symbol_proj : grDF.carrier →ₐ[ℂ] O_TstarF.carrier
  symbol_proj_left_inv : Function.LeftInverse symbol_proj incl_TstarF
  generators_grU₀ : Set grU₀.carrier
  grU₀_generated : Algebra.adjoin ℂ generators_grU₀ = ⊤
  generators_grU₀_deg1 : Set grU₀.carrier
  generators_grU₀_decomp : generators_grU₀ ⊆
    Set.range (algebraMap ℂ grU₀.carrier) ∪ generators_grU₀_deg1
  symbolOfAction : grU₀.carrier → grDF.carrier
  gr_a₀_eq_symbolOfAction_field : ∀ x ∈ generators_grU₀_deg1, gr_a₀ x = symbolOfAction x
  incl_p_star_eq_symbolOfAction_field : ∀ x ∈ generators_grU₀_deg1,
    (incl_TstarF.comp p_star) x = symbolOfAction x

  DModF : AbCat.{u}
  U₀Mod : AbCat.{u}
  Gamma : DModF.Obj ⥤ U₀Mod.Obj
  Loc : U₀Mod.Obj ⥤ DModF.Obj

  filtration_U₀ : ℕ → Submodule ℂ U₀.carrier
  filtration_DF : ℕ → Submodule ℂ DF.carrier
  filtration_U₀_exhaustive : ∀ x, ∃ n, x ∈ filtration_U₀ n
  filtration_U₀_mono : ∀ ⦃m n⦄, m ≤ n → filtration_U₀ m ≤ filtration_U₀ n

  filtration_DF_exhaustive : ∀ y, ∃ n, y ∈ filtration_DF n

  quotient_U₀ : (n : ℕ) → { x : U₀.carrier // x ∈ filtration_U₀ n } → grU₀.carrier
  quotient_DF : (n : ℕ) → { y : DF.carrier // y ∈ filtration_DF n } → grDF.carrier
  quotient_U₀_ker : ∀ n (x : U₀.carrier) (hx : x ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x, hx⟩ = 0 ↔ x ∈ filtPred filtration_U₀ n
  quotient_DF_ker : ∀ n (y : DF.carrier) (hy : y ∈ filtration_DF n),
    quotient_DF n ⟨y, hy⟩ = 0 ↔ y ∈ filtPred filtration_DF n

  quotient_DF_sub : ∀ n (y₁ y₂ : DF.carrier) (hy₁ : y₁ ∈ filtration_DF n)
    (hy₂ : y₂ ∈ filtration_DF n) (hy_sub : y₁ - y₂ ∈ filtration_DF n),
    quotient_DF n ⟨y₁ - y₂, hy_sub⟩ = quotient_DF n ⟨y₁, hy₁⟩ - quotient_DF n ⟨y₂, hy₂⟩
  filtration_DF_mono : ∀ ⦃m n⦄, m ≤ n → filtration_DF m ≤ filtration_DF n
  quotient_U₀_add : ∀ n (x₁ x₂ : U₀.carrier) (hx₁ : x₁ ∈ filtration_U₀ n)
    (hx₂ : x₂ ∈ filtration_U₀ n) (hx_add : x₁ + x₂ ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x₁ + x₂, hx_add⟩ = quotient_U₀ n ⟨x₁, hx₁⟩ + quotient_U₀ n ⟨x₂, hx₂⟩
  quotient_U₀_sub : ∀ n (x₁ x₂ : U₀.carrier) (hx₁ : x₁ ∈ filtration_U₀ n)
    (hx₂ : x₂ ∈ filtration_U₀ n) (hx_sub : x₁ - x₂ ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x₁ - x₂, hx_sub⟩ = quotient_U₀ n ⟨x₁, hx₁⟩ - quotient_U₀ n ⟨x₂, hx₂⟩
  quotient_DF_add : ∀ n (y₁ y₂ : DF.carrier) (hy₁ : y₁ ∈ filtration_DF n)
    (hy₂ : y₂ ∈ filtration_DF n) (hy_add : y₁ + y₂ ∈ filtration_DF n),
    quotient_DF n ⟨y₁ + y₂, hy_add⟩ = quotient_DF n ⟨y₁, hy₁⟩ + quotient_DF n ⟨y₂, hy₂⟩
  quotient_DF_surj : ∀ z : grDF.carrier,
    ∃ n, ∃ y : DF.carrier, ∃ hy : y ∈ filtration_DF n, quotient_DF n ⟨y, hy⟩ = z
  quotient_U₀_surj : ∀ z : grU₀.carrier,
    ∃ n, ∃ x : U₀.carrier, ∃ hx : x ∈ filtration_U₀ n, quotient_U₀ n ⟨x, hx⟩ = z
  filtration_UEA : ℕ → Submodule ℂ
    (@UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
  actionMap_filtration_preserving :
    ∀ n (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    u ∈ filtration_UEA n → actionMap u ∈ filtration_DF n
  proj₀_filtration_surj : ∀ n (x : U₀.carrier),
    x ∈ filtration_U₀ n →
    ∃ u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra,
      u ∈ filtration_UEA n ∧ proj₀ u = x
  gr_a₀_compat_UEA :
    ∀ n (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
      (hu : u ∈ filtration_UEA n)
      (hpu : proj₀ u ∈ filtration_U₀ n),
      gr_a₀ (quotient_U₀ n ⟨proj₀ u, hpu⟩) =
        quotient_DF n ⟨actionMap u, actionMap_filtration_preserving n u hu⟩

  symbol_proj_right_inv : Function.RightInverse symbol_proj incl_TstarF
  gr_a₀_approx_surj : ∀ (n : ℕ) (y : DF.carrier) (hy : y ∈ filtration_DF n),
    ∃ (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
      (hu : u ∈ filtration_UEA n) (_ : proj₀ u ∈ filtration_U₀ n),
      quotient_DF n ⟨actionMap u, actionMap_filtration_preserving n u hu⟩ =
        quotient_DF n ⟨y, hy⟩

attribute [instance] BBDataZero.instLieRing BBDataZero.instLieAlgebra BBDataZero.instSemisimple

noncomputable def BBDataZero.a₀ (D : BBDataZero) : D.U₀.carrier →ₐ[ℂ] D.DF.carrier :=
  AlgHom.liftOfSurjectiveNC D.proj₀ D.proj₀_surjective D.actionMap D.ker_inclusion

theorem BBDataZero.a₀_factors (D : BBDataZero) :
    ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
      D.a₀ (D.proj₀ x) = D.actionMap x :=
  fun x => AlgHom.liftOfSurjectiveNC_apply D.proj₀ D.proj₀_surjective D.actionMap D.ker_inclusion x

theorem BBDataZero.a₀_filtration_preserving (D : BBDataZero) :
    ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n → D.a₀ x ∈ D.filtration_DF n := by
  intro n x hx
  obtain ⟨u, hu_fil, hu_proj⟩ := D.proj₀_filtration_surj n x hx
  have h_factor : D.a₀ x = D.actionMap u := by
    rw [← hu_proj, D.a₀_factors]
  rw [h_factor]
  exact D.actionMap_filtration_preserving n u hu_fil

theorem BBDataZero.gr_a₀_compat (D : BBDataZero) :
    ∀ n (x : D.U₀.carrier) (hx : x ∈ D.filtration_U₀ n),
      D.gr_a₀ (D.quotient_U₀ n ⟨x, hx⟩) =
        D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ := by
  intro n x hx

  obtain ⟨u, hu_fil, hu_proj⟩ := D.proj₀_filtration_surj n x hx

  have hcompat := D.gr_a₀_compat_UEA n u hu_fil (hu_proj ▸ hx)

  have hq_eq : (⟨D.proj₀ u, hu_proj ▸ hx⟩ : { y : D.U₀.carrier // y ∈ D.filtration_U₀ n }) =
      ⟨x, hx⟩ := by
    simp only [Subtype.mk.injEq]; exact hu_proj
  rw [hq_eq] at hcompat

  have h_a₀_eq : D.a₀ x = D.actionMap u := by
    rw [← hu_proj, D.a₀_factors]
  rw [hcompat]
  congr 1
  exact Subtype.ext h_a₀_eq.symm
theorem BBDataZero.a₀_surj_of_structure (D : BBDataZero) :
    Function.Surjective D.a₀ := by
  suffices h : ∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
      ∃ x : D.U₀.carrier, x ∈ D.filtration_U₀ n ∧ D.a₀ x = y by
    intro y; obtain ⟨n, hn⟩ := D.filtration_DF_exhaustive y
    exact ⟨_, (h n y hn).choose_spec.2⟩
  intro n; induction n with
  | zero =>
    intro y hy
    obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj 0 y hy
    refine ⟨D.proj₀ u, hpu, ?_⟩
    have ha₀ : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u
    have hmem : D.actionMap u ∈ D.filtration_DF 0 := D.actionMap_filtration_preserving 0 u hu
    have hmem' : D.a₀ (D.proj₀ u) ∈ D.filtration_DF 0 := ha₀ ▸ hmem
    have hsub : y - D.a₀ (D.proj₀ u) ∈ D.filtration_DF 0 := (D.filtration_DF 0).sub_mem hy hmem'
    have hqs := D.quotient_DF_sub 0 y (D.a₀ (D.proj₀ u)) hy hmem' hsub
    have hq' : D.quotient_DF 0 ⟨D.a₀ (D.proj₀ u), hmem'⟩ = D.quotient_DF 0 ⟨y, hy⟩ := by
      have : D.quotient_DF 0 ⟨D.a₀ (D.proj₀ u), hmem'⟩ =
             D.quotient_DF 0 ⟨D.actionMap u, hmem⟩ := by
        congr 1; exact Subtype.ext ha₀
      rw [this]; exact hq
    have hzero : D.quotient_DF 0 ⟨y - D.a₀ (D.proj₀ u), hsub⟩ = 0 := by rw [hqs, hq', sub_self]
    have hbot := (D.quotient_DF_ker 0 _ hsub).mp hzero
    simp only [filtPred, Submodule.mem_bot] at hbot
    exact (sub_eq_zero.mp hbot).symm
  | succ n ih =>
    intro y hy
    obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj (n+1) y hy
    have ha₀ : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u
    have hmem : D.actionMap u ∈ D.filtration_DF (n+1) := D.actionMap_filtration_preserving (n+1) u hu
    have hmem' : D.a₀ (D.proj₀ u) ∈ D.filtration_DF (n+1) := ha₀ ▸ hmem
    have hsub : y - D.a₀ (D.proj₀ u) ∈ D.filtration_DF (n+1) := (D.filtration_DF (n+1)).sub_mem hy hmem'
    have hqs := D.quotient_DF_sub (n+1) y (D.a₀ (D.proj₀ u)) hy hmem' hsub
    have hq' : D.quotient_DF (n+1) ⟨D.a₀ (D.proj₀ u), hmem'⟩ = D.quotient_DF (n+1) ⟨y, hy⟩ := by
      have : D.quotient_DF (n+1) ⟨D.a₀ (D.proj₀ u), hmem'⟩ =
             D.quotient_DF (n+1) ⟨D.actionMap u, hmem⟩ := by
        congr 1; exact Subtype.ext ha₀
      rw [this]; exact hq
    have hzero : D.quotient_DF (n+1) ⟨y - D.a₀ (D.proj₀ u), hsub⟩ = 0 := by rw [hqs, hq', sub_self]
    have hresid := (D.quotient_DF_ker (n+1) _ hsub).mp hzero
    simp only [filtPred] at hresid
    obtain ⟨x', hx', hx'eq⟩ := ih _ hresid
    refine ⟨D.proj₀ u + x', Submodule.add_mem _ hpu (D.filtration_U₀_mono (Nat.le_succ n) hx'), ?_⟩
    rw [map_add, hx'eq, ha₀, add_sub_cancel]

theorem BBDataZero.actionMap_surjective (D : BBDataZero) :
    Function.Surjective D.actionMap := by
  intro y
  obtain ⟨u, hu⟩ := D.a₀_surj_of_structure y
  obtain ⟨x, hx⟩ := D.proj₀_surjective u
  exact ⟨x, by rw [← D.a₀_factors, hx, hu]⟩

theorem BBDataZero.gr_a₀_eq_symbolOfAction (D : BBDataZero) :
    ∀ x ∈ D.generators_grU₀_deg1, D.gr_a₀ x = D.symbolOfAction x :=
  D.gr_a₀_eq_symbolOfAction_field

theorem BBDataZero.incl_p_star_eq_symbolOfAction (D : BBDataZero) :
    ∀ x ∈ D.generators_grU₀_deg1,
      (D.incl_TstarF.comp D.p_star) x = D.symbolOfAction x :=
  D.incl_p_star_eq_symbolOfAction_field

theorem BBDataZero.gr_a₀_step_down (D : BBDataZero) :
    Function.Injective D.gr_a₀ →
      ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n →
        D.a₀ x ∈ filtPred D.filtration_DF n → x ∈ filtPred D.filtration_U₀ n := by
  intro h_inj n x hx ha₀x

  have ha₀x_n : D.a₀ x ∈ D.filtration_DF n := D.a₀_filtration_preserving n x hx

  have hq_DF : D.quotient_DF n ⟨D.a₀ x, ha₀x_n⟩ = 0 :=
    (D.quotient_DF_ker n (D.a₀ x) ha₀x_n).mpr ha₀x

  have hcompat := D.gr_a₀_compat n x hx

  have hgr_zero : D.gr_a₀ (D.quotient_U₀ n ⟨x, hx⟩) = 0 := by
    rw [hcompat, hq_DF]

  have hq_zero : D.quotient_U₀ n ⟨x, hx⟩ = 0 := by
    have h0 : D.gr_a₀ 0 = 0 := map_zero D.gr_a₀
    rw [← h0] at hgr_zero
    exact h_inj hgr_zero

  exact (D.quotient_U₀_ker n x hx).mp hq_zero

theorem BBDataZero.quotient_surj_from_a₀ (D : BBDataZero) :
    Function.Surjective D.a₀ →
    ∀ (n : ℕ) (y : D.DF.carrier) (hy : y ∈ D.filtration_DF n),
      ∃ x : D.U₀.carrier, ∃ hx : x ∈ D.filtration_U₀ n,
        D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ = D.quotient_DF n ⟨y, hy⟩ := by
  intro _h_surj n y hy

  obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj n y hy

  refine ⟨D.proj₀ u, hpu, ?_⟩

  have ha₀_eq : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u

  have : D.quotient_DF n ⟨D.a₀ (D.proj₀ u), D.a₀_filtration_preserving n (D.proj₀ u) hpu⟩ =
      D.quotient_DF n ⟨D.actionMap u, D.actionMap_filtration_preserving n u hu⟩ := by
    congr 1; exact Subtype.ext ha₀_eq
  rw [this]
  exact hq

theorem BBDataZero.gr_a₀_step_up (D : BBDataZero) :
    Function.Surjective D.a₀ →
      ∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
        ∃ x, x ∈ D.filtration_U₀ n ∧ y - D.a₀ x ∈ filtPred D.filtration_DF n := by
  intro h_surj n y hy

  obtain ⟨x, hx, hq_eq⟩ := D.quotient_surj_from_a₀ h_surj n y hy
  refine ⟨x, hx, ?_⟩

  have ha₀x_n : D.a₀ x ∈ D.filtration_DF n := D.a₀_filtration_preserving n x hx

  have hy_sub_n : y - D.a₀ x ∈ D.filtration_DF n :=
    (D.filtration_DF n).sub_mem hy ha₀x_n

  have hsub := D.quotient_DF_sub n y (D.a₀ x) hy ha₀x_n hy_sub_n


  have hq_zero : D.quotient_DF n ⟨y - D.a₀ x, hy_sub_n⟩ = 0 := by
    rw [hsub, hq_eq, sub_self]

  exact (D.quotient_DF_ker n (y - D.a₀ x) hy_sub_n).mp hq_zero

theorem BBDataZero.gr_a₀_surj_of_levelwise_surj (D : BBDataZero) :
    (∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
      ∃ x, x ∈ D.filtration_U₀ n ∧ D.a₀ x = y) →
    Function.Surjective D.gr_a₀ := by
  intro h z

  obtain ⟨n, y, hy, hyz⟩ := D.quotient_DF_surj z

  obtain ⟨x, hx, hax⟩ := h n y hy

  refine ⟨D.quotient_U₀ n ⟨x, hx⟩, ?_⟩

  rw [D.gr_a₀_compat n x hx]

  subst hax
  exact hyz

theorem incl_TstarF_inj (D : BBDataZero) : Function.Injective D.incl_TstarF :=
  D.symbol_proj_left_inv.injective

theorem a₀_factorization (D : BBDataZero) :
    ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
      D.a₀ (D.proj₀ x) = D.actionMap x :=
  D.a₀_factors

theorem a₀_surj (D : BBDataZero) : Function.Surjective D.a₀ := by
  intro y
  obtain ⟨x, hx⟩ := D.actionMap_surjective y
  exact ⟨D.proj₀ x, by rw [D.a₀_factors]; exact hx⟩

theorem gr_a₀_eq_on_deg1 (D : BBDataZero) :
    ∀ x ∈ D.generators_grU₀_deg1,
      D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
  intro x hx


  have h1 : D.gr_a₀ x = D.symbolOfAction x := D.gr_a₀_eq_symbolOfAction x hx
  have h2 : (D.incl_TstarF.comp D.p_star) x = D.symbolOfAction x :=
    D.incl_p_star_eq_symbolOfAction x hx
  exact h1.trans h2.symm

theorem a₀_comp_proj₀ (D : BBDataZero)
    (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra) :
    D.a₀ (D.proj₀ x) = D.actionMap x :=
  a₀_factorization D x

theorem gr_a₀_eq_on_generators (D : BBDataZero) :
    ∀ x ∈ D.generators_grU₀, D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by


  intro x hx
  rcases D.generators_grU₀_decomp hx with h_deg0 | h_deg1
  ·

    obtain ⟨r, rfl⟩ := h_deg0
    simp [AlgHom.commutes]
  ·
    exact gr_a₀_eq_on_deg1 D x h_deg1

theorem incl_TstarF_injective (D : BBDataZero) :
    Function.Injective D.incl_TstarF :=
  incl_TstarF_inj D

theorem filtered_surj (D : BBDataZero) :
    Function.Surjective D.a₀ → Function.Surjective D.gr_a₀ := by
  intro h_surj


  apply D.gr_a₀_surj_of_levelwise_surj

  have step_up := D.gr_a₀_step_up h_surj
  intro n
  induction n with
  | zero =>
    intro y hy

    obtain ⟨x, hx_mem, hresid⟩ := step_up 0 y hy
    simp only [filtPred, Submodule.mem_bot] at hresid

    exact ⟨x, hx_mem, (sub_eq_zero.mp hresid).symm⟩
  | succ n ih =>
    intro y hy

    obtain ⟨x, hx_mem, hresid⟩ := step_up (n + 1) y hy
    simp only [filtPred] at hresid

    obtain ⟨x', hx'_mem, hx'_eq⟩ := ih (y - D.a₀ x) hresid

    refine ⟨x + x', ?_, ?_⟩
    · exact Submodule.add_mem _ hx_mem
        (D.filtration_U₀_mono (Nat.le_succ n) hx'_mem)
    · rw [map_add, hx'_eq, add_sub_cancel]

theorem gr_a₀_surjective (D : BBDataZero) :
    Function.Surjective D.gr_a₀ :=
  filtered_surj D (a₀_surj D)

theorem thm_29_1_factorization (D : BBDataZero) :
    D.actionMap = D.a₀.comp D.proj₀ := by


  ext x


  show D.actionMap (UniversalEnvelopingAlgebra.ι ℂ x) =
    D.a₀ (D.proj₀ (UniversalEnvelopingAlgebra.ι ℂ x))
  exact (a₀_comp_proj₀ D (UniversalEnvelopingAlgebra.ι ℂ x)).symm

theorem thm_29_1_gr_eq_pullback (D : BBDataZero) :
    D.gr_a₀ = D.incl_TstarF.comp D.p_star := by


  ext x
  have hx : x ∈ Algebra.adjoin ℂ D.generators_grU₀ := by
    rw [D.grU₀_generated]; exact Algebra.mem_top
  exact Algebra.adjoin_induction
    (p := fun x _ => D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x)
    (fun y hy => gr_a₀_eq_on_generators D y hy)
    (fun r => by simp [AlgHom.commutes])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => by simp [map_mul, ha, hb])
    hx

theorem thm_29_1_grDF_eq_O_TstarF (D : BBDataZero) :
    Function.Bijective D.incl_TstarF := by


  constructor
  ·
    exact incl_TstarF_injective D
  ·


    have h_gr_surj : Function.Surjective D.gr_a₀ := gr_a₀_surjective D

    have h_eq := thm_29_1_gr_eq_pullback D

    intro y
    obtain ⟨x, hx⟩ := h_gr_surj y
    have : D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
      rw [h_eq]
    rw [this] at hx

    exact ⟨D.p_star x, hx⟩

theorem filtered_bij (D : BBDataZero) :
    Function.Bijective D.gr_a₀ → Function.Bijective D.a₀ := by
  intro hgr_bij
  refine ⟨?_, a₀_surj D⟩

  have step_down := D.gr_a₀_step_down hgr_bij.1
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  set z := x - y
  have hz : D.a₀ z = 0 := by simp [z, map_sub, hxy]
  obtain ⟨n, hn⟩ := D.filtration_U₀_exhaustive z
  induction n with
  | zero =>
    have h1 : D.a₀ z ∈ filtPred D.filtration_DF 0 := by
      simp only [filtPred, Submodule.mem_bot]; exact hz
    have h2 := step_down 0 z hn h1
    simp only [filtPred, Submodule.mem_bot] at h2
    exact h2
  | succ n ih =>
    have h1 : D.a₀ z ∈ filtPred D.filtration_DF (n + 1) := by
      simp only [filtPred]; rw [hz]; exact Submodule.zero_mem _
    have h2 := step_down (n + 1) z hn h1
    simp only [filtPred] at h2
    exact ih h2

theorem thm_29_1_iso (D : BBDataZero) :
    Function.Bijective D.a₀ := by

  apply filtered_bij

  rw [thm_29_1_gr_eq_pullback D]

  exact (thm_29_1_grDF_eq_O_TstarF D).comp D.p_star_bijective



structure PartialFlagData where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  X : SmoothAlgVariety.{u}
  DX : CAlgebra.{u}
  DMod : AbCat.{u}
  DXMod : AbCat.{u}
  Gamma : DMod.Obj ⥤ DXMod.Obj
  Loc : DXMod.Obj ⥤ DMod.Obj

attribute [instance] PartialFlagData.instLieRing PartialFlagData.instLieAlgebra
  PartialFlagData.instSemisimple


structure TwistedDiffOps (X : SmoothAlgVariety.{u}) (WeightSpace : Type u) where
  weight : WeightSpace
  algebra : CAlgebra.{u}

structure TwistedDModuleCat (X : SmoothAlgVariety.{u}) (WeightSpace : Type u) where
  weight : WeightSpace
  cat : AbCat.{u}

structure BBDataTwisted where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  WeightSpace : Type u
  IsAntidominant : WeightSpace → Prop
  FlagVar : SmoothAlgVariety.{u}
  DOfWeight : WeightSpace → CAlgebra.{u}
  UOfWeight : WeightSpace → CAlgebra.{u}
  projOfWeight : (mu : WeightSpace) →
    @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ]
      (UOfWeight mu).carrier
  actionMapOfWeight : (mu : WeightSpace) →
    @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ]
      (DOfWeight mu).carrier
  aOfWeight : (mu : WeightSpace) →
    (UOfWeight mu).carrier →ₐ[ℂ] (DOfWeight mu).carrier


  NilpCone : Type u
  CotangentBundle : Type u
  grUOfWeight : WeightSpace → GradedAlgebra.{u}
  grDOfWeight : WeightSpace → GradedAlgebra.{u}
  O_TstarF : GradedAlgebra.{u}
  gr_aOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier →ₐ[ℂ] (grDOfWeight mu).carrier
  p_starOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier →ₐ[ℂ] O_TstarF.carrier
  incl_TstarFOfWeight : (mu : WeightSpace) →
    O_TstarF.carrier →ₐ[ℂ] (grDOfWeight mu).carrier
  p_starOfWeight_bijective : ∀ mu : WeightSpace,
    Function.Bijective (p_starOfWeight mu)
  symbol_projOfWeight : (mu : WeightSpace) →
    (grDOfWeight mu).carrier →ₐ[ℂ] O_TstarF.carrier
  symbol_projOfWeight_left_inv : ∀ (mu : WeightSpace),
    Function.LeftInverse (symbol_projOfWeight mu) (incl_TstarFOfWeight mu)

  generators_grUOfWeight : (mu : WeightSpace) → Set (grUOfWeight mu).carrier
  grUOfWeight_generated : ∀ mu : WeightSpace,
    Algebra.adjoin ℂ (generators_grUOfWeight mu) = ⊤
  generators_grUOfWeight_deg1 : (mu : WeightSpace) → Set (grUOfWeight mu).carrier
  generators_grUOfWeight_decomp : ∀ mu : WeightSpace,
    generators_grUOfWeight mu ⊆
      Set.range (algebraMap ℂ (grUOfWeight mu).carrier) ∪ generators_grUOfWeight_deg1 mu
  symbolOfActionOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier → (grDOfWeight mu).carrier
  gr_aOfWeight_eq_symbolOfAction_field : ∀ (mu : WeightSpace)
    (x : (grUOfWeight mu).carrier), x ∈ generators_grUOfWeight_deg1 mu →
    gr_aOfWeight mu x = symbolOfActionOfWeight mu x
  incl_p_star_eq_symbolOfActionOfWeight_field : ∀ (mu : WeightSpace)
    (x : (grUOfWeight mu).carrier), x ∈ generators_grUOfWeight_deg1 mu →
    (incl_TstarFOfWeight mu).comp (p_starOfWeight mu) x =
      symbolOfActionOfWeight mu x


  filtration_UOfWeight : (mu : WeightSpace) → ℕ → Submodule ℂ (UOfWeight mu).carrier
  filtration_DOfWeight : (mu : WeightSpace) → ℕ → Submodule ℂ (DOfWeight mu).carrier
  filtration_UOfWeight_exhaustive : ∀ mu x, ∃ n, x ∈ filtration_UOfWeight mu n
  filtration_UOfWeight_mono : ∀ mu, ∀ ⦃m n⦄, m ≤ n →
    filtration_UOfWeight mu m ≤ filtration_UOfWeight mu n

  filtration_DOfWeight_exhaustive : ∀ mu y, ∃ n, y ∈ filtration_DOfWeight mu n


  DModOfWeight : WeightSpace → AbCat.{u}
  UModOfWeight : WeightSpace → AbCat.{u}
  GammaOfWeight : (mu : WeightSpace) → (DModOfWeight mu).Obj ⥤ (UModOfWeight mu).Obj
  LocOfWeight : (mu : WeightSpace) → (UModOfWeight mu).Obj ⥤ (DModOfWeight mu).Obj

  aOfWeight_filtration_preserving : ∀ mu n (x : (UOfWeight mu).carrier),
    x ∈ filtration_UOfWeight mu n → aOfWeight mu x ∈ filtration_DOfWeight mu n
  quotient_UOfWeight : (mu : WeightSpace) → (n : ℕ) →
    { x : (UOfWeight mu).carrier // x ∈ filtration_UOfWeight mu n } → (grUOfWeight mu).carrier
  quotient_DOfWeight : (mu : WeightSpace) → (n : ℕ) →
    { y : (DOfWeight mu).carrier // y ∈ filtration_DOfWeight mu n } → (grDOfWeight mu).carrier
  quotient_UOfWeight_ker : ∀ mu n (x : (UOfWeight mu).carrier)
    (hx : x ∈ filtration_UOfWeight mu n),
    quotient_UOfWeight mu n ⟨x, hx⟩ = 0 ↔ x ∈ filtPred (filtration_UOfWeight mu) n
  quotient_DOfWeight_ker : ∀ mu n (y : (DOfWeight mu).carrier)
    (hy : y ∈ filtration_DOfWeight mu n),
    quotient_DOfWeight mu n ⟨y, hy⟩ = 0 ↔ y ∈ filtPred (filtration_DOfWeight mu) n
  gr_aOfWeight_compat : ∀ mu n (x : (UOfWeight mu).carrier)
    (hx : x ∈ filtration_UOfWeight mu n),
    gr_aOfWeight mu (quotient_UOfWeight mu n ⟨x, hx⟩) =
      quotient_DOfWeight mu n ⟨aOfWeight mu x, aOfWeight_filtration_preserving mu n x hx⟩
  quotient_DOfWeight_sub : ∀ mu n (y₁ y₂ : (DOfWeight mu).carrier)
    (hy₁ : y₁ ∈ filtration_DOfWeight mu n) (hy₂ : y₂ ∈ filtration_DOfWeight mu n)
    (hy_sub : y₁ - y₂ ∈ filtration_DOfWeight mu n),
    quotient_DOfWeight mu n ⟨y₁ - y₂, hy_sub⟩ =
      quotient_DOfWeight mu n ⟨y₁, hy₁⟩ - quotient_DOfWeight mu n ⟨y₂, hy₂⟩
  filtration_DOfWeight_mono : ∀ mu, ∀ ⦃m n⦄, m ≤ n →
    filtration_DOfWeight mu m ≤ filtration_DOfWeight mu n
  quotient_DOfWeight_surj : ∀ mu (z : (grDOfWeight mu).carrier),
    ∃ n, ∃ y : (DOfWeight mu).carrier, ∃ hy : y ∈ filtration_DOfWeight mu n,
      quotient_DOfWeight mu n ⟨y, hy⟩ = z
  quotient_UOfWeight_surj : ∀ mu (z : (grUOfWeight mu).carrier),
    ∃ n, ∃ x : (UOfWeight mu).carrier, ∃ hx : x ∈ filtration_UOfWeight mu n,
      quotient_UOfWeight mu n ⟨x, hx⟩ = z
  aOfWeight_factors_field : ∀ (mu : WeightSpace)
    (x : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    aOfWeight mu (projOfWeight mu x) = actionMapOfWeight mu x
  actionMapOfWeight_surjective_field : ∀ (mu : WeightSpace),
    Function.Surjective (actionMapOfWeight mu)
  gr_aOfWeight_approx_surj : ∀ (mu : WeightSpace) (n : ℕ)
    (y : (DOfWeight mu).carrier) (hy : y ∈ filtration_DOfWeight mu n),
    ∃ (x : (UOfWeight mu).carrier) (hx : x ∈ filtration_UOfWeight mu n),
      quotient_DOfWeight mu n ⟨aOfWeight mu x, aOfWeight_filtration_preserving mu n x hx⟩ =
        quotient_DOfWeight mu n ⟨y, hy⟩

attribute [instance] BBDataTwisted.instLieRing BBDataTwisted.instLieAlgebra
  BBDataTwisted.instSemisimple


theorem BBDataTwisted.aOfWeight_factors (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace)
      (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
      D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
  D.aOfWeight_factors_field

theorem BBDataTwisted.actionMapOfWeight_surjective (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace),
      Function.Surjective (D.actionMapOfWeight mu) :=
  D.actionMapOfWeight_surjective_field

theorem BBDataTwisted.gr_aOfWeight_eq_symbolOfAction (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace)
      (x : (D.grUOfWeight mu).carrier), x ∈ D.generators_grUOfWeight_deg1 mu →
      D.gr_aOfWeight mu x = D.symbolOfActionOfWeight mu x :=
  D.gr_aOfWeight_eq_symbolOfAction_field

theorem BBDataTwisted.incl_p_star_eq_symbolOfActionOfWeight (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace)
      (x : (D.grUOfWeight mu).carrier), x ∈ D.generators_grUOfWeight_deg1 mu →
      (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x =
        D.symbolOfActionOfWeight mu x :=
  D.incl_p_star_eq_symbolOfActionOfWeight_field

theorem BBDataTwisted.gr_aOfWeight_step_down (D : BBDataTwisted) :
    ∀ mu, Function.Injective (D.gr_aOfWeight mu) →
      ∀ n (x : (D.UOfWeight mu).carrier), x ∈ D.filtration_UOfWeight mu n →
        D.aOfWeight mu x ∈ filtPred (D.filtration_DOfWeight mu) n →
          x ∈ filtPred (D.filtration_UOfWeight mu) n := by
  intro mu h_inj n x hx ha_x

  have ha_x_n : D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    D.aOfWeight_filtration_preserving mu n x hx

  have hq_D : D.quotient_DOfWeight mu n ⟨D.aOfWeight mu x, ha_x_n⟩ = 0 :=
    (D.quotient_DOfWeight_ker mu n (D.aOfWeight mu x) ha_x_n).mpr ha_x

  have hcompat := D.gr_aOfWeight_compat mu n x hx

  have hgr_zero : D.gr_aOfWeight mu (D.quotient_UOfWeight mu n ⟨x, hx⟩) = 0 := by
    rw [hcompat, hq_D]

  have hq_zero : D.quotient_UOfWeight mu n ⟨x, hx⟩ = 0 := by
    have h0 : D.gr_aOfWeight mu 0 = 0 := map_zero (D.gr_aOfWeight mu)
    rw [← h0] at hgr_zero
    exact h_inj hgr_zero

  exact (D.quotient_UOfWeight_ker mu n x hx).mp hq_zero

theorem BBDataTwisted.quotient_surj_from_aOfWeight (D : BBDataTwisted) :
    ∀ mu, Function.Surjective (D.aOfWeight mu) →
    ∀ (n : ℕ) (y : (D.DOfWeight mu).carrier) (hy : y ∈ D.filtration_DOfWeight mu n),
      ∃ x : (D.UOfWeight mu).carrier, ∃ hx : x ∈ D.filtration_UOfWeight mu n,
        D.quotient_DOfWeight mu n ⟨D.aOfWeight mu x, D.aOfWeight_filtration_preserving mu n x hx⟩ =
          D.quotient_DOfWeight mu n ⟨y, hy⟩ := by
  intro mu _h_surj n y hy
  exact D.gr_aOfWeight_approx_surj mu n y hy

theorem BBDataTwisted.gr_aOfWeight_step_up (D : BBDataTwisted) :
    ∀ mu, Function.Surjective (D.aOfWeight mu) →
      ∀ n (y : (D.DOfWeight mu).carrier), y ∈ D.filtration_DOfWeight mu n →
        ∃ x, x ∈ D.filtration_UOfWeight mu n ∧
          y - D.aOfWeight mu x ∈ filtPred (D.filtration_DOfWeight mu) n := by
  intro mu h_surj n y hy

  obtain ⟨x, hx, hq_eq⟩ := D.quotient_surj_from_aOfWeight mu h_surj n y hy
  refine ⟨x, hx, ?_⟩

  have ha_x_n : D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    D.aOfWeight_filtration_preserving mu n x hx

  have hy_sub_n : y - D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    (D.filtration_DOfWeight mu n).sub_mem hy ha_x_n

  have hsub := D.quotient_DOfWeight_sub mu n y (D.aOfWeight mu x) hy ha_x_n hy_sub_n

  have hq_zero : D.quotient_DOfWeight mu n ⟨y - D.aOfWeight mu x, hy_sub_n⟩ = 0 := by
    rw [hsub, hq_eq, sub_self]

  exact (D.quotient_DOfWeight_ker mu n (y - D.aOfWeight mu x) hy_sub_n).mp hq_zero

theorem BBDataTwisted.gr_aOfWeight_surj_of_levelwise_surj (D : BBDataTwisted) :
    ∀ mu,
      (∀ n (y : (D.DOfWeight mu).carrier), y ∈ D.filtration_DOfWeight mu n →
        ∃ x, x ∈ D.filtration_UOfWeight mu n ∧ D.aOfWeight mu x = y) →
      Function.Surjective (D.gr_aOfWeight mu) := by
  intro mu h z

  obtain ⟨n, y, hy, hyz⟩ := D.quotient_DOfWeight_surj mu z

  obtain ⟨x, hx, hax⟩ := h n y hy

  refine ⟨D.quotient_UOfWeight mu n ⟨x, hx⟩, ?_⟩

  rw [D.gr_aOfWeight_compat mu n x hx]

  subst hax
  exact hyz

theorem aOfWeight_factorization (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace)
      (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
      D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
  D.aOfWeight_factors

theorem incl_TstarFOfWeight_inj (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace), Function.Injective (D.incl_TstarFOfWeight mu) :=
  fun mu => (D.symbol_projOfWeight_left_inv mu).injective

theorem aOfWeight_surj (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace), Function.Surjective (D.aOfWeight mu) := by
  intro mu y
  obtain ⟨x, hx⟩ := D.actionMapOfWeight_surjective mu y
  exact ⟨D.projOfWeight mu x, by rw [D.aOfWeight_factors]; exact hx⟩

theorem gr_aOfWeight_eq_on_deg1 (D : BBDataTwisted) :
    ∀ (mu : D.WeightSpace) (x : (D.grUOfWeight mu).carrier),
      x ∈ D.generators_grUOfWeight_deg1 mu →
      D.gr_aOfWeight mu x = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x := by
  intro mu x hx


  have h1 : D.gr_aOfWeight mu x = D.symbolOfActionOfWeight mu x :=
    D.gr_aOfWeight_eq_symbolOfAction mu x hx
  have h2 : (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x =
      D.symbolOfActionOfWeight mu x :=
    D.incl_p_star_eq_symbolOfActionOfWeight mu x hx
  exact h1.trans h2.symm

theorem aOfWeight_comp_proj (D : BBDataTwisted) (mu : D.WeightSpace)
    (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra) :
    D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
  aOfWeight_factorization D mu x

theorem gr_aOfWeight_eq_on_generators (D : BBDataTwisted) (mu : D.WeightSpace)
    (x : (D.grUOfWeight mu).carrier) :
    x ∈ D.generators_grUOfWeight mu →
    D.gr_aOfWeight mu x = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x := by


  intro hx
  rcases D.generators_grUOfWeight_decomp mu hx with h_deg0 | h_deg1
  ·
    obtain ⟨r, rfl⟩ := h_deg0
    simp [AlgHom.commutes]
  ·
    exact gr_aOfWeight_eq_on_deg1 D mu x h_deg1

theorem incl_TstarFOfWeight_injective (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Injective (D.incl_TstarFOfWeight mu) :=
  incl_TstarFOfWeight_inj D mu

theorem thm_29_6_factorization (D : BBDataTwisted) (mu : D.WeightSpace) :
    D.actionMapOfWeight mu = (D.aOfWeight mu).comp (D.projOfWeight mu) := by


  ext x
  show D.actionMapOfWeight mu (UniversalEnvelopingAlgebra.ι ℂ x) =
    D.aOfWeight mu (D.projOfWeight mu (UniversalEnvelopingAlgebra.ι ℂ x))
  exact (aOfWeight_comp_proj D mu (UniversalEnvelopingAlgebra.ι ℂ x)).symm

theorem thm_29_6_gr_eq_pullback (D : BBDataTwisted) (mu : D.WeightSpace) :
    D.gr_aOfWeight mu = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) := by


  ext x
  have hx : x ∈ Algebra.adjoin ℂ (D.generators_grUOfWeight mu) := by
    rw [D.grUOfWeight_generated mu]; exact Algebra.mem_top
  exact Algebra.adjoin_induction
    (p := fun x _ => D.gr_aOfWeight mu x = ((D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu)) x)
    (fun y hy => gr_aOfWeight_eq_on_generators D mu y hy)
    (fun r => by simp [AlgHom.commutes])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => by simp [map_mul, ha, hb])
    hx

theorem filtered_surj_twisted (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Surjective (D.aOfWeight mu) → Function.Surjective (D.gr_aOfWeight mu) := by
  intro h_surj


  apply D.gr_aOfWeight_surj_of_levelwise_surj mu

  have step_up := D.gr_aOfWeight_step_up mu h_surj
  intro n
  induction n with
  | zero =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up 0 y hy
    simp only [filtPred, Submodule.mem_bot] at hresid
    exact ⟨x, hx_mem, (sub_eq_zero.mp hresid).symm⟩
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up (n + 1) y hy
    simp only [filtPred] at hresid
    obtain ⟨x', hx'_mem, hx'_eq⟩ := ih (y - D.aOfWeight mu x) hresid
    refine ⟨x + x', ?_, ?_⟩
    · exact Submodule.add_mem _ hx_mem
        (D.filtration_UOfWeight_mono mu (Nat.le_succ n) hx'_mem)
    · rw [map_add, hx'_eq, add_sub_cancel]

theorem gr_aOfWeight_surjective (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Surjective (D.gr_aOfWeight mu) :=
  filtered_surj_twisted D mu (aOfWeight_surj D mu)

theorem thm_29_6_grDF_eq_O_TstarF (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Bijective (D.incl_TstarFOfWeight mu) := by


  constructor
  · exact incl_TstarFOfWeight_injective D mu
  ·
    have h_gr_surj : Function.Surjective (D.gr_aOfWeight mu) := gr_aOfWeight_surjective D mu
    have h_eq := thm_29_6_gr_eq_pullback D mu
    intro y
    obtain ⟨x, hx⟩ := h_gr_surj y
    have : D.gr_aOfWeight mu x = ((D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu)) x := by
      rw [h_eq]
    rw [this] at hx
    exact ⟨D.p_starOfWeight mu x, hx⟩

theorem filtered_bijOfWeight (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Bijective (D.gr_aOfWeight mu) → Function.Bijective (D.aOfWeight mu) := by
  intro hgr_bij
  refine ⟨?_, aOfWeight_surj D mu⟩

  have step_down := D.gr_aOfWeight_step_down mu hgr_bij.1
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  set z := x - y
  have hz : D.aOfWeight mu z = 0 := by simp [z, map_sub, hxy]
  obtain ⟨n, hn⟩ := D.filtration_UOfWeight_exhaustive mu z
  induction n with
  | zero =>
    have h1 : D.aOfWeight mu z ∈ filtPred (D.filtration_DOfWeight mu) 0 := by
      simp only [filtPred, Submodule.mem_bot]; exact hz
    have h2 := step_down 0 z hn h1
    simp only [filtPred, Submodule.mem_bot] at h2
    exact h2
  | succ n ih =>
    have h1 : D.aOfWeight mu z ∈ filtPred (D.filtration_DOfWeight mu) (n + 1) := by
      simp only [filtPred]; rw [hz]; exact Submodule.zero_mem _
    have h2 := step_down (n + 1) z hn h1
    simp only [filtPred] at h2
    exact ih h2

theorem thm_29_6_iso (D : BBDataTwisted) (mu : D.WeightSpace) :
    Function.Bijective (D.aOfWeight mu) := by

  apply filtered_bijOfWeight

  rw [thm_29_6_gr_eq_pullback D mu]

  exact (thm_29_6_grDF_eq_O_TstarF D mu).comp (D.p_starOfWeight_bijective mu)



end

end BeilinsonBernstein
