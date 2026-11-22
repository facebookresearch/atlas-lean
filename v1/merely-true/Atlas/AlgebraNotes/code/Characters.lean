/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.GroupTheory.ClassEquation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.ToLin

universe u

noncomputable section

open Classical

namespace CharacterTheory

open Representation

abbrev HomG {k : Type u} [CommRing k] {G : Type u} [Monoid G]
    {V : Type u} [AddCommMonoid V] [Module k V]
    {W : Type u} [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (ψ : Representation k G W) :=
  ρ.IntertwiningMap ψ

theorem schur_dim_HomG
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Type u} [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    Module.finrank k (HomG ρ σ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  change Module.finrank k (ρ.IntertwiningMap σ) = _
  split_ifs with h
  · obtain ⟨e⟩ := h
    have equiv : (ρ.IntertwiningMap σ) ≃ₗ[k] (σ.IntertwiningMap σ) := {
      toFun := fun f => Representation.IntertwiningMap.comp f e.toIntertwiningMap
      invFun := fun g => Representation.IntertwiningMap.comp g e.symm.toIntertwiningMap
      left_inv := by intro f; ext v; simp [Representation.IntertwiningMap.comp]
      right_inv := by intro g; ext w; simp [Representation.IntertwiningMap.comp]
      map_add' := by intro f g; ext; simp [Representation.IntertwiningMap.comp]
      map_smul' := by intro c f; ext; simp [Representation.IntertwiningMap.comp]
    }
    rw [LinearEquiv.finrank_eq equiv]
    exact Representation.IsIrreducible.finrank_intertwiningMap_self σ
  · haveI : IsEmpty (ρ.Equiv σ) := by
      rw [isEmpty_iff]; intro e; exact h ⟨e.symm⟩
    haveI : Subsingleton (ρ.IntertwiningMap σ) := inferInstance
    haveI : Unique (ρ.IntertwiningMap σ) := uniqueOfSubsingleton 0
    exact Module.finrank_zero_of_subsingleton

lemma rep_convolution_eq_comp
    {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (φ ψ : MonoidAlgebra k G) :
    ρ.asAlgebraHom (φ * ψ) = ρ.asAlgebraHom φ * ρ.asAlgebraHom ψ :=
  ρ.asAlgebraHom.map_mul φ ψ

def convolution {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {k : Type*} [CommSemiring k] (φ ψ : G → k) : G → k :=
  fun g => ∑ h : G, φ h * ψ (h⁻¹ * g)

def IsClassFunction {G : Type u} [Group G] {k : Type u} [Field k] (f : G → k) : Prop :=
  ∀ g h : G, f (h * g * h⁻¹) = f g

noncomputable def classInnerProduct {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    [Invertible (Nat.card G : k)] (f₁ f₂ : G → k) : k :=
  (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹

theorem character_orthonormality {G : Type u} [Group G] {k : Type u} [Field k]
    {V W : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    classInnerProduct ρ.character σ.character =
      if Nonempty (σ.Equiv ρ) then (1 : k) else 0 := by
  simp only [classInnerProduct]
  exact Representation.char_orthonormal ρ σ

theorem character_selfInnerProduct_eq_sum_sq_aux
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    [Invertible (Nat.card G : k)] [IsAlgClosed k]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (h_pairwise : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    (n : ι → ℕ)
    (χ : G → k)
    (hχ : ∀ g : G, χ g = ∑ i, (n i : k) * (ρ i).character g) :
    classInnerProduct χ χ = ∑ i, ((n i : k) ^ 2) := by
  have hexp : classInnerProduct χ χ = ∑ i, ∑ j, (n i : k) * (n j : k) *
      ((Nat.card G : k)⁻¹ * ∑ g : G, (ρ i).character g * (ρ j).character g⁻¹) := by
    simp only [classInnerProduct]
    rw [Finset.mul_sum]
    simp_rw [hχ]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext g
    rw [Finset.sum_comm]
    congr 1; ext i
    congr 1; ext j
    ring
  rw [hexp]
  congr 1; ext i
  have h_ortho : ∀ j, (n i : k) * (n j : k) *
      ((Nat.card G : k)⁻¹ * ∑ g : G, (ρ i).character g * (ρ j).character g⁻¹) =
      if j = i then (n i : k) ^ 2 else 0 := by
    intro j
    rw [Representation.char_orthonormal (ρ i) (ρ j)]
    by_cases hij : i = j
    · subst hij
      have hself : Nonempty ((ρ i).Equiv (ρ i)) := ⟨Representation.Equiv.refl _⟩
      simp only [hself, ite_true, mul_one, ite_true]
      ring
    · have hne : ¬Nonempty ((ρ j).Equiv (ρ i)) := by
        intro ⟨e⟩; exact h_pairwise i j hij ⟨e.symm⟩
      simp only [hne, ite_false, mul_zero, show ¬(j = i) from fun h => hij h.symm, ite_false]
  simp_rw [h_ortho]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

set_option backward.isDefEq.respectTransparency false in
theorem isIrreducible_of_finrank_intertwiningMap_eq_one
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Invertible (Nat.card G : k)] [IsAlgClosed k]
    (σ : Representation k G V)
    (hfr : Module.finrank k (σ.IntertwiningMap σ) = 1) :
    σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  haveI : IsSemisimpleRing (MonoidAlgebra k G) := MonoidAlgebra.Submodule.instIsSemisimpleModule
  have hfr_end : Module.finrank k (Module.End (MonoidAlgebra k G) σ.asModule) = 1 := by
    rw [← LinearEquiv.finrank_eq (IntertwiningMap.equivAlgEnd σ).toLinearEquiv]; exact hfr
  have hV_ne : Nontrivial σ.asModule := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Module.finrank k (Module.End (MonoidAlgebra k G) σ.asModule) = 0 := by
      haveI : Subsingleton (Module.End (MonoidAlgebra k G) σ.asModule) :=
        ⟨fun f g => LinearMap.ext fun x => @Subsingleton.elim _ hnt _ _⟩
      exact Module.finrank_zero_of_subsingleton
    linarith
  have hid_ne : (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) ≠ 0 := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hV_ne.exists_pair_ne
    have hx := LinearMap.ext_iff.mp heq x
    have hy := LinearMap.ext_iff.mp heq y
    simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
    exact hxy (by rw [hx, hy])
  exact {
    exists_pair_ne := ⟨⊥, ⊤, by
      intro heq
      obtain ⟨x, y, hxy⟩ := hV_ne.exists_pair_ne
      have hx : x ∈ (⊥ : Submodule (MonoidAlgebra k G) σ.asModule) := heq ▸ Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (MonoidAlgebra k G) σ.asModule) := heq ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      exact hxy (by rw [hx, hy])⟩
    eq_bot_or_eq_top := fun S => by
      obtain ⟨T, hST⟩ := exists_isCompl S
      set p := S.subtype.comp (Submodule.linearProjOfIsCompl S T hST)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid_ne).mp hfr_end p
      have hp_idem : p.comp p = p := by
        ext x
        simp only [p, LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply,
          Submodule.subtype_apply]
        congr 1
        exact Submodule.linearProjOfIsCompl_apply_left hST _
      have hc2 : c * c = c := by
        have h1 : (c * c) • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) =
            c • LinearMap.id := by
          have hcomp : (c • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule)).comp
              (c • LinearMap.id) = (c * c) • LinearMap.id := by
            ext x; simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
              smul_smul, mul_comm]
          have hcomp2 : (c • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule)).comp
              (c • LinearMap.id) = c • LinearMap.id := by
            have := hp_idem; rw [← hc] at this; exact this
          rw [← hcomp]; exact hcomp2
        have h2 : (c * c - c) • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) = 0 := by
          rw [sub_smul, h1, sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hid_ne
      have hc01 : c = 0 ∨ c = 1 := by
        have h3 : c * (c - 1) = 0 := by linear_combination hc2 - c
        rcases mul_eq_zero.mp h3 with h4 | h4
        · left; exact h4
        · right; exact sub_eq_zero.mp h4
      rcases hc01 with rfl | rfl
      · left
        have hp0 : p = 0 := by rw [hc.symm]; simp only [zero_smul]
        ext x; constructor
        · intro hx
          have hmem : (Submodule.linearProjOfIsCompl S T hST x : σ.asModule) = x := by
            have := Submodule.linearProjOfIsCompl_apply_left hST ⟨x, hx⟩
            exact congrArg Subtype.val this
          have h0 : (p x : σ.asModule) = 0 := by
            have := LinearMap.ext_iff.mp hp0 x
            simp only [LinearMap.zero_apply] at this
            exact this
          simp only [p, LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply,
            Submodule.subtype_apply] at h0
          rw [← hmem]; exact h0
        · intro hx
          simp only [Submodule.mem_bot] at hx
          rw [hx]; exact S.zero_mem
      · right
        rw [eq_top_iff]; intro x _
        have hp1 : p = LinearMap.id := by rw [hc.symm]; simp only [one_smul]
        have hpx : (↑(Submodule.linearProjOfIsCompl S T hST x) : σ.asModule) = x := by
          have h := LinearMap.ext_iff.mp hp1 x
          simp only [p, LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply,
            Submodule.subtype_apply, LinearMap.id_apply] at h
          exact h
        exact hpx ▸ (Submodule.linearProjOfIsCompl S T hST x).2
  }

theorem character_selfInnerProduct_irreducible_iff_aux
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Invertible (Nat.card G : k)] [IsAlgClosed k] [CharZero k]
    (σ : Representation k G V) :
    σ.IsIrreducible ↔ classInnerProduct σ.character σ.character = 1 := by
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ σ
  simp only [classInnerProduct]
  constructor
  · intro hirr
    rw [key, Representation.IsIrreducible.finrank_intertwiningMap_self σ]
    norm_cast
  · intro h
    rw [key] at h
    have hfr : Module.finrank k (σ.IntertwiningMap σ) = 1 := by exact_mod_cast h
    exact isIrreducible_of_finrank_intertwiningMap_eq_one σ hfr

theorem character_selfInnerProduct_corollary
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    [Invertible (Nat.card G : k)] [IsAlgClosed k] [CharZero k]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (h_pairwise : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    (n : ι → ℕ)
    (χ : G → k)
    (hχ : ∀ g : G, χ g = ∑ i, (n i : k) * (ρ i).character g) :
    (classInnerProduct χ χ = ∑ i, ((n i : k) ^ 2)) ∧
    (∀ {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (σ : Representation k G W),
      σ.IsIrreducible ↔ classInnerProduct σ.character σ.character = 1) :=
  ⟨character_selfInnerProduct_eq_sum_sq_aux ρ h_pairwise n χ hχ,
   fun σ => character_selfInnerProduct_irreducible_iff_aux σ⟩

theorem mainTheorem_wedderburn (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)

theorem mainTheorem_sum_sq_eq_card (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      (∑ i, (d i) ^ 2 = Nat.card G) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := mainTheorem_wedderburn k G
  refine ⟨n, d, hd, ?_, ⟨e⟩⟩
  have hdim : Module.finrank k (MonoidAlgebra k G) =
      Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [show Module.finrank k (MonoidAlgebra k G) = Nat.card G from by
    change Module.finrank k (G →₀ k) = _; rw [Module.finrank_finsupp]; simp] at hdim
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at hdim
  rw [hdim]; congr 1; funext i; ring

theorem rat_int_of_pow_int
    (r : ℚ) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ n : ℕ, ∃ m : ℤ, (d : ℚ) * r ^ n = ↑m) :
    ∃ z : ℤ, r = ↑z := by
  suffices r.den = 1 from ⟨r.num, ((Rat.den_eq_one_iff r).mp this).symm⟩

  have hden_dvd : ∀ n : ℕ, (r.den : ℤ) ^ n ∣ d := by
    intro n
    obtain ⟨m, hm⟩ := h n
    have hr : r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    have key : d * r.num ^ n = m * (r.den : ℤ) ^ n := by
      have hcast : (d : ℚ) * (r.num : ℚ) ^ n = (m : ℚ) * (r.den : ℚ) ^ n := by
        rw [hr] at hm; rw [div_pow] at hm; field_simp at hm ⊢; linarith
      exact_mod_cast hcast
    have hcop : IsCoprime (r.num : ℤ) (r.den : ℤ) := by
      have hred := r.reduced.isCoprime
      rcases Int.natAbs_eq r.num with hpos | hneg
      · rw [hpos]; exact hred
      · rw [hneg]; exact IsCoprime.neg_left hred
    have hcop_pow : IsCoprime (r.num ^ n : ℤ) ((r.den : ℤ) ^ n) := hcop.pow
    have hdvd_prod : (r.den : ℤ) ^ n ∣ d * r.num ^ n := ⟨m, by linarith⟩
    rw [mul_comm] at hdvd_prod
    exact hcop_pow.symm.dvd_of_dvd_mul_left hdvd_prod

  by_contra hden_ne_one
  have hbpos : 1 < r.den := by have := r.den_pos; omega
  have hle : ∀ n : ℕ, r.den ^ n ≤ d.natAbs := by
    intro n
    have h1 : (↑(r.den ^ n) : ℤ) ∣ d := by push_cast; exact hden_dvd n
    have h2 : (↑(r.den ^ n) : ℤ) ≤ |d| :=
      Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs (↑(r.den ^ n)) d).mpr h1)
    rw [Int.abs_eq_natAbs] at h2
    exact_mod_cast h2
  have hgrow : d.natAbs < r.den ^ (d.natAbs + 1) := by
    have h1 : d.natAbs < 2 ^ d.natAbs := Nat.lt_two_pow_self
    have h2 : 2 ^ d.natAbs ≤ r.den ^ d.natAbs := Nat.pow_le_pow_left hbpos _
    have h3 : r.den ^ d.natAbs ≤ r.den ^ (d.natAbs + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    linarith
  linarith [hle (d.natAbs + 1)]

section MatrixSimpleModule
open Matrix


theorem char_charpoly_roots_pow_eq_one
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ∀ μ ∈ ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ g)).charpoly.roots),
      μ ^ Fintype.card G = 1 := by
  classical
  set f : Module.End ℂ V := ρ g
  set b := Module.finBasis ℂ V
  have hord : f ^ Fintype.card G = 1 := by
    simp only [f, ← map_pow, pow_card_eq_one, map_one]
  intro μ hμ
  have hev : Module.End.HasEigenvalue f μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero)).mp hμ
  have hev_minpoly : (minpoly ℂ f).IsRoot μ := by
    rwa [Module.End.hasEigenvalue_iff_isRoot] at hev
  have hdvd : minpoly ℂ f ∣ (Polynomial.X ^ Fintype.card G - 1) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
    exact sub_eq_zero.mpr hord
  have hμ_root : (Polynomial.X ^ Fintype.card G - 1 : Polynomial ℂ).IsRoot μ := by
    obtain ⟨r, hr⟩ := hdvd
    rw [Polynomial.IsRoot.def] at hev_minpoly ⊢
    rw [hr, Polynomial.eval_mul, hev_minpoly, zero_mul]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
             Polynomial.eval_X, Polynomial.eval_one] at hμ_root
  exact sub_eq_zero.mp hμ_root

theorem char_inv_eq_conj
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) := by
  classical
  set f : Module.End ℂ V := ρ g
  set f' : Module.End ℂ V := ρ g⁻¹
  have hord : f ^ Fintype.card G = 1 := by
    simp only [f, ← map_pow, pow_card_eq_one, map_one]
  have hfg : f * f' = 1 := by simp only [f, f', ← map_mul, mul_inv_cancel, map_one]
  have hgf : f' * f = 1 := by simp only [f, f', ← map_mul, inv_mul_cancel, map_one]
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun hgf x)
  have hss : Module.End.IsSemisimple f := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ)
        (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne') one_ne_zero).squarefree
    · simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]; exact sub_eq_zero.mpr hord
  have hint : DirectSum.IsInternal (fun μ : ℂ => f.eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  have hfin : {μ : ℂ | f.eigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.eigenspaces_iSupIndep
  have hf_maps : ∀ μ : ℂ, Set.MapsTo f (↑(f.eigenspace μ)) (↑(f.eigenspace μ)) := fun μ v hv => by
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv ⊢
    show f (f v) = μ • (f v); rw [hv, map_smul, hv]

  have hg_maps : ∀ μ : ℂ, Set.MapsTo f' (↑(f.eigenspace μ)) (↑(f.eigenspace μ)) := fun μ v hv => by
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv ⊢
    show f (f' v) = μ • (f' v)
    have hfgv : f (f' v) = v := LinearMap.congr_fun hfg v
    have hgfv : f' (f v) = v := LinearMap.congr_fun hgf v
    rw [hv, map_smul] at hgfv; rw [hfgv, hgfv]
  show (LinearMap.trace ℂ V) f' = (starRingEnd ℂ) ((LinearMap.trace ℂ V) f)
  rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hf_maps,
      LinearMap.trace_eq_sum_trace_restrict' hint hfin hg_maps, map_sum]
  congr 1; ext μ
  by_cases hμ_bot : f.eigenspace μ = ⊥
  · have hdim : Module.finrank ℂ (f.eigenspace μ) = 0 := by simp [hμ_bot]
    haveI : Subsingleton (f.eigenspace μ) := Module.finrank_zero_iff.mp hdim
    simp [Subsingleton.elim (f.restrict (hf_maps μ)) 0,
          Subsingleton.elim (f'.restrict (hg_maps μ)) 0]
  · have hμ_ne : μ ≠ 0 := by
      intro hμ0; apply hμ_bot; rw [hμ0, Submodule.eq_bot_iff]; intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv; simp only [zero_smul] at hv
      exact hinj (hv.trans (map_zero f).symm)
    have hμ_pow : μ ^ Fintype.card G = 1 := by
      have hev : Module.End.HasEigenvalue f μ := by
        rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue]; exact hμ_bot
      have hev_mp : (minpoly ℂ f).IsRoot μ := Module.End.hasEigenvalue_iff_isRoot.mp hev
      have hdvd : minpoly ℂ f ∣ (Polynomial.X ^ Fintype.card G - 1) := by
        apply minpoly.dvd; simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
        exact sub_eq_zero.mpr hord
      have hroot : (Polynomial.X ^ Fintype.card G - 1 : Polynomial ℂ).IsRoot μ := by
        obtain ⟨r, hr⟩ := hdvd; rw [Polynomial.IsRoot.def] at hev_mp ⊢
        rw [hr, Polynomial.eval_mul, hev_mp, zero_mul]
      simpa [Polynomial.IsRoot.def, sub_eq_zero] using hroot
    have hconj : starRingEnd ℂ μ = μ⁻¹ :=
      (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hμ_pow
        (Fintype.card_pos (α := G)).ne')).symm
    have hf_restr : f.restrict (hf_maps μ) = μ • LinearMap.id := by
      ext ⟨v, hv⟩
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact Module.End.mem_eigenspace_iff.mp hv
    have hg_restr : f'.restrict (hg_maps μ) = μ⁻¹ • LinearMap.id := by
      ext ⟨v, hv⟩
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hev : f v = μ • v := Module.End.mem_eigenspace_iff.mp hv
      have hgfv : f' (f v) = v := LinearMap.congr_fun hgf v
      rw [hev, map_smul] at hgfv
      exact smul_right_injective V hμ_ne
        (hgfv.trans (smul_inv_smul₀ hμ_ne v).symm)
    rw [hf_restr, hg_restr, ← hconj]
    simp [map_smul, LinearMap.trace_id, smul_eq_mul, map_mul, map_natCast]

theorem char_dual_eq_conj
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.dual.character g = starRingEnd ℂ (ρ.character g) := by
  rw [Representation.char_dual, char_inv_eq_conj]

theorem char_value_properties
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (∀ μ ∈ ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ g)).charpoly.roots),
      μ ^ Fintype.card G = 1) ∧
    (ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g)) ∧
    (ρ.dual.character g = starRingEnd ℂ (ρ.character g)) :=
  ⟨char_charpoly_roots_pow_eq_one ρ g, char_inv_eq_conj ρ g, char_dual_eq_conj ρ g⟩

theorem abelian_irrep_one_dimensional
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [CommGroup G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (hirr : ρ.IsIrreducible) :
    Module.finrank k V = 1 := by
  haveI := hirr
  haveI : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ

end MatrixSimpleModule

end CharacterTheory

namespace CharacterTheory

open Representation Module CategoryTheory
open scoped Classical

theorem multiplicity_eq_finrank_intertwining
    {G k : Type*} [Group G] [Fintype G] [Field k] [IsAlgClosed k]
    [Invertible (Nat.card G : k)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (h_pairwise : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W)
    (d : ι → ℕ)
    (h_decomp : Nonempty (Representation.Equiv σ
      (Representation.directSum (ι := (i : ι) × Fin (d i)) (fun p => ρ p.1)))) :
    ∀ i, d i = Module.finrank k ((ρ i).IntertwiningMap σ) := by

  have h_hom_dist : ∀ i, Module.finrank k ((ρ i).IntertwiningMap σ) =
      ∑ p : (j : ι) × Fin (d j), Module.finrank k ((ρ i).IntertwiningMap (ρ p.1)) := by
    intro i
    obtain ⟨e⟩ := h_decomp


    have equiv1 : (ρ i).IntertwiningMap σ ≃ₗ[k] (ρ i).IntertwiningMap
        (Representation.directSum (ι := (j : ι) × Fin (d j)) (fun p => ρ p.1)) := {
      toFun := fun f => Representation.IntertwiningMap.comp e.toIntertwiningMap f
      invFun := fun g => Representation.IntertwiningMap.comp e.symm.toIntertwiningMap g
      left_inv := fun f => by ext v; simp [Representation.IntertwiningMap.comp]
      right_inv := fun g => by ext v; simp [Representation.IntertwiningMap.comp]
      map_add' := fun f g => by ext; simp [Representation.IntertwiningMap.comp]
      map_smul' := fun c f => by ext; simp [Representation.IntertwiningMap.comp]
    }


    have equiv2 : (ρ i).IntertwiningMap
        (Representation.directSum (ι := (j : ι) × Fin (d j)) (fun p => ρ p.1)) ≃ₗ[k]
        ((p : (j : ι) × Fin (d j)) → (ρ i).IntertwiningMap (ρ p.1)) := {
      toFun := fun f p => {
        toLinearMap := (DirectSum.component k _ _ p).comp f.toLinearMap
        isIntertwining' := fun g => by
          ext u; simp only [LinearMap.comp_apply]
          have hf := congr($(f.isIntertwining' g) u)
          simp only [LinearMap.comp_apply] at hf
          show (DirectSum.component k _ _ p) (f.toLinearMap ((ρ i) g u)) =
               (ρ p.1 g) ((DirectSum.component k _ _ p) (f.toLinearMap u))
          rw [hf]
          simp only [Representation.directSum, DirectSum.component, DirectSum.lmap]; rfl
      }
      invFun := fun fs => {
        toLinearMap := (DirectSum.linearEquivFunOnFintype k _ _).symm.toLinearMap.comp
          (LinearMap.pi (fun p => (fs p).toLinearMap))
        isIntertwining' := fun g => by
          have key : ∀ p u, (fs p).toLinearMap ((ρ i) g u) =
              (ρ p.1 g) ((fs p).toLinearMap u) := by
            intro p u; exact congr($(((fs p).isIntertwining' g)) u)
          apply LinearMap.ext; intro u
          simp only [LinearMap.comp_apply]
          apply DFinsupp.ext; intro p
          simp only [Representation.directSum, DirectSum.lmap,
            DirectSum.linearEquivFunOnFintype, DFinsupp.linearEquivFunOnFintype,
            DFinsupp.mapRange.linearMap]
          exact key p u
      }
      left_inv := fun f => by
        apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro u
        simp only [LinearMap.comp_apply]; apply DFinsupp.ext; intro p; rfl
      right_inv := fun fs => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp only [LinearMap.comp_apply]; rfl
      map_add' := fun f g => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp [LinearMap.comp_apply, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c f => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, Pi.smul_apply]
    }

    rw [LinearEquiv.finrank_eq equiv1, LinearEquiv.finrank_eq equiv2,
        Module.finrank_pi_fintype]
  intro idx
  rw [h_hom_dist idx]

  have h_schur : ∀ p : (j : ι) × Fin (d j), Module.finrank k ((ρ idx).IntertwiningMap (ρ p.1)) =
      if p.1 = idx then 1 else 0 := by
    intro ⟨j, _⟩
    simp only
    by_cases h : j = idx
    · cases h
      simp only [ite_true]
      exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ idx)
    · simp only [h, ite_false]
      have hne : ¬Nonempty ((ρ idx).Equiv (ρ j)) :=
        h_pairwise idx j (fun hij => h hij.symm)
      haveI : IsEmpty ((ρ idx).Equiv (ρ j)) := isEmpty_iff.mpr (fun e => hne ⟨e⟩)
      haveI : Subsingleton ((ρ idx).IntertwiningMap (ρ j)) := inferInstance
      exact Module.finrank_zero_of_subsingleton
  simp_rw [h_schur]

  rw [Fintype.sum_sigma]
  have h1 : ∀ x : ι, ∑ _ : Fin (d x), (if x = idx then 1 else 0 : ℕ) =
    d x • (if x = idx then 1 else 0 : ℕ) := by
    intro x; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [h1, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', Finset.mem_univ]



noncomputable def repOfFun {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k) : V →ₗ[k] V :=
  ∑ g : G, f g • ρ g

lemma monoidAlgebra_pow_isIntegral
    {G : Type*} [Group G] [Fintype G]
    (φ : MonoidAlgebra ℂ G) (hφ : ∀ g : G, IsIntegral ℤ (φ g))
    (n : ℕ) : ∀ g : G, IsIntegral ℤ ((φ ^ n) g) := by
  induction n with
  | zero =>
    intro g
    simp only [pow_zero]
    by_cases hg : g = 1
    · subst hg; simp [MonoidAlgebra.one_def]; exact isIntegral_one
    · simp [MonoidAlgebra.one_def, hg]; exact isIntegral_zero
  | succ m ih =>
    intro g
    rw [pow_succ]
    have hmul : (φ ^ m * φ) g =
        ∑ p ∈ (Finset.univ (α := G × G)).filter (fun p => p.1 * p.2 = g),
          (φ ^ m) p.1 * φ p.2 := by
      apply MonoidAlgebra.mul_apply_antidiagonal; simp
    rw [hmul]
    apply IsIntegral.sum
    intro p _
    exact (ih p.1).mul (hφ p.2)

lemma repOfFun_eq_asAlgebraHom
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) :
    repOfFun ρ f = ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f) := by
  simp only [repOfFun, Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
  rw [Finsupp.sum_fintype _ _ (by intro g; simp)]
  simp [Finsupp.equivFunOnFinite]

lemma char_isIntegral
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) := by
  set F := ρ g
  have hord : F ^ Fintype.card G = 1 := by
    simp only [F, ← map_pow, pow_card_eq_one, map_one]
  set b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro μ hμ
  have hev : Module.End.HasEigenvalue F μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
        (LinearMap.charpoly_toMatrix F b).symm]
    exact (Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero)).mp hμ
  have hμ_pow : μ ^ Fintype.card G = 1 := by
    have hev_mp : (minpoly ℂ F).IsRoot μ :=
      (Module.End.hasEigenvalue_iff_isRoot).mp hev
    have hdvd : minpoly ℂ F ∣ (Polynomial.X ^ Fintype.card G - 1) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
      exact sub_eq_zero.mpr hord
    have hμ_root : (Polynomial.X ^ Fintype.card G - 1 : Polynomial ℂ).IsRoot μ := by
      obtain ⟨q, hq⟩ := hdvd
      rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul,
          (Polynomial.IsRoot.def ..).mpr hev_mp, zero_mul]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
               Polynomial.eval_X, Polynomial.eval_one] at hμ_root
    exact sub_eq_zero.mp hμ_root
  refine ⟨Polynomial.X ^ Fintype.card G - 1, ?_, ?_⟩
  · rw [show (1 : Polynomial ℤ) = Polynomial.C 1 from by simp]
    exact Polynomial.monic_X_pow_sub_C 1 (Fintype.card_pos (α := G)).ne'
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
               Polynomial.eval₂_one, hμ_pow, sub_self]

theorem repOfFun_scalar_rational_is_int
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) (r : ℚ)
    (hf : ∀ g : G, IsIntegral ℤ (f g))
    (hρf : repOfFun ρ f = (algebraMap ℚ ℂ r) • LinearMap.id)
    (hdim : Module.finrank ℂ V ≠ 0) :
    ∃ z : ℤ, r = ↑z := by
  apply rat_int_of_pow_int r (Module.finrank ℂ V : ℤ) (by exact_mod_cast hdim)
  intro n
  set φ : MonoidAlgebra ℂ G := Finsupp.equivFunOnFinite.symm f
  have hbase : ∀ g : G, IsIntegral ℤ (φ g) := by
    intro g; simp [φ, Finsupp.equivFunOnFinite]; exact hf g

  have hpow : (repOfFun ρ f) ^ n = ((algebraMap ℚ ℂ r) ^ n) • (LinearMap.id : V →ₗ[ℂ] V) := by
    rw [hρf]
    change ((algebraMap ℚ ℂ r) • (1 : Module.End ℂ V)) ^ n = _
    rw [smul_pow, one_pow]; rfl

  have htrace_eq : LinearMap.trace ℂ V ((repOfFun ρ f) ^ n) =
      (Module.finrank ℂ V : ℂ) * (algebraMap ℚ ℂ r) ^ n := by
    rw [hpow, LinearMap.map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

  have htrace_sum : LinearMap.trace ℂ V ((repOfFun ρ f) ^ n) =
      ∑ g : G, (φ ^ n) g * LinearMap.trace ℂ V (ρ g) := by
    conv_lhs => rw [repOfFun_eq_asAlgebraHom ρ f, ← map_pow]
    simp only [Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
    rw [Finsupp.sum_fintype _ _ (by intro g; simp), map_sum]
    congr 1; ext g; rw [LinearMap.map_smul, smul_eq_mul]

  have htrace_int : IsIntegral ℤ (LinearMap.trace ℂ V ((repOfFun ρ f) ^ n)) := by
    rw [htrace_sum]
    apply IsIntegral.sum
    intro g _
    exact (monoidAlgebra_pow_isIntegral φ hbase n g).mul (char_isIntegral ρ g)

  rw [htrace_eq] at htrace_int
  have hrat : (Module.finrank ℂ V : ℂ) * (algebraMap ℚ ℂ r) ^ n =
      algebraMap ℚ ℂ ((Module.finrank ℂ V : ℚ) * r ^ n) := by
    push_cast; ring
  rw [hrat] at htrace_int
  have hq_int : IsIntegral ℤ ((Module.finrank ℂ V : ℚ) * r ^ n) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp htrace_int
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq_int
  exact ⟨z, by exact_mod_cast hz.symm⟩

theorem repOfFun_comm_of_classFunction
    {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (h : G) :
    (repOfFun ρ f) ∘ₗ (ρ h) = (ρ h) ∘ₗ (repOfFun ρ f) := by
  ext v
  simp only [repOfFun, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  have mul_apply : ∀ (a b : G) (w : V), (ρ a) ((ρ b) w) = (ρ (a * b)) w := fun a b w => by
    rw [← LinearMap.comp_apply]
    exact congr_fun (congr_arg DFunLike.coe (ρ.map_mul a b).symm) w
  simp_rw [mul_apply]
  rw [← Fintype.sum_equiv ((Equiv.mulLeft h).trans (Equiv.mulRight h⁻¹)) _ _ (fun x => ?_)]
  show f x • (ρ (h * x)) v = f (h * x * h⁻¹) • (ρ (h * x * h⁻¹ * h)) v
  rw [hf x h, show h * x * h⁻¹ * h = h * x from by group]

theorem irred_rep_class_fun_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    ∃ c : k, repOfFun ρ f = c • LinearMap.id := by
  have hbij := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) (k := k)
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := repOfFun ρ f
      isIntertwining' := repOfFun_comm_of_classFunction ρ f hf }
  obtain ⟨c, hc⟩ := hbij.2 T
  exact ⟨c, by
    have h1 : T.toLinearMap = repOfFun ρ f := rfl
    rw [← h1, ← hc]; ext v; simp [Algebra.algebraMap_eq_smul_one]⟩

theorem rep_conj_char_eq_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ c : k, repOfFun ρ (fun g => ρ.character g⁻¹) = c • LinearMap.id ∧
      c * (Module.finrank k V : k) = (Nat.card G : k) := by

  have hcf : ∀ g h : G, ρ.character (h * g * h⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g h
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group]
    exact Representation.char_conj ρ g⁻¹ h

  obtain ⟨c, heq⟩ := irred_rep_class_fun_scalar ρ (fun g => ρ.character g⁻¹) hcf
  refine ⟨c, heq, ?_⟩

  have htrace := congr_arg (LinearMap.trace k V) heq
  rw [LinearMap.map_smul_of_tower, LinearMap.trace_id, smul_eq_mul] at htrace
  simp only [repOfFun, map_sum, LinearMap.map_smul_of_tower, smul_eq_mul] at htrace

  have key : ∑ g : G, ρ.character g * ρ.character g⁻¹ = c * ↑(finrank k V) := by
    rw [← htrace]
    simp only [Representation.character]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [inv_inv])

  have hortho : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k) := by
    have h := Representation.char_orthonormal ρ ρ
    simp only [show Nonempty (ρ.Equiv ρ) from ⟨Representation.Equiv.refl ρ⟩, ite_true] at h
    have hne : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
    exact mul_left_cancel₀ (inv_ne_zero hne) (h.trans (inv_mul_cancel₀ hne).symm)
  exact key.symm.trans hortho

lemma monoidAlgebra_pow_isIntegral_general
    {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    (φ : MonoidAlgebra k G) (hφ : ∀ g : G, IsIntegral ℤ (φ g))
    (n : ℕ) : ∀ g : G, IsIntegral ℤ ((φ ^ n) g) := by
  induction n with
  | zero =>
    intro g
    simp only [pow_zero]
    by_cases hg : g = 1
    · subst hg; simp [MonoidAlgebra.one_def]; exact isIntegral_one
    · simp [MonoidAlgebra.one_def, hg]; exact isIntegral_zero
  | succ m ih =>
    intro g
    rw [pow_succ]
    have hmul : (φ ^ m * φ) g =
        ∑ p ∈ (Finset.univ (α := G × G)).filter (fun p => p.1 * p.2 = g),
          (φ ^ m) p.1 * φ p.2 := by
      apply MonoidAlgebra.mul_apply_antidiagonal; simp
    rw [hmul]
    apply IsIntegral.sum
    intro p _
    exact (ih p.1).mul (hφ p.2)

lemma char_isIntegral_general
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace k V (ρ g)) := by
  set F := ρ g
  have hord : F ^ Fintype.card G = 1 := by
    simp only [F, ← map_pow, pow_card_eq_one, map_one]
  set b := Module.finBasis k V
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro μ hμ
  have hev : Module.End.HasEigenvalue F μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, (LinearMap.charpoly_toMatrix F b).symm]
    exact (Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero)).mp hμ
  have hμ_pow : μ ^ Fintype.card G = 1 := by
    have hdvd : minpoly k F ∣ (Polynomial.X ^ Fintype.card G - 1) := by
      apply minpoly.dvd; simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
      exact sub_eq_zero.mpr hord
    have hμ_root : (Polynomial.X ^ Fintype.card G - 1 : Polynomial k).IsRoot μ := by
      obtain ⟨q, hq⟩ := hdvd
      rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul,
          (Polynomial.IsRoot.def ..).mpr ((Module.End.hasEigenvalue_iff_isRoot).mp hev), zero_mul]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
               Polynomial.eval_X, Polynomial.eval_one] at hμ_root
    exact sub_eq_zero.mp hμ_root
  exact ⟨Polynomial.X ^ Fintype.card G - 1, by
    rw [show (1 : Polynomial ℤ) = Polynomial.C 1 from by simp]
    exact Polynomial.monic_X_pow_sub_C 1 (Fintype.card_pos (α := G)).ne', by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
               Polynomial.eval₂_one, hμ_pow, sub_self]⟩

theorem mainTheorem_dim_dvd_card_charZero
    {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [NeZero (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Nat.card G := by
  set d := Module.finrank k V

  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 := Representation.IsIrreducible.finrank_intertwiningMap_self ρ
    have hzero : Module.finrank k (V →ₗ[k] V) = 0 := by
      rw [Module.finrank_linearMap]; simp [show Module.finrank k V = 0 from h0]
    have hss : Subsingleton (V →ₗ[k] V) := Module.finrank_zero_iff.mp hzero
    have h2 : Module.finrank k (ρ.IntertwiningMap ρ) = 0 := Module.finrank_zero_iff.mpr
      ((Representation.IntertwiningMap.toLinearMap_injective ρ ρ).subsingleton)
    linarith
  have hdk_ne : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  haveI : Invertible (Nat.card G : k) := invertibleOfNonzero (NeZero.ne _)

  obtain ⟨c, hcf, hcd⟩ := rep_conj_char_eq_scalar ρ

  set r : ℚ := (Nat.card G : ℚ) / (d : ℚ)
  have hd_rat_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  have hc_eq : c = algebraMap ℚ k r := by
    have h1 : c = (Nat.card G : k) * (d : k)⁻¹ := by
      rw [← hcd, mul_assoc, mul_inv_cancel₀ hdk_ne, mul_one]
    rw [h1]; simp [r, map_div₀]; ring

  have hf_int : ∀ g : G, IsIntegral ℤ (ρ.character g⁻¹) := fun g =>
    char_isIntegral_general ρ g⁻¹

  have hρf : repOfFun ρ (fun g => ρ.character g⁻¹) = (algebraMap ℚ k r) • LinearMap.id := by
    rw [hcf, hc_eq]

  have h_pow_int : ∀ n : ℕ, ∃ m : ℤ, (d : ℚ) * r ^ n = ↑m := by
    intro n
    set φ : MonoidAlgebra k G := Finsupp.equivFunOnFinite.symm (fun g => ρ.character g⁻¹)
    have hbase : ∀ g : G, IsIntegral ℤ (φ g) := by
      intro g; simp [φ, Finsupp.equivFunOnFinite]; exact hf_int g

    have hpow : (repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n =
        ((algebraMap ℚ k r) ^ n) • (LinearMap.id : V →ₗ[k] V) := by
      rw [hρf]; change ((algebraMap ℚ k r) • (1 : Module.End k V)) ^ n = _
      rw [smul_pow, one_pow]; rfl

    have htrace_eq : LinearMap.trace k V ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n) =
        (d : k) * (algebraMap ℚ k r) ^ n := by
      rw [hpow, LinearMap.map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

    have htrace_sum : LinearMap.trace k V ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n) =
        ∑ g : G, (φ ^ n) g * LinearMap.trace k V (ρ g) := by
      conv_lhs => rw [show repOfFun ρ (fun g => ρ.character g⁻¹) =
        ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm (fun g => ρ.character g⁻¹)) from by
          simp only [repOfFun, Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
          rw [Finsupp.sum_fintype _ _ (by intro g; simp)]
          simp [Finsupp.equivFunOnFinite]]
      rw [← map_pow]
      simp only [Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
      rw [Finsupp.sum_fintype _ _ (by intro g; simp), map_sum]
      congr 1; ext g; rw [LinearMap.map_smul, smul_eq_mul]

    have htrace_int : IsIntegral ℤ (LinearMap.trace k V
        ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n)) := by
      rw [htrace_sum]; apply IsIntegral.sum; intro g _
      exact (monoidAlgebra_pow_isIntegral_general φ hbase n g).mul (char_isIntegral_general ρ g)

    rw [htrace_eq] at htrace_int
    have hrat : (d : k) * (algebraMap ℚ k r) ^ n = algebraMap ℚ k ((d : ℚ) * r ^ n) := by
      push_cast; ring
    rw [hrat] at htrace_int
    have hq_int : IsIntegral ℤ ((d : ℚ) * r ^ n) :=
      (isIntegral_algebraMap_iff (algebraMap ℚ k).injective).mp htrace_int
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq_int
    exact ⟨z, by exact_mod_cast hz.symm⟩

  have hr_int : ∃ z : ℤ, r = ↑z :=
    rat_int_of_pow_int r (d : ℤ) (by exact_mod_cast hd_ne) h_pow_int

  obtain ⟨z, hz⟩ := hr_int
  have hr_pos : (0 : ℚ) < r := by
    apply div_pos
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.pos_of_ne_zero hd_ne
  have hz_pos : 0 < z := by
    have : (0 : ℚ) < (z : ℚ) := hz ▸ hr_pos; exact_mod_cast this
  have key : d * z.toNat = Nat.card G := by
    have h1 : (d : ℚ) * r = (Nat.card G : ℚ) := mul_div_cancel₀ _ hd_rat_ne
    rw [hz] at h1
    have h2 : (d : ℤ) * z = (Nat.card G : ℤ) := by exact_mod_cast h1
    zify; rw [Int.toNat_of_nonneg hz_pos.le]; exact_mod_cast h2
  exact ⟨z.toNat, key.symm⟩

theorem irred_dim_dvd_card
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] [NeZero (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card]
  exact mainTheorem_dim_dvd_card_charZero ρ

noncomputable def wedderburnIrrep (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k)
    (i : Fin n) :
    Representation k G (Fin (d i) → k) :=
  ((Matrix.toLinAlgEquiv' (R := k) (n := Fin (d i))).toAlgHom.comp
    ((Pi.evalAlgHom k _ i).comp e.toAlgHom)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of k G)




end CharacterTheory
