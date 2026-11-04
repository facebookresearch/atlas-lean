/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
open Polynomial Finset Classical Finsupp Cardinal
universe u


lemma endomorphism_bijective_of_ne_zero
    {A : Type u} [Ring A] {M : Type u} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] (f : Module.End A M) (hf : f ≠ 0) :
    Function.Bijective f :=
  ⟨LinearMap.ker_eq_bot.mp ((IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker f)).resolve_right
      (fun h => hf (LinearMap.ext (fun x => LinearMap.mem_ker.mp (h ▸ Submodule.mem_top))))),
   LinearMap.range_eq_top.mp ((IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f)).resolve_left
      (fun h => hf (LinearMap.ext (fun x => by
        have : f x ∈ LinearMap.range f := ⟨x, rfl⟩
        rw [h] at this; exact (Submodule.mem_bot _).mp this))))⟩

instance endDivisionRing {A : Type u} [Ring A]
    {M : Type u} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] : DivisionRing (Module.End A M) :=
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  { (inferInstance : Ring (Module.End A M)) with
    inv := fun f => if h : f = 0 then 0 else
      (LinearEquiv.ofBijective f (endomorphism_bijective_of_ne_zero f h)).symm.toLinearMap
    inv_zero := by simp
    mul_inv_cancel := by
      intro f hf; simp only [dif_neg hf]; ext x
      show f ((LinearEquiv.ofBijective f (endomorphism_bijective_of_ne_zero f hf)).symm x) = x
      exact (LinearEquiv.ofBijective f _).apply_symm_apply x
    nnqsmul := _
    qsmul := _ }


lemma algebraic_in_range_of_algClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (D : Type u) [DivisionRing D] [Algebra k D]
    (x : D) (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k D) := by
  obtain ⟨p, hp_ne, hp_eval⟩ := hx
  suffices ∀ n, ∀ p : k[X], p ≠ 0 → p.natDegree ≤ n → aeval x p = 0 →
      x ∈ Set.range (algebraMap k D) from
    this p.natDegree p hp_ne le_rfl hp_eval
  intro n
  induction n with
  | zero =>
    intro p hp hd heval; exfalso
    rw [Nat.le_zero] at hd
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hd
    rw [hconst, aeval_C] at heval
    have hc : p.coeff 0 ≠ 0 := fun h => hp (by rw [hconst]; simp [h])
    rw [map_eq_zero_iff _ (algebraMap k D).injective] at heval
    exact hc heval
  | succ n ih =>
    intro p hp hd heval
    by_cases hd0 : p.natDegree = 0
    · exact ih p hp (by omega) heval
    · have hdeg : p.degree ≠ 0 := by
        intro h; apply hd0
        have := Polynomial.degree_eq_natDegree hp; rw [this] at h; exact_mod_cast h
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
      rw [← Polynomial.dvd_iff_isRoot] at ha; obtain ⟨q, hpq⟩ := ha
      have hq : q ≠ 0 := fun hq => hp (by rw [hpq, hq, mul_zero])
      have heval2 : (x - algebraMap k D a) * aeval x q = 0 := by
        rw [hpq] at heval
        simp only [map_mul, aeval_sub, aeval_X, aeval_C] at heval
        exact heval
      rcases mul_eq_zero.mp heval2 with h1 | h2
      · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
      · have hdeg_q : q.natDegree ≤ n := by
          have := natDegree_mul (X_sub_C_ne_zero a) hq
          rw [natDegree_X_sub_C] at this; rw [← hpq] at this; omega
        exact ih q hq hdeg_q h2


lemma x_sub_ne_zero_of_transcendental {k : Type u} [Field k]
    {D : Type u} [DivisionRing D] [Algebra k D]
    {x : D} (hx : Transcendental k x) (a : k) :
    x - algebraMap k D a ≠ 0 := by
  intro h; apply hx; exact ⟨X - C a, X_sub_C_ne_zero a, by simp [h]⟩

lemma linearIndependent_resolvent
    (k : Type u) [Field k] (D : Type u) [DivisionRing D] [Algebra k D]
    (x : D) (hx : Transcendental k x) :
    LinearIndependent k (fun a : k => (x - algebraMap k D a)⁻¹) := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hl_ne

  have hl_sum : ∑ a ∈ l.support, algebraMap k D (l a) * (x - algebraMap k D a)⁻¹ = 0 := by
    have := hl; simp only [linearCombination_apply, Finsupp.sum] at this
    rwa [Finset.sum_congr rfl (fun i _ => Algebra.smul_def (l i) _)] at this
  set S := l.support

  let Q := aeval x (∏ b ∈ S, (X - C b))
  have h0 : (∑ a ∈ S, algebraMap k D (l a) * (x - algebraMap k D a)⁻¹) * Q = 0 := by
    rw [hl_sum, zero_mul]
  rw [Finset.sum_mul] at h0

  have hP_eval : ∑ a ∈ S, algebraMap k D (l a) *
      aeval x (∏ b ∈ S.erase a, (X - C b)) = 0 := by
    convert h0 using 1; apply Finset.sum_congr rfl; intro a ha
    rw [mul_assoc]; congr 1; symm
    rw [show Q = aeval x (∏ b ∈ S, (X - C b)) from rfl,
        (Finset.mul_prod_erase S (fun b => X - C b) ha).symm,
        map_mul, aeval_sub, aeval_X, aeval_C,
        ← mul_assoc, inv_mul_cancel₀ (x_sub_ne_zero_of_transcendental hx a), one_mul]

  set P := ∑ a ∈ S, C (l a) * ∏ b ∈ S.erase a, (X - C b) with hP_def
  have haeval : aeval x P = 0 := by
    simp only [P, map_sum, map_mul, aeval_C]; exact hP_eval

  have hP_zero : P = 0 := by by_contra hP_ne; exact hx ⟨P, hP_ne, haeval⟩

  obtain ⟨a₀, ha₀⟩ := support_nonempty_iff.mpr hl_ne
  have hla₀ : l a₀ ≠ 0 := mem_support_iff.mp ha₀
  have heval : eval a₀ P = 0 := by rw [hP_zero]; simp
  rw [hP_def] at heval; simp only [eval_finset_sum, eval_mul, eval_C] at heval

  have hsum : (∑ a ∈ S, l a * eval a₀ (∏ b ∈ S.erase a, (X - C b))) =
      l a₀ * eval a₀ (∏ b ∈ S.erase a₀, (X - C b)) := by
    apply Finset.sum_eq_single a₀
    · intro b _ hba
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      exact mul_eq_zero_of_right _
        (Finset.prod_eq_zero (mem_erase.mpr ⟨hba.symm, ha₀⟩) (sub_self a₀))
    · intro h; exact absurd ha₀ h
  rw [hsum] at heval

  exact hla₀ ((mul_eq_zero.mp heval).resolve_right (by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr
      (fun b hb => sub_ne_zero.mpr (ne_of_mem_erase hb).symm)))


def evalAt {k : Type u} [CommSemiring k] (A : Type u) [Semiring A] [Algebra k A]
    {M : Type u} [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
    (v : M) : Module.End A M →ₗ[k] M where
  toFun T := T v
  map_add' _ _ := by simp
  map_smul' c T := by
    simp only [RingHom.id_apply]
    show (algebraMap k (Module.End A M) c * T) v = c • T v
    simp [Algebra.algebraMap_eq_smul_one]

lemma evalAt_injective {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] (v : M) (hv : v ≠ 0) :
    Function.Injective (evalAt (k := k) A v) := by
  intro T₁ T₂ h; simp only [evalAt] at h
  have hker : v ∈ LinearMap.ker (T₁ - T₂) := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h
  have hne : LinearMap.ker (T₁ - T₂) ≠ ⊥ := by
    intro hbot; apply hv; rwa [hbot, Submodule.mem_bot] at hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp
    ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hne))

def smulMap {k : Type u} [CommSemiring k] (A : Type u) [Semiring A] [Algebra k A]
    {M : Type u} [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
    (v : M) : A →ₗ[k] M where
  toFun a := a • v
  map_add' a b := add_smul a b v
  map_smul' c a := smul_assoc c a v

lemma smulMap_surjective {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] (v : M) (hv : v ≠ 0) :
    Function.Surjective (smulMap (k := k) A v) := by
  intro m
  have htop : Submodule.span A {v} = ⊤ := by
    exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (fun h => hv (by
      have : v ∈ Submodule.span A {v} := Submodule.subset_span (Set.mem_singleton v)
      rwa [h, Submodule.mem_bot] at this))
  have hm : m ∈ Submodule.span A {v} := htop ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨a, rfl⟩ := hm
  exact ⟨a, rfl⟩


theorem dixmier_lemma
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M]
    (hA : Module.rank k A ≤ ℵ₀)
    (hunc : ℵ₀ < #k) :
    Function.Bijective (algebraMap k (Module.End A M)) := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  constructor
  ·
    have : Nontrivial (Module.End A M) := by
      refine ⟨⟨0, 1, ?_⟩⟩; intro h
      obtain ⟨x, hx⟩ := exists_ne (0 : M); apply hx
      have := congr_fun (congr_arg DFunLike.coe h) x; simpa using this.symm
    exact (algebraMap k (Module.End A M)).injective
  ·
    intro T
    by_contra hT

    have hT_not_alg : ¬ IsAlgebraic k T := by
      intro halg
      exact hT (algebraic_in_range_of_algClosed k (Module.End A M) T halg)

    have hT_trans : Transcendental k T := hT_not_alg

    have hli := linearIndependent_resolvent k (Module.End A M) T hT_trans
    have hcard : #k ≤ Module.rank k (Module.End A M) := hli.cardinal_le_rank

    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    have h1 : Module.rank k (Module.End A M) ≤ Module.rank k M :=
      LinearMap.rank_le_of_injective (evalAt A v) (evalAt_injective A v hv)
    have h2 : Module.rank k M ≤ Module.rank k A :=
      LinearMap.rank_le_of_surjective (smulMap A v) (smulMap_surjective A v hv)

    exact not_le.mpr hunc (le_trans hcard (le_trans h1 (le_trans h2 hA)))


def centerToEnd {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Subalgebra.center k A →ₐ[k] Module.End A M where
  toFun z :=
    { toFun := fun m => (z : A) • m
      map_add' := fun m₁ m₂ => smul_add (z : A) m₁ m₂
      map_smul' := fun c m => by
        have hz := z.2
        simp only [Subalgebra.mem_center_iff] at hz
        show (↑z : A) • (c • m) = c • ((↑z : A) • m)
        rw [← mul_smul, ← mul_smul, hz c] }
  map_one' := by ext m; show (1 : A) • m = m; exact one_smul A m
  map_mul' z₁ z₂ := by
    ext m; show ((z₁ : A) * (z₂ : A)) • m = (z₁ : A) • ((z₂ : A) • m)
    exact mul_smul (z₁ : A) (z₂ : A) m
  map_zero' := by ext m; show (0 : A) • m = 0; exact zero_smul A m
  map_add' z₁ z₂ := by
    ext m; show ((z₁ : A) + (z₂ : A)) • m = (z₁ : A) • m + (z₂ : A) • m
    exact add_smul (z₁ : A) (z₂ : A) m
  commutes' c := by
    ext m
    change (algebraMap k A c) • m = (algebraMap k (Module.End A M) c) m
    conv_rhs => rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
    exact algebraMap_smul A c m

def centerCharacter {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (hbij : Function.Bijective (algebraMap k (Module.End A M))) :
    Subalgebra.center k A →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A M)) hbij).symm.toAlgHom.comp
    (centerToEnd A)

theorem center_acts_by_character
    {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (hbij : Function.Bijective (algebraMap k (Module.End A M)))
    (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centerCharacter A hbij z • m := by
  have key : algebraMap k (Module.End A M) (centerCharacter A hbij z) =
      centerToEnd A z := by
    simp only [centerCharacter, AlgHom.comp_apply]
    exact (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A M)) hbij).apply_symm_apply
      (centerToEnd A z)
  have h1 : (centerToEnd A z) m = (z : A) • m := rfl
  have h2 : (algebraMap k (Module.End A M) (centerCharacter A hbij z)) m =
      centerCharacter A hbij z • m := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← h1, ← h2, key]

theorem dixmier_lemma_center_character
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M]
    (hA : Module.rank k A ≤ ℵ₀)
    (hunc : ℵ₀ < #k) :
    ∃ χ : Subalgebra.center k A →ₐ[k] k,
      ∀ (z : Subalgebra.center k A) (m : M), (z : A) • m = χ z • m := by
  have hbij := dixmier_lemma k A M hA hunc
  exact ⟨centerCharacter A hbij, center_acts_by_character A hbij⟩

end
