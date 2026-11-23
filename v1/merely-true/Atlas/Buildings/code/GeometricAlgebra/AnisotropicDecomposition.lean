/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000

namespace Garrett

variable {F : Type*} [Field F]


/-- A bilinear form `B` is anisotropic when every isotropic vector (one with
`B x x = 0`) is zero. -/
def BilinForm.IsAnisotropic {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) : Prop :=
  ∀ x : V, B x x = 0 → x = 0

/-- A subspace `H` is hyperbolic for `B` iff it is spanned by `n` mutually orthogonal
hyperbolic pairs `(vs i, ws i)` with `B (vs i) (ws i) = 1` and all self-pairings and
cross-pairings between distinct pairs vanishing. -/
def BilinForm.IsHyperbolicSubspace {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (H : Submodule F V) : Prop :=
  ∃ (n : ℕ) (vs ws : Fin n → V),
    (∀ i, vs i ∈ H) ∧ (∀ i, ws i ∈ H) ∧
    (∀ i, B (vs i) (vs i) = 0) ∧
    (∀ i, B (ws i) (ws i) = 0) ∧
    (∀ i, B (vs i) (ws i) = 1) ∧
    (∀ i j, i ≠ j → B (vs i) (vs j) = 0) ∧
    (∀ i j, i ≠ j → B (ws i) (ws j) = 0) ∧
    (∀ i j, i ≠ j → B (vs i) (ws j) = 0) ∧
    H = Submodule.span F (Set.range vs ∪ Set.range ws)


/-- Given a nondegenerate symmetric form (with `2` invertible) and a nonzero isotropic
vector `v`, there exists `w` forming a hyperbolic pair with `v`: `B v w = B w v = 1`
and `B w w = 0`. -/
lemma exists_hyperbolic_pair_of_isotropic
    {V : Type*} [AddCommGroup V] [Module F V]
    [Invertible (2 : F)]
    (B : LinearMap.BilinForm F V)
    (hBnd : B.Nondegenerate)
    (hBsymm : B.IsSymm)
    (v : V) (hv : v ≠ 0) (hiso : B v v = 0) :
    ∃ w : V, B v w = 1 ∧ B w w = 0 ∧ B w v = 1 := by

  have ⟨y, hy⟩ : ∃ y, B v y ≠ 0 := by
    by_contra hall; push Not at hall; exact hv (hBnd.1 v hall)

  set y' := (B v y)⁻¹ • y
  have hvy' : B v y' = 1 := by
    simp only [y', map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hy
  have hy'v : B y' v = 1 := by rw [hBsymm.eq y' v]; exact hvy'

  set c := ⅟(2 : F) * B y' y'
  set w := y' - c • v

  have hvw : B v w = 1 := by
    show B v (y' - c • v) = 1
    simp only [map_sub, map_smul, smul_eq_mul, hvy', hiso, mul_zero, sub_zero]
  have hwv : B w v = 1 := by rw [hBsymm.eq]; exact hvw
  have hww : B w w = 0 := by
    show B (y' - c • v) (y' - c • v) = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
               hiso, hy'v, hvy', mul_one, mul_zero, sub_zero, c]
    have : ⅟(2 : F) * B y' y' + ⅟(2 : F) * B y' y' = B y' y' := by
      rw [← add_mul, ← two_mul, mul_invOf_self, one_mul]
    linear_combination -this
  exact ⟨w, hvw, hww, hwv⟩

/-- If a reflexive nondegenerate form `B` restricts nondegenerately to a subspace `P`,
then it also restricts nondegenerately to the orthogonal complement of `P`. -/
lemma restrict_orthogonal_nondegenerate
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hBnd : B.Nondegenerate) (hBrefl : B.IsRefl)
    (P : Submodule F V) (hP : (B.restrict P).Nondegenerate) :
    (B.restrict (B.orthogonal P)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl]
  rw [LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl P]
  exact (B.isCompl_orthogonal_of_restrict_nondegenerate hBrefl hP).symm

/-- Restriction of a symmetric bilinear form to a subspace remains symmetric. -/
lemma restrict_isSymm {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (hBsymm : B.IsSymm) (W : Submodule F V) :
    (B.restrict W).IsSymm := by
  constructor; intro ⟨x, _⟩ ⟨y, _⟩
  simp only [LinearMap.BilinForm.restrict_apply]; exact hBsymm.eq x y

/-- The restriction of any bilinear form to `⊥` is vacuously nondegenerate. -/
lemma restrict_bot_nondegenerate {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) : (B.restrict (⊥ : Submodule F V)).Nondegenerate := by
  constructor <;> intro ⟨m, hm⟩ _ <;>
    simp only [Submodule.mem_bot] at hm <;> exact Subtype.ext hm

/-- The orthogonal complement of the trivial subspace `⊥` is the whole space `⊤`. -/
lemma orthogonal_bot {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) : B.orthogonal ⊥ = ⊤ := by
  ext x; simp

/-- If `B` is anisotropic on all of `V`, then its restriction to `⊤` is also
anisotropic. -/
lemma restrict_top_anisotropic {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (hB : BilinForm.IsAnisotropic B) :
    BilinForm.IsAnisotropic (B.restrict (⊤ : Submodule F V)) := by
  intro ⟨x, _⟩ hx
  simp only [LinearMap.BilinForm.restrict_apply] at hx
  exact Subtype.ext (hB x hx)

/-- Compatibility of orthogonal complements with the lift `Pperp.subtype`: the
orthogonal of `P ⊔ (H' lifted to V)` equals the lift of `(B|Pperp).orthogonal H'`. -/
lemma orthogonal_sup_map_eq {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V)
    (P Pperp : Submodule F V) (hPperp : Pperp = B.orthogonal P)
    (H' : Submodule F ↥Pperp) :
    B.orthogonal (P ⊔ H'.map Pperp.subtype) =
    ((B.restrict Pperp).orthogonal H').map Pperp.subtype := by
  ext x; constructor
  · intro hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    have hxP : x ∈ Pperp := by
      rw [hPperp, LinearMap.BilinForm.mem_orthogonal_iff]
      intro p hp; exact hx p (Submodule.mem_sup_left hp)
    exact Submodule.mem_map.mpr ⟨⟨x, hxP⟩, by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro ⟨h', _⟩ hh'H
      exact hx h' (Submodule.mem_sup_right (Submodule.mem_map_of_mem hh'H)), rfl⟩
  · intro hx
    obtain ⟨⟨x', hx'P⟩, hx'H, rfl⟩ := Submodule.mem_map.mp hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
    show B (p + q) x' = 0
    rw [map_add, LinearMap.add_apply,
        show B p x' = 0 from by rw [hPperp] at hx'P; exact hx'P p hp,
        show B q x' = 0 from by
          obtain ⟨q', hq'H, rfl⟩ := Submodule.mem_map.mp hq
          exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx'H) q' hq'H,
        add_zero]

/-- Lifting complements through a complement: if `P ⊕ Pperp = V` and `H' ⊕ A' = Pperp`,
then `(P ⊔ H'.map Pperp.subtype) ⊕ (A'.map Pperp.subtype) = V`. -/
lemma isCompl_lift_submodule {V : Type*} [AddCommGroup V] [Module F V]
    (P Pperp : Submodule F V) (hCompl : IsCompl P Pperp)
    (H' A' : Submodule F ↥Pperp) (hHA : IsCompl H' A') :
    IsCompl (P ⊔ H'.map Pperp.subtype) (A'.map Pperp.subtype) := by
  constructor
  ·
    rw [disjoint_iff]; ext x
    simp only [Submodule.mem_inf, Submodule.mem_bot]; constructor
    · intro ⟨hx_sup, hx_A⟩
      have hxPperp : x ∈ Pperp := by
        obtain ⟨a, _, rfl⟩ := Submodule.mem_map.mp hx_A; exact a.2
      obtain ⟨p, hp, h', hh', rfl⟩ := Submodule.mem_sup.mp hx_sup
      have hh'Pperp : h' ∈ Pperp := by
        obtain ⟨h'', _, rfl⟩ := Submodule.mem_map.mp hh'; exact h''.2
      have hp0 : p = 0 := by
        have hpPperp : p ∈ Pperp := by
          have hsub : p = (p + h') - h' := by abel
          rw [hsub]; exact Pperp.sub_mem hxPperp hh'Pperp
        have : p ∈ P ⊓ Pperp := Submodule.mem_inf.mpr ⟨hp, hpPperp⟩
        rwa [hCompl.inf_eq_bot, Submodule.mem_bot] at this
      rw [hp0, zero_add]; rw [hp0, zero_add] at hx_A
      obtain ⟨h'', hh''H, rfl⟩ := Submodule.mem_map.mp hh'
      obtain ⟨a', ha'A, ha'eq⟩ := Submodule.mem_map.mp hx_A
      have : h'' ∈ H' ⊓ A' := Submodule.mem_inf.mpr ⟨hh''H,
        (Subtype.val_injective ha'eq.symm : h'' = a') ▸ ha'A⟩
      rw [hHA.inf_eq_bot, Submodule.mem_bot] at this; simp [this]
    · intro h; simp [h]
  ·
    rw [codisjoint_iff, sup_assoc,
        show H'.map Pperp.subtype ⊔ A'.map Pperp.subtype = Pperp from by
          rw [← Submodule.map_sup, hHA.sup_eq_top]
          simp [Submodule.map_top, Submodule.range_subtype]]
    exact hCompl.sup_eq_top

/-- Anisotropy transfers through the lift `W.subtype`: if `(B|W)|A` is anisotropic,
then `B` restricted to the lifted subspace `A.map W.subtype` is anisotropic. -/
lemma isAnisotropic_restrict_map {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (W : Submodule F V) (A : Submodule F ↥W)
    (hA : BilinForm.IsAnisotropic ((B.restrict W).restrict A)) :
    BilinForm.IsAnisotropic (B.restrict (A.map W.subtype)) := by
  intro ⟨x, hx⟩ hBx
  obtain ⟨⟨a, haW⟩, haA, rfl⟩ := Submodule.mem_map.mp hx
  have h := hA ⟨⟨a, haW⟩, haA⟩ hBx
  simp only [Subtype.ext_iff] at h; exact Subtype.ext h


/-- Garrett's Chapter 7 Corollary: every finite-dimensional nondegenerate symmetric
formed space decomposes as `H ⊕ A` where `H` is hyperbolic, `A = H⊥`, and the
restriction of `B` to `A` is anisotropic. Proved by strong induction on
`Module.finrank F V`. -/
theorem garrett_7_2_corollary
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Invertible (2 : F)]
    (B : LinearMap.BilinForm F V)
    (hBnd : B.Nondegenerate)
    (hBsymm : B.IsSymm) :
    ∃ (H A : Submodule F V),
      BilinForm.IsHyperbolicSubspace B H ∧
      BilinForm.IsAnisotropic (B.restrict A) ∧
      IsCompl H A ∧
      A = B.orthogonal H := by

  induction hn : Module.finrank F V using Nat.strongRecOn generalizing V with
  | _ n ih =>

  by_cases hAniso : BilinForm.IsAnisotropic B
  · refine ⟨⊥, B.orthogonal ⊥, ?_, ?_, ?_, rfl⟩

    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        by simp [Set.range_eq_empty]⟩

    · rw [orthogonal_bot]; exact restrict_top_anisotropic B hAniso

    · rw [orthogonal_bot]; exact isCompl_bot_top

  · simp only [BilinForm.IsAnisotropic, not_forall] at hAniso
    obtain ⟨v, hiso, hv⟩ := hAniso

    obtain ⟨w, hvw, hww, hwv⟩ := exists_hyperbolic_pair_of_isotropic B hBnd hBsymm v hv hiso

    set P := Submodule.span F {v, w} with hP_def

    have hPnd : (B.restrict P).Nondegenerate := by
      rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm.isRefl]
      rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hBsymm.isRefl]
      rw [disjoint_iff]
      ext x
      constructor
      · intro hx
        obtain ⟨hxP, hxPerp⟩ := Submodule.mem_inf.mp hx
        have hxv : B x v = 0 := by
          have hv_mem : v ∈ P := Submodule.subset_span (Set.mem_insert v {w})
          have h := hxPerp v hv_mem
          exact hBsymm.eq v x ▸ h
        have hxw : B x w = 0 := by
          have hw_mem : w ∈ P := Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
          have h := hxPerp w hw_mem
          exact hBsymm.eq w x ▸ h
        rw [Submodule.mem_span_insert] at hxP
        obtain ⟨a, z, hz, hxeq⟩ := hxP
        rw [Submodule.mem_span_singleton] at hz; obtain ⟨b, rfl⟩ := hz
        rw [show x = a • v + b • w from hxeq] at hxv hxw
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          at hxv hxw
        rw [hiso, hwv, mul_zero, zero_add, mul_one] at hxv
        rw [hvw, hww, mul_one, mul_zero, add_zero] at hxw
        rw [hxeq, hxv, hxw, zero_smul, zero_smul, add_zero]
        exact Submodule.zero_mem _
      · intro hx
        rw [(Submodule.mem_bot F).mp hx]
        exact Submodule.zero_mem _

    have hCompl : IsCompl P (B.orthogonal P) :=
      B.isCompl_orthogonal_of_restrict_nondegenerate hBsymm.isRefl hPnd

    have hPerpNd : (B.restrict (B.orthogonal P)).Nondegenerate :=
      restrict_orthogonal_nondegenerate B hBnd hBsymm.isRefl P hPnd

    have hPerpRank : Module.finrank F ↥(B.orthogonal P) < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro h
      rw [h] at hCompl
      have := hCompl.inf_eq_bot
      simp only [inf_top_eq] at this
      have hv_mem : v ∈ P := Submodule.subset_span (Set.mem_insert v {w})
      rw [this] at hv_mem
      exact hv ((Submodule.mem_bot F).mp hv_mem)

    set Pperp := B.orthogonal P
    have hPerpSymm := restrict_isSymm B hBsymm Pperp
    obtain ⟨H', A'_ih, hH'hyp, hH'aniso, hH'A'compl, hA'eq⟩ :=
      ih _ hPerpRank (B.restrict Pperp) hPerpNd hPerpSymm rfl

    set H'V := H'.map Pperp.subtype
    set H := P ⊔ H'V
    set A' := (B.restrict Pperp).orthogonal H'

    have hA'_ih_eq : A'_ih = A' := hA'eq

    have hOrthH : B.orthogonal H = A'.map Pperp.subtype :=
      orthogonal_sup_map_eq B P Pperp rfl H'

    have hHA : IsCompl H' A' := hA'_ih_eq ▸ hH'A'compl

    have hHCompl : IsCompl H (B.orthogonal H) := by
      rw [hOrthH]
      exact isCompl_lift_submodule P Pperp hCompl H' A' hHA

    have hHhyp : BilinForm.IsHyperbolicSubspace B H := by
      obtain ⟨m, vs', ws', hvs'H, hws'H, hvs'iso, hws'iso, hvw'pair,
        hvv'orth, hww'orth, hvw'orth, hH'span⟩ := hH'hyp

      let vs0 : Fin m → V := fun i => (vs' i : V)
      let ws0 : Fin m → V := fun i => (ws' i : V)

      refine ⟨m + 1, Fin.cons v vs0, Fin.cons w ws0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert v {w}))
        · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (hvs'H j))

      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (hws'H j))

      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hiso
        · exact hvs'iso j

      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hww
        · exact hws'iso j

      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hvw
        · exact hvw'pair j

      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (vs' b).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · rw [hBsymm.eq]; exact (vs' a).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · exact hvv'orth a b (fun h => hij (congrArg Fin.succ h))

      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (ws' b).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · rw [hBsymm.eq]; exact (ws' a).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact hww'orth a b (fun h => hij (congrArg Fin.succ h))

      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (ws' b).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · rw [hBsymm.eq]; exact (vs' a).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact hvw'orth a b (fun h => hij (congrArg Fin.succ h))

      · have hvs0_range : Set.range vs0 = Pperp.subtype '' Set.range vs' := by
          ext x; simp [vs0, Set.mem_range, Set.mem_image]
        have hws0_range : Set.range ws0 = Pperp.subtype '' Set.range ws' := by
          ext x; simp [ws0, Set.mem_range, Set.mem_image]
        rw [show H = P ⊔ H'V from rfl]
        rw [show H'V = H'.map Pperp.subtype from rfl]
        rw [hH'span, Submodule.map_span]
        simp only [Fin.range_cons, Set.image_union]
        rw [← hvs0_range, ← hws0_range]
        rw [show P = Submodule.span F {v, w} from rfl]
        rw [← Submodule.span_union]
        congr 1
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
        tauto

    exact ⟨H, B.orthogonal H, hHhyp,
      by rw [hOrthH]; exact isAnisotropic_restrict_map B Pperp A' (hA'_ih_eq ▸ hH'aniso),
      hHCompl, rfl⟩

end Garrett
