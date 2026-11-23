/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Atlas.Buildings.code.GeometricAlgebra.BilinFormComplementation

set_option maxHeartbeats 0

namespace Formalization.GeometricAlgebra

open LinearMap.BilinForm

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The radical of a subspace `W` for the bilinear form `B`: the part of `W`
that is orthogonal to all of `W`. -/
def SubspaceRadical (B : LinearMap.BilinForm k V) (W : Submodule k V) : Submodule k V :=
  W ⊓ orthogonal B W

set_option linter.unusedSectionVars false in
/-- Given a chain `p ≤ q` of subspaces in a finite-dimensional space, there
exists a complementary subspace `r ≤ q` to `p` within `q`. -/
lemma exists_complement_within (p q : Submodule k V) (h : p ≤ q) :
    ∃ (r : Submodule k V), r ≤ q ∧ Disjoint p r ∧ p ⊔ r = q := by
  set p' := Submodule.comap q.subtype p
  obtain ⟨r', hr'⟩ := Submodule.exists_isCompl p'
  set r := Submodule.map q.subtype r'
  refine ⟨r, Submodule.map_subtype_le q r', ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxp hxr
    obtain ⟨⟨y, hy_mem⟩, hy_r', hy_eq⟩ := Submodule.mem_map.mp hxr
    simp at hy_eq; subst hy_eq
    have hyp' : (⟨y, hy_mem⟩ : ↥q) ∈ p' := Submodule.mem_comap.mpr (by simp; exact hxp)
    have hbot := hr'.disjoint.eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    have := hbot ⟨y, hy_mem⟩ (Submodule.mem_inf.mpr ⟨hyp', hy_r'⟩)
    exact congr_arg Subtype.val this
  · ext x; constructor
    · intro hx
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
      rw [← hab]; exact q.add_mem (h ha) (Submodule.map_subtype_le q r' hb)
    · intro hx
      have hx' : (⟨x, hx⟩ : ↥q) ∈ p' ⊔ r' := hr'.sup_eq_top ▸ Submodule.mem_top
      rcases Submodule.mem_sup.mp hx' with ⟨a, ha, b, hb, hab⟩
      have hab' : x = ↑a + ↑b := by
        have := congr_arg Subtype.val hab; simp at this; exact this.symm
      rw [hab']; apply Submodule.mem_sup.mpr
      exact ⟨a.1, Submodule.mem_comap.mp ha, b.1, Submodule.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩

set_option linter.unusedSectionVars false in
/-- If `W₁` is a complement to the radical `W ⊓ Wᗮ` inside `W`, then the
restriction of `B` to `W₁` is nondegenerate. -/
lemma restrict_complement_of_radical_nondegenerate
    (B : LinearMap.BilinForm k V) (hBr : B.IsRefl)
    (W W₁ : Submodule k V)
    (hW₁_le : W₁ ≤ W)
    (hDisj : Disjoint (W ⊓ orthogonal B W) W₁)
    (hSup : (W ⊓ orthogonal B W) ⊔ W₁ = W) :
    (restrict B W₁).Nondegenerate := by
  constructor
  ·
    intro ⟨x, hx_mem⟩ hx
    suffices hx_rad : (x : V) ∈ W ⊓ orthogonal B W by
      exact Subtype.ext (Submodule.disjoint_def.mp hDisj x hx_rad hx_mem)
    refine Submodule.mem_inf.mpr ⟨hW₁_le hx_mem, ?_⟩
    intro n hn
    rw [← hSup] at hn
    rcases Submodule.mem_sup.mp hn with ⟨a, ha, b, hb, hab⟩
    rw [← hab]; show (B (a + b)) x = 0
    rw [map_add, LinearMap.add_apply]
    have hBxa : (B x) a = 0 := (Submodule.mem_inf.mp ha).2 x (hW₁_le hx_mem)
    have hBax : (B a) x = 0 := hBr.eq_zero hBxa
    have hBxb : (B x) b = 0 := hx ⟨b, hb⟩
    have hBbx : (B b) x = 0 := hBr.eq_zero hBxb
    rw [hBax, hBbx, add_zero]
  ·
    intro ⟨y, hy_mem⟩ hy
    suffices hy_rad : (y : V) ∈ W ⊓ orthogonal B W by
      exact Subtype.ext (Submodule.disjoint_def.mp hDisj y hy_rad hy_mem)
    refine Submodule.mem_inf.mpr ⟨hW₁_le hy_mem, ?_⟩
    intro n hn
    rw [← hSup] at hn
    rcases Submodule.mem_sup.mp hn with ⟨a, ha, b, hb, hab⟩
    rw [← hab]; show (B (a + b)) y = 0
    rw [map_add, LinearMap.add_apply]
    have hBya : (B y) a = 0 := (Submodule.mem_inf.mp ha).2 y (hW₁_le hy_mem)
    have hBay : (B a) y = 0 := hBr.eq_zero hBya
    have hBby : (B b) y = 0 := hy ⟨b, hb⟩
    rw [hBay, hBby, add_zero]

/-- A hyperbolic pair for `B` consists of two isotropic vectors `x, y` with
`B x y = 1`. -/
def IsHyperbolicPair (B : LinearMap.BilinForm k V) (x y : V) : Prop :=
  B x x = 0 ∧ B y y = 0 ∧ B x y = 1

set_option linter.unusedSectionVars false in
/-- For a nondegenerate bilinear form `B`, every nonzero vector `x` has some
`z` with `B x z = 1`. -/
theorem exists_eval_one
    (B : LinearMap.BilinForm k V) (hBnd : B.Nondegenerate)
    (x : V) (hx_ne : x ≠ 0) :
    ∃ z : V, B x z = 1 := by
  have ⟨w, hw⟩ : ∃ w, B x w ≠ 0 := by
    by_contra h; push Not at h; exact hx_ne (hBnd.1 x h)
  exact ⟨(B x w)⁻¹ • w, by simp [smul_eq_mul, mul_comm, mul_inv_cancel₀ hw]⟩

set_option linter.unusedSectionVars false in
/-- Adjust a vector `z` with `B x z = 1` to obtain a hyperbolic pair partner for
the isotropic `x` (subtract off the right multiple of `x` to make `z` isotropic). -/
theorem isotropic_adjustment
    (B : LinearMap.BilinForm k V) (hBs : B.IsSymm)
    (x z : V) (hx_iso : B x x = 0) (hxz : B x z = 1) :
    IsHyperbolicPair B x (z - (⅟(2 : k) * (B z z)) • x) := by
  have hzx : (B z) x = 1 := by rw [← hBs.eq x z]; exact hxz
  refine ⟨hx_iso, ?_, ?_⟩
  ·
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
    rw [hxz, hzx, hx_iso, smul_zero, sub_zero, smul_eq_mul, mul_one, sub_sub]
    rw [show ⅟(2 : k) * (B z z) + ⅟(2 : k) * (B z z) = (B z z) from
      by rw [← add_mul, ← two_mul, mul_invOf_self, one_mul]]
    exact sub_self _
  ·
    simp only [map_sub, map_smul]
    rw [hx_iso, smul_zero, sub_zero]; exact hxz

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
/-- Given a vector `x₀` in the radical of `W` together with a basis-tail
condition, produce a hyperbolic partner `y₀` to `x₀` orthogonal to the tail of
the basis. -/
theorem hyperbolic_pair_from_radical_with_tail_orth
    (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm)
    (W W₁ : Submodule k V)
    (hW₁_le : W₁ ≤ W)
    (_hSup : SubspaceRadical B W ⊔ W₁ = W)
    (hW₁_nd : (restrict B W₁).Nondegenerate)
    {n : ℕ}
    (bW₀ : Module.Basis (Fin (n + 1)) k (SubspaceRadical B W)) :
    ∃ y₀ : V, y₀ ∈ orthogonal B W₁ ∧
      IsHyperbolicPair B (bW₀ 0 : V) y₀ ∧
      ∀ j : Fin n, B (bW₀ j.succ : V) y₀ = 0 := by
  have hBr : B.IsRefl := hBs.isRefl
  set x₀ := (bW₀ 0 : V) with hx₀_def

  have hx₀_rad := (bW₀ 0).prop
  have hx₀_W : x₀ ∈ W := (Submodule.mem_inf.mp hx₀_rad).1
  have hx₀_orth : x₀ ∈ orthogonal B W := (Submodule.mem_inf.mp hx₀_rad).2
  have hx₀_iso : B x₀ x₀ = 0 := hx₀_orth x₀ hx₀_W
  have hx₀_orthW₁ : x₀ ∈ orthogonal B W₁ := orthogonal_le hW₁_le hx₀_orth

  have htail_orth : ∀ j : Fin n, (bW₀ j.succ : V) ∈ orthogonal B W :=
    fun j => (Submodule.mem_inf.mp (bW₀ j.succ).prop).2

  set T := Submodule.span k (Set.range (fun j : Fin n => (bW₀ j.succ : V))) with hT_def
  have hx₀_notT : x₀ ∉ T := by
    have hli : LinearIndependent k (fun i : Fin (n + 1) => (bW₀ i : V)) :=
      bW₀.linearIndependent.map' (SubspaceRadical B W).subtype (Submodule.ker_subtype _)
    show x₀ ∉ Submodule.span k (Set.range (fun j : Fin n => (bW₀ j.succ : V)))
    rw [show Set.range (fun j : Fin n => (bW₀ j.succ : V)) =
      (fun i : Fin (n + 1) => (bW₀ i : V)) '' (Set.range Fin.succ) from by
        ext v; simp only [Set.mem_range, Set.mem_image]; constructor
        · rintro ⟨j, rfl⟩; exact ⟨j.succ, ⟨j, rfl⟩, rfl⟩
        · rintro ⟨i, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩]
    exact hli.notMem_span_image
      (by simp only [Set.mem_range, not_exists]; exact fun j => Fin.succ_ne_zero j)

  obtain ⟨z, hz_orth_T, hz_ne⟩ : ∃ z ∈ orthogonal B T, B x₀ z ≠ 0 := by
    rw [← orthogonal_orthogonal hB hBr T] at hx₀_notT
    by_contra h; push Not at h
    exact hx₀_notT (fun m hm => hBr.eq_zero (h m hm))

  have hz_tail : ∀ j : Fin n, B (bW₀ j.succ : V) z = 0 :=
    fun j => hz_orth_T _ (Submodule.subset_span ⟨j, rfl⟩)

  have hIsCompl : IsCompl W₁ (orthogonal B W₁) :=
    B.isCompl_orthogonal_of_restrict_nondegenerate hBr hW₁_nd
  obtain ⟨w₁, hw₁, o, ho, hzo⟩ := Submodule.mem_sup.mp
    (hIsCompl.sup_eq_top ▸ (Submodule.mem_top : z ∈ ⊤))

  have hBxw₁ : (B x₀) w₁ = 0 := hBr.eq_zero (hx₀_orth w₁ (hW₁_le hw₁))

  have hBxo : (B x₀) o ≠ 0 := by
    intro heq; apply hz_ne
    calc (B x₀) z = (B x₀) (w₁ + o) := by rw [hzo]
      _ = (B x₀) w₁ + (B x₀) o := map_add ..
      _ = 0 + 0 := by rw [hBxw₁, heq]
      _ = 0 := add_zero 0

  have htail_o : ∀ j : Fin n, B (bW₀ j.succ : V) o = 0 := by
    intro j
    have ho_eq : o = z - w₁ := eq_sub_of_add_eq' hzo
    rw [ho_eq, map_sub, hz_tail j, hBr.eq_zero (htail_orth j w₁ (hW₁_le hw₁)), sub_self]

  have htail_x₀ : ∀ j : Fin n, B (bW₀ j.succ : V) x₀ = 0 :=
    fun j => hBr.eq_zero (htail_orth j x₀ hx₀_W)

  set α := (B x₀) o with hα_def
  set h' := α⁻¹ • o with hh'_def
  have hBxh' : (B x₀) h' = 1 := by
    show (B x₀) (α⁻¹ • o) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hBxo]
  have hh'_orth : h' ∈ orthogonal B W₁ := (orthogonal B W₁).smul_mem α⁻¹ ho

  set c := ⅟(2 : k) * ((B h') h') with hc_def
  set y₀ := h' - c • x₀ with hy₀_def

  have hy₀_orth : y₀ ∈ orthogonal B W₁ :=
    (orthogonal B W₁).sub_mem hh'_orth ((orthogonal B W₁).smul_mem c hx₀_orthW₁)

  have hp := isotropic_adjustment B hBs x₀ h' hx₀_iso hBxh'

  have htail_y₀ : ∀ j : Fin n, B (bW₀ j.succ : V) y₀ = 0 := by
    intro j
    simp only [hy₀_def, hh'_def, map_sub, map_smul,
      htail_o j, smul_zero, htail_x₀ j, sub_self]
  exact ⟨y₀, hy₀_orth, hp, htail_y₀⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
/-- Adjoining a hyperbolic partner `y₀` (for the first basis vector of the
radical of `W`) to `W` reduces the dimension of the radical by one. -/
lemma radical_shrinks_after_hyperbolic_extension
    (B : LinearMap.BilinForm k V) (hBs : B.IsSymm)
    (W : Submodule k V)
    {n : ℕ}
    (bW₀ : Module.Basis (Fin (n + 1)) k (SubspaceRadical B W))
    (y₀ : V)
    (hBy₀ : B (bW₀ 0 : V) y₀ = 1)
    (hBy₀_tail : ∀ j : Fin n, B (bW₀ j.succ : V) y₀ = 0) :
    ∃ bW₀' : Module.Basis (Fin n) k (SubspaceRadical B (W ⊔ Submodule.span k {y₀})),
      ∀ j : Fin n, (bW₀' j : V) = (bW₀ j.succ : V) := by
  set W' := W ⊔ Submodule.span k {y₀}
  set W₀' := SubspaceRadical B W'

  have hv_mem : ∀ j : Fin n, (bW₀ j.succ : V) ∈ W₀' := by
    intro j
    refine ⟨Submodule.mem_sup_left (bW₀ j.succ).prop.1, fun z hz => ?_⟩
    rw [Submodule.mem_sup] at hz
    obtain ⟨w, hw, s, hs, rfl⟩ := hz
    rw [Submodule.mem_span_singleton] at hs
    obtain ⟨c, rfl⟩ := hs
    show B (w + c • y₀) (bW₀ j.succ : V) = 0
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        (bW₀ j.succ).prop.2 w hw, smul_eq_mul, hBs.eq y₀ (bW₀ j.succ : V), hBy₀_tail j,
        mul_zero, add_zero]
  let v : Fin n → W₀' := fun j => ⟨(bW₀ j.succ : V), hv_mem j⟩

  have hv_li : LinearIndependent k v := by
    apply LinearIndependent.of_comp W₀'.subtype
    show LinearIndependent k (W₀'.subtype ∘ v)
    have : W₀'.subtype ∘ v = (SubspaceRadical B W).subtype ∘ bW₀ ∘ Fin.succ := by
      ext j; simp [v]
    rw [this]
    exact (bW₀.linearIndependent.comp _ (Fin.succ_injective n)).map'
      (SubspaceRadical B W).subtype (Submodule.ker_subtype _)

  have hv_span : ⊤ ≤ Submodule.span k (Set.range v) := by
    intro ⟨x, hx_mem⟩ _
    have hx_orth : ∀ z ∈ W', B z x = 0 := hx_mem.2
    obtain ⟨w, hw, s, hs, hx_eq⟩ := Submodule.mem_sup.mp hx_mem.1
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs

    have hc_eq_zero : c = 0 := by
      have h0 : (B (bW₀ 0 : V)) (w + c • y₀) = 0 :=
        hx_eq ▸ hx_orth _ (Submodule.mem_sup_left (bW₀ 0).prop.1)
      have h1 : (B (bW₀ 0 : V)) w = 0 := by
        rw [hBs.eq (↑(bW₀ 0) : V) w]; exact (bW₀ 0).prop.2 w hw
      have h2 : (B (bW₀ 0 : V)) (c • y₀) = c := by
        rw [LinearMap.map_smul, hBy₀, smul_eq_mul, mul_one]
      rw [map_add, h1, h2, zero_add] at h0; exact h0
    rw [hc_eq_zero, zero_smul, add_zero] at hx_eq

    have hx_rad : x ∈ SubspaceRadical B W := by
      subst hx_eq
      exact ⟨hw, fun z hz => hx_orth z (Submodule.mem_sup_left hz)⟩
    set x' : SubspaceRadical B W := ⟨x, hx_rad⟩

    have hx_sum : x = ∑ i, (bW₀.repr x') i • (bW₀ i : V) := by
      have h := congr_arg Subtype.val (bW₀.sum_repr x').symm
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h

    have hBy₀_x : B y₀ x = 0 :=
      hx_orth y₀ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀))
    rw [hx_sum, map_sum, Fin.sum_univ_succ] at hBy₀_x
    simp only [map_smul, smul_eq_mul] at hBy₀_x
    rw [hBs.eq y₀ (bW₀ 0 : V), hBy₀, mul_one] at hBy₀_x
    have h_tail : ∑ i : Fin n, (bW₀.repr x') i.succ * B y₀ (bW₀ i.succ : V) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hBs.eq y₀ (bW₀ j.succ : V), hBy₀_tail j, mul_zero])
    rw [h_tail, add_zero] at hBy₀_x

    have hx_as_sum : (⟨x, hx_mem⟩ : W₀') = ∑ j : Fin n, (bW₀.repr x') j.succ • v j := by
      apply Subtype.ext
      simp only [v, Submodule.coe_sum, Submodule.coe_smul]
      rw [hx_sum, Fin.sum_univ_succ, hBy₀_x, zero_smul, zero_add]
    rw [hx_as_sum]
    exact Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))
  exact ⟨Module.Basis.mk hv_li hv_span, fun j => by simp [v, Module.Basis.mk]⟩

set_option linter.unusedVariables false in
/-- Extend a nondegenerate complement `W₁` of the radical of `W` to a
nondegenerate complement of the radical of `W' = W ⊔ ⟨y₀⟩` by adjoining the
hyperbolic pair `{x₀, y₀}`. -/
lemma nondegen_complement_extension_with_W₁
    (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm)
    (W W₁ : Submodule k V)
    (hW₁_le : W₁ ≤ W)
    (hDisj : Disjoint (SubspaceRadical B W) W₁)
    (hSup : SubspaceRadical B W ⊔ W₁ = W)
    (hW₁_nd : (restrict B W₁).Nondegenerate)
    (x₀ y₀ : V) (hx₀ : x₀ ∈ SubspaceRadical B W)
    (hy₀_orth : y₀ ∈ orthogonal B W₁)
    (hhp : IsHyperbolicPair B x₀ y₀) :
    let W' := W ⊔ Submodule.span k {y₀}
    ∃ (W₁' : Submodule k V),
      W₁ ≤ W₁' ∧
      Submodule.span k {x₀, y₀} ≤ W₁' ∧
      W₁' ≤ W' ∧
      Disjoint (SubspaceRadical B W') W₁' ∧
      SubspaceRadical B W' ⊔ W₁' = W' ∧
      (restrict B W₁').Nondegenerate := by
  intro W'

  set W₁' := W₁ ⊔ Submodule.span k {x₀, y₀}

  have hW₁'_le_W' : W₁' ≤ W' := sup_le (le_trans hW₁_le le_sup_left)
    (Submodule.span_le.mpr (fun v hv => by
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact Submodule.mem_sup_left (Submodule.mem_inf.mp hx₀).1
      · rw [Set.mem_singleton_iff] at hv; rw [hv]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)))

  have hDisj' : Disjoint (SubspaceRadical B W') W₁' := by
    rw [Submodule.disjoint_def]
    intro v hv_rad hv_W₁'
    have hv_orth : v ∈ orthogonal B W' := (Submodule.mem_inf.mp hv_rad).2
    have hBx₀v : B x₀ v = 0 :=
      hv_orth x₀ (Submodule.mem_sup_left (Submodule.mem_inf.mp hx₀).1)
    have hBy₀v : B y₀ v = 0 :=
      hv_orth y₀ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀))

    obtain ⟨w₁, hw₁, s, hs, hvs⟩ := Submodule.mem_sup.mp hv_W₁'
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hs

    have hBy₀w₁ : B y₀ w₁ = 0 := by rw [hBs.eq y₀ w₁]; exact hy₀_orth w₁ hw₁

    have ha_eq : a = 0 := by
      have := hBy₀v
      rw [← hvs, map_add, hBy₀w₁, zero_add, map_add, map_smul, map_smul,
          smul_eq_mul, smul_eq_mul, hBs.eq y₀ x₀, hhp.2.2, mul_one,
          hhp.2.1, mul_zero, add_zero] at this
      exact this

    have hBx₀w₁ : B x₀ w₁ = 0 := by
      rw [hBs.eq x₀ w₁]; exact (Submodule.mem_inf.mp hx₀).2 w₁ (hW₁_le hw₁)

    have hb_eq : b = 0 := by
      have := hBx₀v
      rw [← hvs, map_add, hBx₀w₁, zero_add, map_add, map_smul, map_smul,
          smul_eq_mul, smul_eq_mul, hhp.1, mul_zero, zero_add, hhp.2.2, mul_one] at this
      exact this

    subst ha_eq; subst hb_eq
    simp only [zero_smul, add_zero] at hvs
    rw [← hvs] at hv_orth ⊢

    have hv_orth_W : w₁ ∈ orthogonal B W := orthogonal_le le_sup_left hv_orth
    exact Submodule.disjoint_def.mp hDisj w₁
      (Submodule.mem_inf.mpr ⟨hW₁_le hw₁, hv_orth_W⟩) hw₁

  have hSup' : SubspaceRadical B W' ⊔ W₁' = W' := by
    apply le_antisymm
    · exact sup_le (fun _ h => (Submodule.mem_inf.mp h).1) hW₁'_le_W'
    · intro v hv
      obtain ⟨w, hw, s, hs, hvs⟩ := Submodule.mem_sup.mp hv
      have hs_W₁' : s ∈ W₁' :=
        Submodule.mem_sup_right (Submodule.span_mono (Set.subset_insert x₀ {y₀}) hs)
      rw [← hSup] at hw
      obtain ⟨r, hr, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hw

      set c := B y₀ r

      have hr'_orth : r - c • x₀ ∈ orthogonal B W' := by
        rw [mem_orthogonal_iff]
        intro n hn; rw [IsOrtho]
        obtain ⟨nw, hnw, ns, hns, rfl⟩ := Submodule.mem_sup.mp hn
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hns
        simp only [map_add, LinearMap.add_apply, map_sub, map_smul,
                   LinearMap.smul_apply, smul_eq_mul]
        rw [(Submodule.mem_inf.mp hr).2 nw hnw, (Submodule.mem_inf.mp hx₀).2 nw hnw]
        simp only [zero_add]
        rw [hBs.eq y₀ x₀, hhp.2.2, mul_one]; ring
      have hr'_W' : r - c • x₀ ∈ W' :=
        W'.sub_mem (Submodule.mem_sup_left ((Submodule.mem_inf.mp hr).1))
          (Submodule.mem_sup_left (W.smul_mem c ((Submodule.mem_inf.mp hx₀).1)))
      have hr'_rad : r - c • x₀ ∈ SubspaceRadical B W' :=
        Submodule.mem_inf.mpr ⟨hr'_W', hr'_orth⟩

      have hcx₀ : c • x₀ ∈ W₁' :=
        Submodule.mem_sup_right (Submodule.smul_mem _ c
          (Submodule.subset_span (Set.mem_insert x₀ {y₀})))

      rw [← hvs]
      have : r + w₁ + s = (r - c • x₀) + (c • x₀ + w₁ + s) := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hr'_rad)
        (Submodule.mem_sup_right
          (W₁'.add_mem (W₁'.add_mem hcx₀ (Submodule.mem_sup_left hw₁)) hs_W₁'))
  refine ⟨W₁', le_sup_left, le_sup_right, hW₁'_le_W', hDisj', hSup',
    restrict_complement_of_radical_nondegenerate B hBs.isRefl W' W₁' hW₁'_le_W' hDisj' hSup'⟩

set_option linter.unusedSectionVars false in
/-- A subspace `S` is a hyperbolic space for `B` if it is spanned by a finite
collection of mutually orthogonal hyperbolic pairs `{x_i, y_i}`. -/
def IsHyperbolicSpace (B : LinearMap.BilinForm k V) (S : Submodule k V) : Prop :=
  ∃ (n : ℕ) (x y : Fin n → V),
    (∀ i, IsHyperbolicPair B (x i) (y i)) ∧
    (∀ i j, i ≠ j → B (x i) (x j) = 0 ∧ B (x i) (y j) = 0 ∧ B (y i) (y j) = 0) ∧
    S = Submodule.span k (Set.range x ∪ Set.range y)

/-- Full kernel decomposition: given a basis `bW₀` for the radical of `W` and a
nondegenerate complement `W₁`, produce hyperbolic partners `y_i` that extend `W`
to a subspace whose radical-complement is fully nondegenerate and contains an
explicit hyperbolic-plane decomposition. -/
theorem kernel_decomposition_hyperbolic_planes_full
    {k : Type*} [Field k] [Invertible (2 : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hBs : B.IsSymm)
    (W W₁ : Submodule k V)
    (hW₁_le : W₁ ≤ W)
    (hDisj : Disjoint (SubspaceRadical B W) W₁)
    (hSup : SubspaceRadical B W ⊔ W₁ = W)
    (hW₁_nd : (restrict B W₁).Nondegenerate)
    (n : ℕ) (bW₀ : Module.Basis (Fin n) k (SubspaceRadical B W)) :
    ∃ (y : Fin n → V),
      (∀ i, y i ∈ orthogonal B W₁) ∧
      (∀ i, IsHyperbolicPair B (bW₀ i : V) (y i)) ∧
      (∀ i j, i ≠ j → B (bW₀ i : V) (y j) = 0 ∧ B (y i) (y j) = 0) ∧
      (restrict B (W ⊔ Submodule.span k (Set.range y))).Nondegenerate ∧
      IsHyperbolicSpace B (SubspaceRadical B W ⊔ Submodule.span k (Set.range y)) ∧
      Disjoint W (Submodule.span k (Set.range y)) := by

  suffices h : ∃ (y : Fin n → V),
      (∀ i, y i ∈ orthogonal B W₁) ∧
      (∀ i, IsHyperbolicPair B (bW₀ i : V) (y i)) ∧
      (∀ i j, i ≠ j → B (bW₀ i : V) (y j) = 0 ∧ B (y i) (y j) = 0) ∧
      (restrict B (W ⊔ Submodule.span k (Set.range y))).Nondegenerate by
    obtain ⟨y, h1, h2, h3, h4⟩ := h
    refine ⟨y, h1, h2, h3, h4, ?_, ?_⟩

    · let x : Fin n → V := fun i => (bW₀ i : V)
      refine ⟨n, x, y, h2, ?_, ?_⟩
      · intro i j hij
        have hj_orth : (bW₀ j : V) ∈ orthogonal B W :=
          (Submodule.mem_inf.mp (bW₀ j).prop).2
        have hi_W : (bW₀ i : V) ∈ W :=
          (Submodule.mem_inf.mp (bW₀ i).prop).1
        exact ⟨hj_orth _ hi_W, (h3 i j hij).1, (h3 i j hij).2⟩
      · rw [Submodule.span_union]
        congr 1
        have himg : Set.range x = (SubspaceRadical B W).subtype '' Set.range bW₀ := by
          ext v; constructor
          · rintro ⟨i, rfl⟩; exact ⟨bW₀ i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨w, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
        rw [himg, Submodule.span_image, bW₀.span_eq, Submodule.map_top,
            Submodule.range_subtype]

    · rw [Submodule.disjoint_def]
      intro v hv_W hv_span
      rw [Submodule.mem_span_range_iff_exists_fun] at hv_span
      obtain ⟨c, hc⟩ := hv_span
      have hB_zero : ∀ i, B (bW₀ i : V) v = 0 := by
        intro i
        have horth : (bW₀ i : V) ∈ orthogonal B W := (Submodule.mem_inf.mp (bW₀ i).prop).2
        rw [hBs.eq (bW₀ i : V) v]
        exact horth v hv_W
      have hB_coeff : ∀ i, B (bW₀ i : V) v = c i := by
        intro i
        rw [← hc, map_sum]
        simp only [map_smul, smul_eq_mul]
        have hδ : ∀ j, B (↑(bW₀ i)) (y j) = if i = j then 1 else 0 := by
          intro j
          split_ifs with hij
          · subst hij; exact (h2 i).2.2
          · exact (h3 i j hij).1
        simp_rw [hδ]
        simp [Finset.mem_univ]
      have hc_zero : ∀ i, c i = 0 := fun i => by rw [← hB_coeff i]; exact hB_zero i
      rw [← hc]; simp [hc_zero]

  induction n generalizing W W₁ with
  | zero =>
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, ?_⟩
    have : Set.range (Fin.elim0 : Fin 0 → V) = ∅ := Set.range_eq_empty _
    rw [this, Submodule.span_empty, sup_bot_eq]
    have hW₁_eq : W₁ = W := by
      have h0 : SubspaceRadical B W = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have := bW₀.repr ⟨x, hx⟩
        simp at this
        rw [Submodule.mem_bot]
        have : (⟨x, hx⟩ : SubspaceRadical B W) = 0 := by
          rw [← bW₀.repr.injective.eq_iff]
          ext i; exact Fin.elim0 i
        exact congr_arg Subtype.val this
      rw [h0, bot_sup_eq] at hSup
      exact hSup ▸ rfl
    rw [← hW₁_eq]; exact hW₁_nd
  | succ n ih =>

    obtain ⟨y₀, hy₀_orth, hy₀_hp, hy₀_tail⟩ :=
      hyperbolic_pair_from_radical_with_tail_orth B hB hBs W W₁ hW₁_le hSup hW₁_nd bW₀

    set W' := W ⊔ Submodule.span k {y₀}
    have hBy₀_1 : B (bW₀ 0 : V) y₀ = 1 := hy₀_hp.2.2
    obtain ⟨bW₀_new, hbW₀_new_eq⟩ :=
      radical_shrinks_after_hyperbolic_extension B hBs W bW₀ y₀ hBy₀_1 hy₀_tail

    have hx₀_rad : (bW₀ 0 : V) ∈ SubspaceRadical B W := (bW₀ 0).prop
    obtain ⟨W₁', hW₁_le', hxy_le', hW₁'_le, hDisj', hSup', hW₁'_nd⟩ :=
      nondegen_complement_extension_with_W₁ B hB hBs W W₁ hW₁_le hDisj hSup hW₁_nd
        (bW₀ 0 : V) y₀ hx₀_rad hy₀_orth hy₀_hp

    obtain ⟨y_tail, hy_tail_orth, hy_tail_hp, hy_tail_cross, hy_tail_nd⟩ :=
      ih W' W₁' hW₁'_le hDisj' hSup' hW₁'_nd bW₀_new

    have horth_le : orthogonal B W₁' ≤ orthogonal B W₁ :=
      orthogonal_le hW₁_le'

    have hx₀_in_W₁' : (bW₀ 0 : V) ∈ W₁' :=
      hxy_le' (Submodule.subset_span (Set.mem_insert _ _))
    have hy₀_in_W₁' : y₀ ∈ W₁' :=
      hxy_le' (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))

    refine ⟨Fin.cons y₀ y_tail, ?_, ?_, ?_, ?_⟩

    · intro i
      refine Fin.cases hy₀_orth (fun j => ?_) i
      simp only [Fin.cons_succ]
      exact horth_le (hy_tail_orth j)

    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; exact hy₀_hp
      · simp only [Fin.cons_succ]
        rw [← hbW₀_new_eq j]
        exact hy_tail_hp j

    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij

      · exact absurd rfl hij

      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact ⟨hy_tail_orth j' _ hx₀_in_W₁', hy_tail_orth j' _ hy₀_in_W₁'⟩

      · simp only [Fin.cons_zero, Fin.cons_succ]
        constructor
        · exact hy₀_tail i'
        · rw [hBs.eq (y_tail i') y₀]
          exact hy_tail_orth i' _ hy₀_in_W₁'

      · simp only [Fin.cons_succ]
        have hij' : i' ≠ j' := fun h => hij (congr_arg Fin.succ h)
        have := hy_tail_cross i' j' hij'
        constructor
        · rw [← hbW₀_new_eq i']; exact this.1
        · exact this.2

    · rw [Fin.range_cons, Set.insert_eq, Submodule.span_union, ← sup_assoc]
      exact hy_tail_nd

end Formalization.GeometricAlgebra
