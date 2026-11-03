/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Group

namespace GeometricAlgebra

/-- Abbreviation for the general linear group `GL(V)` of a `k`-module `V`. -/
abbrev GLV (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :=
  LinearMap.GeneralLinearGroup k V

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Convert a linear equivalence `V ≃ₗ[k] V` to an element of the general linear
group `GLV k V`. -/
noncomputable def linearEquivToGLV (e : V ≃ₗ[k] V) : GLV k V :=
  ⟨e.toLinearMap, e.symm.toLinearMap,
   by ext x; simp,
   by ext x; simp⟩

/-- The underlying linear map of `linearEquivToGLV e` is `e.toLinearMap`. -/
@[simp] lemma linearEquivToGLV_val (e : V ≃ₗ[k] V) :
    (↑(linearEquivToGLV e) : V →ₗ[k] V) = e.toLinearMap := rfl

/-- Convert an element of the general linear group `GLV k V` back to a linear
equivalence `V ≃ₗ[k] V`. -/
noncomputable def glvToLinearEquiv (g : GLV k V) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (↑g : V →ₗ[k] V) (↑(g⁻¹) : V →ₗ[k] V)
    (by ext x; change (↑(g * g⁻¹) : V →ₗ[k] V) x = x; simp [mul_inv_cancel])
    (by ext x; change (↑(g⁻¹ * g) : V →ₗ[k] V) x = x; simp [inv_mul_cancel])

/-- The linear map underlying `glvToLinearEquiv g` is the underlying map of `g`. -/
@[simp] lemma glvToLinearEquiv_toLinearMap (g : GLV k V) :
    (glvToLinearEquiv g).toLinearMap = (↑g : V →ₗ[k] V) := rfl

/-- Round-trip lemma: converting `g : GLV k V` to a linear equivalence and back
recovers `g`. -/
lemma linearEquivToGLV_glvToLinearEquiv (g : GLV k V) :
    linearEquivToGLV (glvToLinearEquiv g) = g := by
  ext x; show (glvToLinearEquiv g).toLinearMap x = (↑g : V →ₗ[k] V) x
  rw [glvToLinearEquiv_toLinearMap]

/-- The product `linearEquivToGLV d * linearEquivToGLV u` in `GLV k V` has
underlying linear map equal to the composition `d ∘ u`. -/
lemma linearEquivToGLV_mul_val (d u : V ≃ₗ[k] V) :
    (↑(linearEquivToGLV d * linearEquivToGLV u) : V →ₗ[k] V) =
    d.toLinearMap.comp u.toLinearMap := by
  show (↑(linearEquivToGLV d) : V →ₗ[k] V) ∘ₗ (↑(linearEquivToGLV u) : V →ₗ[k] V) = _; simp


/-- If a linear equivalence `e` preserves a submodule `W`, then so does its inverse
`e.symm`. -/
lemma map_inv_of_map_eq (e : V ≃ₗ[k] V) (W : Submodule k V)
    (h : W.map e.toLinearMap = W) : W.map e.symm.toLinearMap = W := by
  rw [Submodule.comap_equiv_eq_map_symm e W |>.symm]
  ext v; simp only [Submodule.mem_comap]
  constructor
  · intro hv
    have hmem : e v ∈ W.map e.toLinearMap := by rw [h]; exact hv
    rw [Submodule.mem_map] at hmem; obtain ⟨w, hw, hew⟩ := hmem
    exact e.injective hew ▸ hw
  · intro hv
    have : e v ∈ W.map e.toLinearMap := Submodule.mem_map_of_mem hv
    rwa [h] at this

/-- If `g ∈ GLV k V` sends a submodule `W₁` to `W₂`, then `g⁻¹` sends `W₂` back to `W₁`. -/
lemma map_inv_of_map_to (g : GLV k V) (W₁ W₂ : Submodule k V)
    (h : W₁.map (↑g : V →ₗ[k] V) = W₂) : W₂.map (↑(g⁻¹) : V →ₗ[k] V) = W₁ := by
  rw [← h]; ext x; simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    convert hz using 1; change (↑(g⁻¹ * g) : V →ₗ[k] V) z = z; simp [inv_mul_cancel]
  · intro hx
    exact ⟨(↑g : V →ₗ[k] V) x, ⟨x, hx, rfl⟩,
      by change (↑(g⁻¹ * g) : V →ₗ[k] V) x = x; simp [inv_mul_cancel]⟩


/-- A flag in a `k`-vector space `V` is a strictly increasing sequence of submodules
`spaces : Fin len → Submodule k V`. -/
structure Flag (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] where
  len : ℕ
  spaces : Fin len → Submodule k V
  strictMono : StrictMono spaces

namespace Flag

/-- The type of a flag `F` is the sequence of dimensions of its constituent
submodules. -/
noncomputable def type (F : Flag k V) : Fin F.len → ℕ :=
  fun i => Module.finrank k (F.spaces i)

/-- Two flags have the same type when they have the same length and the same
sequence of dimensions. -/
def sameType (F₁ F₂ : Flag k V) : Prop :=
  F₁.len = F₂.len ∧ ∀ (h : F₁.len = F₂.len) (i : Fin F₁.len),
    F₁.type i = F₂.type (i.cast h)


/-- The image of a submodule under the product of two `GL` elements equals the
iterated image: `W.map (a * b) = (W.map b).map a`. -/
lemma submodule_map_mul_eq (a b : GLV k V) (W : Submodule k V) :
    W.map (↑(a * b) : V →ₗ[k] V) = (W.map (↑b : V →ₗ[k] V)).map (↑a : V →ₗ[k] V) := by
  ext x; simp only [Submodule.mem_map, Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨(b : V →ₗ[k] V) y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

/-- The parabolic subgroup of `GL(V)` stabilizing a flag `F`: the elements
preserving every space in the flag. -/
def parabolicSubgroup (F : Flag k V) : Subgroup (GLV k V) where
  carrier := { g | ∀ i, (F.spaces i).map (g : V →ₗ[k] V) = F.spaces i }
  mul_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq] at *; intro i
    rw [submodule_map_mul_eq, hb i, ha i]
  one_mem' := by
    simp only [Set.mem_setOf_eq]; intro i; exact Submodule.map_id _
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    intro i; convert map_inv_of_map_to a _ _ (ha i) using 1


/-- The unipotent radical of the parabolic subgroup of `F`: elements in the
parabolic that act as the identity on each successive quotient `F.spaces i /
F.spaces (i-1)` (and as the identity on `F.spaces 0`). -/
def unipotentRadical (F : Flag k V) : Set (GLV k V) :=
  { g | g ∈ F.parabolicSubgroup ∧
    ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      (g : V →ₗ[k] V) v - v ∈
        if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ }


/-- An element of the parabolic subgroup of `F` maps each flag level into itself
pointwise. -/
lemma parabolic_mem_preserves {F : Flag k V} {g : GLV k V}
    (hg : g ∈ F.parabolicSubgroup) (i : Fin F.len) {v : V} (hv : v ∈ F.spaces i) :
    (↑g : V →ₗ[k] V) v ∈ F.spaces i := by
  rw [← hg i]; exact Submodule.mem_map_of_mem hv

/-- Multiplication by `g` then `g⁻¹` (as linear maps) cancels: `g (g⁻¹ v) = v`. -/
lemma gl_mul_inv_cancel (g : GLV k V) (v : V) :
    (↑g : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v) = v := by
  change ((↑g : V →ₗ[k] V) ∘ₗ (↑(g⁻¹) : V →ₗ[k] V)) v = v
  have : (↑g : V →ₗ[k] V) ∘ₗ (↑(g⁻¹) : V →ₗ[k] V) = LinearMap.id := by
    ext x; change (↑(g * g⁻¹) : V →ₗ[k] V) x = x; simp [mul_inv_cancel]
  rw [this]; simp

/-- Conjugation in `GLV k V` translates to threefold application of underlying
linear maps: `(g u g⁻¹) v = g (u (g⁻¹ v))`. -/
lemma gl_conj_apply (g u : GLV k V) (v : V) :
    (↑(g * u * g⁻¹) : V →ₗ[k] V) v =
      (↑g : V →ₗ[k] V) ((↑u : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v)) := by
  simp [Units.val_mul]

/-- Difference identity for conjugation: `(g u g⁻¹) v - v = g (u (g⁻¹ v) - g⁻¹ v)`. -/
lemma conj_minus_eq (g u : GLV k V) (v : V) :
    (↑(g * u * g⁻¹) : V →ₗ[k] V) v - v =
      (↑g : V →ₗ[k] V) ((↑u : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v) -
        (↑(g⁻¹) : V →ₗ[k] V) v) := by
  rw [gl_conj_apply, map_sub]; congr 1; exact (gl_mul_inv_cancel g v).symm

/-- If `g ∈ GL(V)` maps the flag `F₁` to `F₂` (level-wise), then the parabolic subgroup
of `F₂` is the `g`-conjugate of the parabolic subgroup of `F₁`. -/
lemma parabolic_conj (F₁ F₂ : Flag k V) (g : GLV k V)
    (hlen : F₁.len = F₂.len)
    (hg : ∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen)) :
    F₂.parabolicSubgroup = (F₁.parabolicSubgroup).map (MulAut.conj g).toMonoidHom := by
  ext h
  simp only [Subgroup.mem_map]
  constructor
  ·
    intro hh
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    ·
      intro i
      rw [show (g⁻¹ * h * g : GLV k V) = g⁻¹ * (h * g) from by group]
      rw [submodule_map_mul_eq, submodule_map_mul_eq]
      rw [hg i, hh (i.cast hlen), map_inv_of_map_to g _ _ (hg i)]
    ·
      simp [MulAut.conj_apply]; group
  ·
    rintro ⟨p, hp, rfl⟩
    intro j
    have hval : (↑((MulEquiv.toMonoidHom (MulAut.conj g)) p) : V →ₗ[k] V) =
        (↑(g * p * g⁻¹) : V →ₗ[k] V) := by simp [MulAut.conj_apply]
    show (F₂.spaces j).map (↑((MulEquiv.toMonoidHom (MulAut.conj g)) p) : V →ₗ[k] V) = F₂.spaces j
    rw [hval, show (g * p * g⁻¹ : GLV k V) = g * (p * g⁻¹) from by group]
    rw [submodule_map_mul_eq, submodule_map_mul_eq]
    let i : Fin F₁.len := j.cast hlen.symm
    rw [show j = i.cast hlen from by simp [i]]
    rw [map_inv_of_map_to g _ _ (hg i), hp i, hg i]


/-- For `g ∈ H`, conjugation by `g` preserves `H` and distributes over intersections:
`(H ⊓ K)^g = H ⊓ K^g`. -/
lemma inf_map_conj_of_mem {G : Type*} [Group G] (H K : Subgroup G) (g : G) (hg : g ∈ H) :
    (H ⊓ K).map (MulAut.conj g).toMonoidHom = H ⊓ K.map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, ⟨hyH, hyK⟩, rfl⟩
    exact ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), y, hyK, rfl⟩
  · rintro ⟨hxH, y, hyK, rfl⟩
    refine ⟨y, ⟨?_, hyK⟩, rfl⟩
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg

/-- Conjugation in `GLV k V` distributes over intersection of subgroups. -/
lemma conj_map_inf (H K : Subgroup (GLV k V)) (g : GLV k V) :
    (H ⊓ K).map (MulAut.conj g).toMonoidHom =
    H.map (MulAut.conj g).toMonoidHom ⊓ K.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_inf_eq H K _ (MulEquiv.injective _)


/-- Two flags are opposite if they have the same length and type, and each matched
pair of levels `(F.spaces i, F'.spaces (F'.len - 1 - i))` is complementary. -/
def isOppositeFlag (F F' : Flag k V) : Prop :=
  F.len = F'.len ∧ F.sameType F' ∧
    ∀ (h : F.len = F'.len) (i : Fin F.len),
      let j : Fin F'.len := ⟨F'.len - 1 - i.val, by omega⟩
      F.spaces i ⊔ F'.spaces j = ⊤ ∧ F.spaces i ⊓ F'.spaces j = ⊥

/-- The parabolic subgroup attached to the opposite flag `F'`. -/
def oppositeParabolic (F' : Flag k V) : Subgroup (GLV k V) := F'.parabolicSubgroup

/-- The Levi component associated with an opposite pair of flags `(F, F')`: the
intersection of their parabolic subgroups. -/
def leviComponent (F F' : Flag k V) (_ : isOppositeFlag F F') : Subgroup (GLV k V) :=
  F.parabolicSubgroup ⊓ F'.parabolicSubgroup


/-- The parabolic subgroup of `F` is a semidirect product of its Levi component
(with respect to the opposite flag `F'`) and its unipotent radical: every element
of the parabolic factors uniquely as a Levi times unipotent. -/
def ParabolicsSemidirectProduct (F F' : Flag k V) (h : isOppositeFlag F F') : Prop :=
  (∀ p ∈ F.parabolicSubgroup,
    ∃ m u : GLV k V,
      m ∈ leviComponent F F' h ∧ u ∈ F.unipotentRadical ∧ p = m * u) ∧
  (∀ m₁ m₂ u₁ u₂ : GLV k V,
    m₁ ∈ leviComponent F F' h → m₂ ∈ leviComponent F F' h →
    u₁ ∈ F.unipotentRadical → u₂ ∈ F.unipotentRadical →
    m₁ * u₁ = m₂ * u₂ → m₁ = m₂ ∧ u₁ = u₂)

end Flag


namespace Flag

/-- Drop the top space from a flag, keeping the first `F.len - 1` levels. -/
def truncate (F : Flag k V) (h : 1 ≤ F.len) : Flag k V where
  len := F.len - 1
  spaces := fun i => F.spaces ⟨i.val, by omega⟩
  strictMono := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    exact F.strictMono (show (⟨a, by omega⟩ : Fin F.len) < ⟨b, by omega⟩ from hab)

/-- Drop the bottom space from a flag, keeping levels from index `1` onwards. -/
def truncateStart (F : Flag k V) (h : 1 ≤ F.len) : Flag k V where
  len := F.len - 1
  spaces := fun i => F.spaces ⟨i.val + 1, by omega⟩
  strictMono := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have : a < b := hab
    show F.spaces ⟨a + 1, by omega⟩ < F.spaces ⟨b + 1, by omega⟩
    exact F.strictMono (by simp [Fin.lt_def]; omega)

/-- The length of `F.truncate h` is `F.len - 1`. -/
@[simp] lemma truncate_len (F : Flag k V) (h : 1 ≤ F.len) :
    (F.truncate h).len = F.len - 1 := rfl

/-- The length of `F.truncateStart h` is `F.len - 1`. -/
@[simp] lemma truncateStart_len (F : Flag k V) (h : 1 ≤ F.len) :
    (F.truncateStart h).len = F.len - 1 := rfl

/-- The spaces of `F.truncate h` agree with those of `F` at the same indices. -/
lemma truncate_spaces (F : Flag k V) (h : 1 ≤ F.len) (i : Fin (F.len - 1)) :
    (F.truncate h).spaces i = F.spaces ⟨i.val, by omega⟩ :=
  rfl

/-- The spaces of `F.truncateStart h` are `F.spaces ⟨i + 1, …⟩`. -/
lemma truncateStart_spaces (F : Flag k V) (h : 1 ≤ F.len) (i : Fin (F.len - 1)) :
    (F.truncateStart h).spaces i = F.spaces ⟨i.val + 1, by omega⟩ :=
  rfl

end Flag


/-- A pair of opposite flags is a "covering" pair when `F` is nonempty and its top
space is all of `V`. -/
def Flag.IsCoveringOppositePair (F F' : Flag k V) (_ : Flag.isOppositeFlag F F') : Prop :=
  ∃ (hlen : 0 < F.len), F.spaces ⟨F.len - 1, by omega⟩ = ⊤

/-- Existence property: for every covering opposite pair `(F, F')` and every flag
stabilizer `p` of `F`, there exists a Levi-unipotent factorization `p = d ∘ u`. -/
class SemidirectExistenceProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  exists_decomp_linear : ∀ (F F' : Flag k V) (_h : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (p : V ≃ₗ[k] V),
    (∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) →
      ∃ (d u : V ≃ₗ[k] V),
        (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
        (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
          u.toLinearMap v - v ∈
            if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
            else F.spaces ⟨i.val - 1, by omega⟩) ∧
        p.toLinearMap = d.toLinearMap.comp u.toLinearMap

/-- Uniqueness in `M ∩ U = {1}`: a linear equivalence that simultaneously preserves
the opposite flag `F'` levelwise and is unipotent along `F` must be the identity. -/
lemma Flag.unipotent_levi_is_id
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (e : V ≃ₗ[k] V)
    (he_F' : ∀ i : Fin F'.len, (F'.spaces i).map e.toLinearMap = F'.spaces i)
    (hunip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) :
    e = LinearEquiv.refl k V := by
  ext v; simp only [LinearEquiv.refl_apply]
  suffices hind : ∀ (n : ℕ) (hn : n < F.len), ∀ w ∈ F.spaces ⟨n, hn⟩, e w = w by
    have hv : v ∈ F.spaces ⟨F.len - 1, by omega⟩ := by rw [hcov]; exact Submodule.mem_top
    exact hind (F.len - 1) (by omega) v hv
  intro n
  induction n with
  | zero =>
    intro hn w hw
    have := hunip ⟨0, hn⟩ w hw; simp at this; rwa [sub_eq_zero] at this
  | succ m ih =>
    intro hn w hw
    have ih_m : ∀ w ∈ F.spaces ⟨m, by omega⟩, e w = w := ih (by omega)
    have hunip_w : e.toLinearMap w - w ∈ F.spaces ⟨m, by omega⟩ := by
      have := hunip ⟨m + 1, hn⟩ w hw; simp at this; exact this
    obtain ⟨hlen_eq, _, hopp_compl⟩ := hopp
    have hopp_m := hopp_compl hlen_eq ⟨m, by omega⟩
    obtain ⟨hsup_m, hinf_m⟩ := hopp_m
    have hw_top : w ∈ F.spaces ⟨m, by omega⟩ ⊔ F'.spaces ⟨F'.len - 1 - m, by omega⟩ := by
      rw [hsup_m]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hw_top
    obtain ⟨wp, hwp, wq, hwq, hwpq⟩ := hw_top
    have hewp : e wp = wp := ih_m wp hwp
    have hew : e w = wp + e wq := by
      rw [← hwpq]; show e (wp + wq) = wp + e wq
      simp [map_add, hewp]
    have h_diff_in_p : e wq - wq ∈ F.spaces ⟨m, by omega⟩ := by
      have hmem : e.toLinearMap w - w ∈ F.spaces ⟨m, by omega⟩ := hunip_w
      have key : e.toLinearMap w - w = e wq - wq := by
        show e w - w = e wq - wq
        rw [hew, ← hwpq]; simp [add_sub_add_left_eq_sub]
      rwa [key] at hmem
    have h_ewq_in_q : e wq ∈ F'.spaces ⟨F'.len - 1 - m, by omega⟩ := by
      rw [← he_F' ⟨F'.len - 1 - m, by omega⟩]; exact Submodule.mem_map_of_mem hwq
    have h_diff_in_q : e wq - wq ∈ F'.spaces ⟨F'.len - 1 - m, by omega⟩ :=
      (F'.spaces ⟨F'.len - 1 - m, by omega⟩).sub_mem h_ewq_in_q hwq
    have h_diff_zero : e wq - wq = 0 := by
      have h4 := Submodule.mem_inf.mpr ⟨h_diff_in_p, h_diff_in_q⟩
      rw [hinf_m, Submodule.mem_bot] at h4; exact h4
    have hewq : e wq = wq := sub_eq_zero.mp h_diff_zero
    rw [hew, hewq, hwpq]

/-- Uniqueness of the Levi-unipotent factorization at the linear-equivalence level:
if `d₁ ∘ u₁ = d₂ ∘ u₂` with both factors lying in the appropriate Levi and
unipotent subspaces, then `d₁ = d₂` and `u₁ = u₂`. -/
lemma Flag.unique_decomp_linear_proof
    (F F' : Flag k V) (hopp : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (d₁ d₂ u₁ u₂ : V ≃ₗ[k] V)
    (_hd₁_F : ∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i)
    (hd₁_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i)
    (_hd₂_F : ∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i)
    (hd₂_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i)
    (hu₁_F : ∀ i : Fin F.len, (F.spaces i).map u₁.toLinearMap = F.spaces i)
    (hu₁_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₁.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩)
    (_hu₂_F : ∀ i : Fin F.len, (F.spaces i).map u₂.toLinearMap = F.spaces i)
    (hu₂_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₂.toLinearMap v - v ∈
        if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩)
    (hcomp : d₁.toLinearMap.comp u₁.toLinearMap = d₂.toLinearMap.comp u₂.toLinearMap) :
    d₁ = d₂ ∧ u₁ = u₂ := by


  set e := d₁.trans d₂.symm with he_def

  have he_F' : ∀ i : Fin F'.len, (F'.spaces i).map e.toLinearMap = F'.spaces i := by
    intro i
    show (F'.spaces i).map (d₂.symm.toLinearMap.comp d₁.toLinearMap) = F'.spaces i
    rw [Submodule.map_comp, hd₁_F' i, map_inv_of_map_eq d₂ _ (hd₂_F' i)]

  have he_eq : ∀ v : V, e v = u₂ (u₁.symm v) := by
    intro v
    show d₂.symm (d₁ v) = u₂ (u₁.symm v)
    have hc := LinearMap.congr_fun hcomp (u₁.symm v)
    simp at hc
    have := congr_arg d₂.symm hc
    simp at this
    exact this

  have he_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e.toLinearMap v - v ∈
        if hh : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ := by
    intro i v hv
    set w := u₁.symm v with hw_def
    have hw_mem : w ∈ F.spaces i := by
      rw [← map_inv_of_map_eq u₁ _ (hu₁_F i)]; exact Submodule.mem_map_of_mem hv
    have hev : e v = u₂ w := he_eq v
    have hew_diff : e v - v = (u₂ w - w) - (u₁ w - w) := by
      rw [hev, hw_def]; simp [LinearEquiv.apply_symm_apply]
    rw [show e.toLinearMap v - v = e v - v from rfl, hew_diff]
    have h1 := hu₂_unip i w hw_mem
    have h2 := hu₁_unip i w hw_mem
    split_ifs at h1 h2 ⊢ with hi
    · rw [Submodule.mem_bot] at h1 h2 ⊢
      rw [show u₂ w = (u₂.toLinearMap w : V) from rfl,
          show u₁ w = (u₁.toLinearMap w : V) from rfl, h1, h2, sub_self]
    · exact (F.spaces ⟨i.val - 1, by omega⟩).sub_mem h1 h2

  have he_id := Flag.unipotent_levi_is_id F F' hopp hlen hcov e he_F' he_unip

  have hd_eq : d₁ = d₂ := by
    ext v
    have h := LinearEquiv.congr_fun he_id v
    simp [he_def] at h
    have := congr_arg d₂ h
    simp at this
    exact this

  have hu_eq : u₁ = u₂ := by
    ext v
    have hc := LinearMap.congr_fun hcomp v
    simp at hc
    rw [hd_eq] at hc
    exact d₂.injective hc
  exact ⟨hd_eq, hu_eq⟩

/-- Combined property packaging both existence and uniqueness of the Levi-unipotent
decomposition of the flag stabilizer. -/
class SemidirectDecompositionProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  exists_decomp_linear : ∀ (F F' : Flag k V) (_h : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (p : V ≃ₗ[k] V),
    (∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) →
      ∃ (d u : V ≃ₗ[k] V),
        (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
        (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
        (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
          u.toLinearMap v - v ∈
            if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
            else F.spaces ⟨i.val - 1, by omega⟩) ∧
        p.toLinearMap = d.toLinearMap.comp u.toLinearMap
  unique_decomp_linear : ∀ (F F' : Flag k V) (_h : Flag.isOppositeFlag F F')
    (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
    (d₁ d₂ u₁ u₂ : V ≃ₗ[k] V),
    (∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i) →
    (∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i) →
    (∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i) →
    (∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i) →
    (∀ i : Fin F.len, (F.spaces i).map u₁.toLinearMap = F.spaces i) →
    (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₁.toLinearMap v - v ∈
        if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) →
    (∀ i : Fin F.len, (F.spaces i).map u₂.toLinearMap = F.spaces i) →
    (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      u₂.toLinearMap v - v ∈
        if _ : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩) →
    d₁.toLinearMap.comp u₁.toLinearMap = d₂.toLinearMap.comp u₂.toLinearMap →
    d₁ = d₂ ∧ u₁ = u₂

/-- The existence property `SemidirectExistenceProperty` together with the
unique-decomposition lemma `Flag.unique_decomp_linear_proof` yields the combined
`SemidirectDecompositionProperty`. -/
instance instSemidirectDecompositionProperty [SemidirectExistenceProperty k V] :
    SemidirectDecompositionProperty k V where
  exists_decomp_linear := SemidirectExistenceProperty.exists_decomp_linear
  unique_decomp_linear := fun F F' hopp hlen hcov d₁ d₂ u₁ u₂
    hd₁F hd₁F' hd₂F hd₂F' hu₁F hu₁U hu₂F hu₂U hcomp =>
    Flag.unique_decomp_linear_proof F F' hopp hlen hcov
      d₁ d₂ u₁ u₂ hd₁F hd₁F' hd₂F hd₂F' hu₁F hu₁U hu₂F hu₂U hcomp


/-- Two flags of the same type are linearly equivalent: there exists a linear
automorphism of `V` mapping one to the other levelwise. -/
class FlagEquivalenceProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  equiv_linear : ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len),
      ∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen)

/-- Group-level corollary of `FlagEquivalenceProperty`: same-type flags are conjugate
under some element of `GLV k V`. -/
theorem FlagsOfSameTypeAreGLEquivalent (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FlagEquivalenceProperty k V] :
    ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ →
      ∃ (g : GLV k V) (hlen : F₁.len = F₂.len),
        ∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen) := by
  intro F₁ F₂ hst
  obtain ⟨e, hlen, he⟩ := FlagEquivalenceProperty.equiv_linear F₁ F₂ hst
  refine ⟨linearEquivToGLV e, hlen, fun i => ?_⟩
  rw [linearEquivToGLV_val]
  exact he i

/-- For any flag `F`, any two flags opposite to `F` are conjugate via a linear
automorphism that preserves `F` levelwise. -/
class OppositeSystemsConjugacyProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  conjugate_linear : ∀ (F : Flag k V) (F'₁ F'₂ : Flag k V)
    (_h₁ : Flag.isOppositeFlag F F'₁) (_h₂ : Flag.isOppositeFlag F F'₂),
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen))

/-- Group-level corollary of `OppositeSystemsConjugacyProperty`: opposite flags to a
fixed `F` are conjugate by an element of the parabolic subgroup of `F`. -/
theorem OppositeSystemsAreConjugate (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V]
    [OppositeSystemsConjugacyProperty k V] :
    ∀ (F : Flag k V) (F'₁ F'₂ : Flag k V)
      (_h₁ : Flag.isOppositeFlag F F'₁) (_h₂ : Flag.isOppositeFlag F F'₂),
      ∃ (p : GLV k V) (_hp : p ∈ F.parabolicSubgroup) (hlen : F'₁.len = F'₂.len),
        ∀ i : Fin F'₁.len, (F'₁.spaces i).map (↑p : V →ₗ[k] V) = F'₂.spaces (i.cast hlen) := by
  intro F F'₁ F'₂ h₁ h₂
  obtain ⟨e, hlen, hpres, hmap⟩ :=
    OppositeSystemsConjugacyProperty.conjugate_linear F F'₁ F'₂ h₁ h₂
  refine ⟨linearEquivToGLV e, ?_, hlen, fun i => ?_⟩
  ·
    intro i
    rw [linearEquivToGLV_val]
    exact hpres i
  · rw [linearEquivToGLV_val]
    exact hmap i

/-- Group-level form of the semidirect existence: under
`SemidirectDecompositionProperty`, any element of the parabolic subgroup of `F`
factors as a Levi component times a unipotent radical element. -/
theorem SemidirectDecompositionExists [SemidirectDecompositionProperty k V] :
    ∀ (F F' : Flag k V) (h : Flag.isOppositeFlag F F')
      (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
      (p : GLV k V),
      p ∈ F.parabolicSubgroup →
        ∃ m u : GLV k V,
          m ∈ Flag.leviComponent F F' h ∧ u ∈ F.unipotentRadical ∧ p = m * u := by
  intro F F' hopp hlen hcov p hp

  let pe := glvToLinearEquiv p

  have hpe : ∀ i : Fin F.len, (F.spaces i).map pe.toLinearMap = F.spaces i :=
    fun i => by simp [pe]; exact hp i

  obtain ⟨d, u, hd_F, hd_F', hu_F, hu_unip, hcomp⟩ :=
    SemidirectDecompositionProperty.exists_decomp_linear F F' hopp hlen hcov pe hpe

  refine ⟨linearEquivToGLV d, linearEquivToGLV u, ?_, ?_, ?_⟩
  ·
    exact ⟨fun i => by rw [linearEquivToGLV_val]; exact hd_F i,
           fun i => by rw [linearEquivToGLV_val]; exact hd_F' i⟩
  ·
    refine ⟨fun i => by rw [linearEquivToGLV_val]; exact hu_F i, ?_⟩
    intro i v hv
    show (↑(linearEquivToGLV u) : V →ₗ[k] V) v - v ∈ _
    rw [linearEquivToGLV_val]
    exact hu_unip i v hv
  ·
    ext x
    have : (↑p : V →ₗ[k] V) x = (d.toLinearMap.comp u.toLinearMap) x := by
      rw [← hcomp]; simp [pe]
    rw [this]
    show _ = (↑(linearEquivToGLV d * linearEquivToGLV u) : V →ₗ[k] V) x
    rw [linearEquivToGLV_mul_val]

/-- Group-level uniqueness for the semidirect decomposition: the Levi-unipotent
factorization of an element of the parabolic subgroup is unique. -/
theorem SemidirectDecompositionUnique [SemidirectDecompositionProperty k V] :
    ∀ (F F' : Flag k V) (h : Flag.isOppositeFlag F F')
      (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
      (m₁ m₂ u₁ u₂ : GLV k V),
      m₁ ∈ Flag.leviComponent F F' h → m₂ ∈ Flag.leviComponent F F' h →
      u₁ ∈ F.unipotentRadical → u₂ ∈ F.unipotentRadical →
      m₁ * u₁ = m₂ * u₂ → m₁ = m₂ ∧ u₁ = u₂ := by
  intro F F' hopp hlen hcov m₁ m₂ u₁ u₂ hm₁ hm₂ hu₁ hu₂ heq

  let d₁ := glvToLinearEquiv m₁
  let d₂ := glvToLinearEquiv m₂
  let e₁ := glvToLinearEquiv u₁
  let e₂ := glvToLinearEquiv u₂

  have hd₁_F : ∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i :=
    fun i => by simp [d₁]; exact hm₁.1 i
  have hd₁_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i :=
    fun i => by simp [d₁]; exact hm₁.2 i
  have hd₂_F : ∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i :=
    fun i => by simp [d₂]; exact hm₂.1 i
  have hd₂_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i :=
    fun i => by simp [d₂]; exact hm₂.2 i
  have he₁_F : ∀ i : Fin F.len, (F.spaces i).map e₁.toLinearMap = F.spaces i :=
    fun i => by simp [e₁]; exact hu₁.1 i
  have he₁_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e₁.toLinearMap v - v ∈
        if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ :=
    fun i v hv => by simp only [e₁, glvToLinearEquiv_toLinearMap]; exact hu₁.2 i v hv
  have he₂_F : ∀ i : Fin F.len, (F.spaces i).map e₂.toLinearMap = F.spaces i :=
    fun i => by simp [e₂]; exact hu₂.1 i
  have he₂_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
      e₂.toLinearMap v - v ∈
        if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
        else F.spaces ⟨i.val - 1, by omega⟩ :=
    fun i v hv => by simp only [e₂, glvToLinearEquiv_toLinearMap]; exact hu₂.2 i v hv

  have hcomp_eq : d₁.toLinearMap.comp e₁.toLinearMap =
      d₂.toLinearMap.comp e₂.toLinearMap := by
    simp only [d₁, d₂, e₁, e₂, glvToLinearEquiv_toLinearMap]
    have : (↑(m₁ * u₁) : V →ₗ[k] V) = (↑(m₂ * u₂) : V →ₗ[k] V) := by rw [heq]
    simpa [Units.val_mul] using this

  have ⟨hd_eq, he_eq⟩ := SemidirectDecompositionProperty.unique_decomp_linear
    F F' hopp hlen hcov d₁ d₂ e₁ e₂ hd₁_F hd₁_F' hd₂_F hd₂_F' he₁_F he₁_unip he₂_F he₂_unip hcomp_eq

  constructor
  · have := congr_arg linearEquivToGLV hd_eq
    rwa [linearEquivToGLV_glvToLinearEquiv, linearEquivToGLV_glvToLinearEquiv] at this
  · have := congr_arg linearEquivToGLV he_eq
    rwa [linearEquivToGLV_glvToLinearEquiv, linearEquivToGLV_glvToLinearEquiv] at this

/-- Any two same-type pairs of opposite flags `(F₁, F'₁)` and `(F₂, F'₂)` are
linearly equivalent: one linear automorphism of `V` carries both `F₁ ↦ F₂` and
`F'₁ ↦ F'₂` levelwise. -/
class CompleteFlagPairEquivalenceProperty (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  equiv_linear : ∀ (F₁ F₂ : Flag k V) (F'₁ F'₂ : Flag k V)
    (_ : Flag.isOppositeFlag F₁ F'₁) (_ : Flag.isOppositeFlag F₂ F'₂),
    F₁.sameType F₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len) (hlen' : F'₁.len = F'₂.len),
      (∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen)) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen'))

/-- Group-level corollary of `CompleteFlagPairEquivalenceProperty`: same-type
opposite flag pairs are conjugate via an element of `GLV k V`. -/
theorem CompleteFlagPairsAreGLEquivalent (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [CompleteFlagPairEquivalenceProperty k V] :
    ∀ (F₁ F₂ : Flag k V) (F'₁ F'₂ : Flag k V)
      (_ : Flag.isOppositeFlag F₁ F'₁) (_ : Flag.isOppositeFlag F₂ F'₂),
      F₁.sameType F₂ →
      ∃ (g : GLV k V) (hlen : F₁.len = F₂.len) (hlen' : F'₁.len = F'₂.len),
        (∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen)) ∧
        (∀ i : Fin F'₁.len, (F'₁.spaces i).map (↑g : V →ₗ[k] V) = F'₂.spaces (i.cast hlen')) := by
  intro F₁ F₂ F'₁ F'₂ h₁ h₂ hst
  obtain ⟨e, hlen, hlen', he_F, he_F'⟩ :=
    CompleteFlagPairEquivalenceProperty.equiv_linear F₁ F₂ F'₁ F'₂ h₁ h₂ hst
  refine ⟨linearEquivToGLV e, hlen, hlen', fun i => ?_, fun i => ?_⟩
  · rw [linearEquivToGLV_val]; exact he_F i
  · rw [linearEquivToGLV_val]; exact he_F' i

end GeometricAlgebra
