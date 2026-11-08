/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- Every element of the Weyl group maps the root system to itself. -/
lemma RootSystem.weylGroupMem_maps_roots (Φ : RootSystem E) {g : E → E}
    (hg : Φ.WeylGroupMem g) : ∀ β ∈ Φ.roots, g β ∈ Φ.roots := by
  induction hg with
  | id => intro β hβ; exact hβ
  | gen α hα => intro β hβ; exact Φ.reflection_closed α hα β hβ
  | comp f g _hf _hg ihf ihg => intro β hβ; exact ihf _ (ihg β hβ)

/-- Composition of two right-folded reflection products equals the fold over the
concatenation. -/
lemma foldr_refl_comp_eq (αs₁ αs₂ : List E) (x : E) :
    (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id)
      ((αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) x) =
    ((αs₁ ++ αs₂).foldr (fun a f => linearReflection a ∘ f) _root_.id) x := by
  induction αs₁ with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, Function.comp_apply, List.cons_append]; exact congr_arg _ ih

/-- Every Weyl-group element is a finite composition of reflections $s_{α_1} \cdots s_{α_k}$
with $α_i ∈ Φ$. -/
lemma RootSystem.weylGroupMem_is_composition (Φ : RootSystem E) {g : E → E}
    (hg : Φ.WeylGroupMem g) :
    ∃ αs : List E, (∀ a ∈ αs, a ∈ Φ.roots) ∧
      g = αs.foldr (fun a f => linearReflection a ∘ f) _root_.id := by
  induction hg with
  | id => exact ⟨[], by simp, rfl⟩
  | gen α hα =>
    refine ⟨[α], fun a ha => ?_, by simp⟩
    simp at ha; subst ha; exact hα
  | comp f g _hf _hg ihf ihg =>
    obtain ⟨αs₁, h₁, rfl⟩ := ihf
    obtain ⟨αs₂, h₂, rfl⟩ := ihg
    refine ⟨αs₁ ++ αs₂, fun a ha => ?_, ?_⟩
    · rcases List.mem_append.mp ha with h | h
      · exact h₁ a h
      · exact h₂ a h
    · ext x; simp only [Function.comp_apply]; exact foldr_refl_comp_eq αs₁ αs₂ x

/-- A composition of reflections is a linear map. -/
lemma foldr_refl_is_linear (αs : List E) :
    ∃ L : E →ₗ[ℝ] E, ∀ v, L v =
      (αs.foldr (fun a f => linearReflection a ∘ f) _root_.id) v := by
  induction αs with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons a as ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨(linearReflectionLM a).comp L, fun v => ?_⟩
    simp only [LinearMap.comp_apply, linearReflectionLM_apply, List.foldr_cons,
      Function.comp_apply]
    rw [← hL]

/-- Two reflection compositions that agree on a spanning set are equal as functions. -/
lemma foldr_refl_eq_of_agree_on_roots (αs₁ αs₂ : List E) (S : Set E)
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ x ∈ S,
      (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id) x =
      (αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) x) :
    (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id) =
    (αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) := by
  obtain ⟨L₁, hL₁⟩ := foldr_refl_is_linear αs₁
  obtain ⟨L₂, hL₂⟩ := foldr_refl_is_linear αs₂
  have hLeq : L₁ = L₂ := by
    apply LinearMap.ext_on hS
    intro x hx
    rw [hL₁, hL₂]
    exact h x hx
  ext v
  rw [← hL₁ v, ← hL₂ v, hLeq]

open Classical in
/-- Restriction of an endomorphism $g$ of $E$ to the finite set $Φ$ of roots, falling
back to the identity when $g$ does not preserve roots. -/
def restrictToRoots (Φ : RootSystem E) (g : E → E) : ↥Φ.roots → ↥Φ.roots :=
  fun ⟨β, hβ⟩ => if h : g β ∈ Φ.roots then ⟨g β, h⟩ else ⟨β, hβ⟩

/-- For Weyl-group elements the restriction agrees with $g$ on the roots. -/
lemma restrictToRoots_val (Φ : RootSystem E) {g : E → E}
    (hg : Φ.WeylGroupMem g) (β : ↥Φ.roots) :
    (restrictToRoots Φ g β).val = g β.val := by
  simp only [restrictToRoots]
  rw [dif_pos (Φ.weylGroupMem_maps_roots hg β.val β.prop)]

/-- A reflection sends its defining root to its negative: $s_α(α) = -α$. -/
lemma linearReflection_self (α : E) (hα : α ≠ 0) : linearReflection α α = -α := by
  simp only [linearReflection]
  have h : 2 * ⟪α, α⟫_ℝ / ⟪α, α⟫_ℝ = 2 := by
    rw [mul_div_cancel_of_imp]
    intro h; exact absurd (inner_self_eq_zero.mp h) hα
  rw [h, two_smul]; abel

/-- Root systems are stable under negation: if $α ∈ Φ$ then $-α ∈ Φ$. -/
lemma RootSystem.neg_mem_roots (Φ : RootSystem E) {α : E} (hα : α ∈ Φ.roots) :
    -α ∈ Φ.roots := by
  rw [← linearReflection_self α (Φ.roots_ne_zero α hα)]
  exact Φ.reflection_closed α hα α hα

/-- The right-fold of $\circ$ over a list distributes over list append. -/
lemma foldr_comp_append {α : Type*} (l₁ l₂ : List (α → α)) :
    l₁.foldr (· ∘ ·) _root_.id ∘ l₂.foldr (· ∘ ·) _root_.id =
    (l₁ ++ l₂).foldr (· ∘ ·) _root_.id := by
  induction l₁ with
  | nil => simp
  | cons f l₁ ih =>
    simp only [List.foldr_cons, List.cons_append]
    rw [← ih]; ext; simp [Function.comp]

/-- `List.ofFn` of a `Fin.append` of two reflection families equals the concatenation
of the individual `List.ofFn`s. -/
lemma ofFn_linearReflection_append {n₁ n₂ : ℕ}
    (αs₁ : Fin n₁ → E) (αs₂ : Fin n₂ → E) :
    (List.ofFn fun i => linearReflection (Fin.append αs₁ αs₂ i)) =
    (List.ofFn fun i => linearReflection (αs₁ i)) ++
    (List.ofFn fun i => linearReflection (αs₂ i)) := by
  have : (fun i => linearReflection (Fin.append αs₁ αs₂ i)) =
         Fin.append (fun i => linearReflection (αs₁ i)) (fun i => linearReflection (αs₂ i)) := by
    ext i
    simp [Fin.append]
    exact Fin.addCases (fun j => by simp [Fin.addCases]) (fun j => by simp [Fin.addCases]) i
  rw [this, List.ofFn_fin_append]

/-- Any right-fold of reflections by roots is an element of the Weyl group. -/
lemma RootSystem.list_foldr_weylGroupMem (Φ : RootSystem E) (αs : List E)
    (hαs : ∀ a ∈ αs, a ∈ Φ.roots) :
    Φ.WeylGroupMem (αs.foldr (fun a g => linearReflection a ∘ g) _root_.id) := by
  induction αs with
  | nil => simpa using WeylGroupMem.id
  | cons a as ih =>
    simp only [List.foldr_cons]
    exact WeylGroupMem.comp _ _
      (WeylGroupMem.gen a (hαs a List.mem_cons_self))
      (ih (fun b hb => hαs b (List.mem_cons_of_mem a hb)))

end FiniteReflectionGroups
