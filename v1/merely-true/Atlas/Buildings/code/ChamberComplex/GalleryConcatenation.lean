/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Basic

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace Gallery

/-- The chamber list of a gallery is nonempty. -/
lemma chambers_ne_nil {K : SimplicialComplex V} (g : Gallery K) :
    g.chambers ≠ [] :=
  List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one
    (Nat.one_le_of_lt g.length_pos))

/-- If $g$ connects $C$ to $D$, then $D$ appears in the chamber list of $g$. -/
lemma last_mem_of_connects {K : SimplicialComplex V} {g : Gallery K}
    {C D : Finset V} (hconn : g.Connects C D) :
    D ∈ g.chambers := by
  have hne := chambers_ne_nil g
  have h2 := hconn.2
  rw [List.getLast?_eq_some_getLast hne] at h2
  have : g.chambers.getLast hne = D := Option.some_injective _ h2
  rw [← this]
  exact List.getLast_mem hne

/-- Gallery concatenation: galleries $g_1 : C_1 \rightsquigarrow C_2$ and
$g_2 : C_2 \rightsquigarrow C_3$ combine into a gallery $g_3 : C_1 \rightsquigarrow C_3$ with
$\ell(g_3) = \ell(g_1) + \ell(g_2)$ and $C_2 \in g_3$. -/
theorem gallery_concat {K : SimplicialComplex V}
    (C₁ C₂ C₃ : Finset V)
    (g₁ g₂ : Gallery K)
    (hconn₁ : g₁.Connects C₁ C₂)
    (hconn₂ : g₂.Connects C₂ C₃) :
    ∃ g₃ : Gallery K,
      g₃.Connects C₁ C₃ ∧
      g₃.length = g₁.length + g₂.length ∧
      C₂ ∈ g₃.chambers := by

  have hne₁ : g₁.chambers ≠ [] := chambers_ne_nil g₁
  have hne₂ : g₂.chambers ≠ [] := chambers_ne_nil g₂

  have hl₂_head : g₂.chambers.head hne₂ = C₂ := by
    have h := hconn₂.1
    rw [List.head?_eq_some_head hne₂] at h
    exact Option.some_injective _ h
  have hl₂_cons : g₂.chambers = C₂ :: g₂.chambers.tail := by
    rw [← hl₂_head]; exact (List.cons_head_tail hne₂).symm

  let l₃ := g₁.chambers ++ g₂.chambers.tail

  have hne₃ : l₃ ≠ [] := List.append_ne_nil_of_left_ne_nil hne₁ _

  have hlen₃_pos : l₃.length > 0 := List.length_pos_of_ne_nil hne₃

  have hall₃ : ∀ C ∈ l₃, K.IsMaximal C := by
    intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact g₁.all_maximal C h
    · exact g₂.all_maximal C (List.mem_of_mem_tail h)

  have hchain₁ : List.IsChain K.Adjacent g₁.chambers := g₁.adjacent_consecutive
  have hchain₂_tail : List.IsChain K.Adjacent g₂.chambers.tail :=
    g₂.adjacent_consecutive.tail

  have hlink : ∀ x ∈ g₁.chambers.getLast?, ∀ y ∈ g₂.chambers.tail.head?,
      K.Adjacent x y := by
    intro x hx y hy

    have hx_eq : x = C₂ := by
      have h := hconn₁.2
      rw [h] at hx
      exact (Option.some_injective _ hx.symm)


    rw [hx_eq]
    have hchain₂_full : List.IsChain K.Adjacent (C₂ :: g₂.chambers.tail) := by
      rw [← hl₂_cons]; exact g₂.adjacent_consecutive
    exact hchain₂_full.rel_head? hy
  have hchain₃ : List.IsChain K.Adjacent l₃ :=
    hchain₁.append hchain₂_tail hlink

  let g₃ : Gallery K := {
    chambers := l₃
    length_pos := hlen₃_pos
    all_maximal := hall₃
    adjacent_consecutive := hchain₃
  }
  refine ⟨g₃, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    change l₃.head? = some C₁
    show (g₁.chambers ++ g₂.chambers.tail).head? = some C₁
    rw [List.head?_append_of_ne_nil _ hne₁]
    exact hconn₁.1
  ·
    change l₃.getLast? = some C₃
    show (g₁.chambers ++ g₂.chambers.tail).getLast? = some C₃
    by_cases htail : g₂.chambers.tail = []
    ·
      rw [htail, List.append_nil]
      have hC₃_eq : C₃ = C₂ := by
        have hg₂ := hconn₂.2
        rw [hl₂_cons, htail] at hg₂
        simp [List.getLast?] at hg₂
        exact hg₂.symm
      rw [hC₃_eq]
      exact hconn₁.2
    ·
      rw [List.getLast?_append_of_ne_nil _ htail]


      have : g₂.chambers.tail.getLast? = g₂.chambers.getLast? := by
        conv_rhs => rw [hl₂_cons]
        rw [List.getLast?_cons]
        rw [List.getLast?_eq_some_getLast htail]
        simp
      rw [this]
      exact hconn₂.2
  ·
    change l₃.length - 1 = (g₁.chambers.length - 1) + (g₂.chambers.length - 1)
    show (g₁.chambers ++ g₂.chambers.tail).length - 1 =
      (g₁.chambers.length - 1) + (g₂.chambers.length - 1)
    have hlen : (g₁.chambers ++ g₂.chambers.tail).length =
        g₁.chambers.length + g₂.chambers.tail.length := List.length_append
    have hlen₂ : g₂.chambers.length = g₂.chambers.tail.length + 1 := by
      conv_lhs => rw [hl₂_cons]
      simp [List.length_cons]
    have hg₁pos : g₁.chambers.length > 0 := g₁.length_pos
    omega
  ·
    change C₂ ∈ l₃
    exact List.mem_append.mpr (Or.inl (last_mem_of_connects hconn₁))

end Gallery
