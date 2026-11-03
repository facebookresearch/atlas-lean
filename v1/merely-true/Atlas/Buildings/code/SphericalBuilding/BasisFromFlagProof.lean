/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnFlagToFrame
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.List.Pairwise

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}


/-- A strictly monotone map $g : \mathrm{Fin}(n+1) \to \mathbb{N}$ with $g(0) = 0$ and
$g(n) = n$ must be the identity. -/
lemma strictMono_nat_id {n : ℕ}
    (g : Fin (n + 1) → ℕ) (hg : StrictMono g)
    (_h0 : g ⟨0, Nat.zero_lt_succ n⟩ = 0)
    (hn : g ⟨n, Nat.lt_succ_of_le le_rfl⟩ = n) :
    ∀ j : Fin (n + 1), g j = j.val := by
  have hlb : ∀ (j : ℕ) (hj : j < n + 1), j ≤ g ⟨j, hj⟩ := by
    intro j hj
    induction j with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      have hm : m < n + 1 := by omega
      have := ih hm
      have := hg (show (⟨m, hm⟩ : Fin (n + 1)) < ⟨m + 1, hj⟩ from Fin.mk_lt_mk.mpr (by omega))
      omega
  have hub : ∀ (j : ℕ) (hj : j < n + 1), g ⟨j, hj⟩ ≤ j := by
    intro j hj
    by_contra hc
    push_neg at hc
    suffices hprop : g ⟨j, hj⟩ + (n - j) ≤ g ⟨n, by omega⟩ by omega
    have key : ∀ (k : ℕ) (hk : k < n + 1), j ≤ k →
        g ⟨j, hj⟩ + (k - j) ≤ g ⟨k, hk⟩ := by
      intro k hk hjk
      induction k with
      | zero =>
        have : j = 0 := by omega
        subst this
        simp
      | succ m ihm =>
        by_cases hjm : j ≤ m
        · have hm : m < n + 1 := by omega
          have h1 := ihm hm hjm
          have h2 := hg (show (⟨m, hm⟩ : Fin (n + 1)) < ⟨m + 1, hk⟩ from
            Fin.mk_lt_mk.mpr (by omega))
          omega
        · have : j = m + 1 := by omega
          subst this
          simp
    exact key n (by omega) (by omega)
  intro ⟨j, hj⟩
  exact Nat.le_antisymm (hub j hj) (hlb j hj)


/-- If no vector in a finite family is in the span of its predecessors (under the natural
ordering of `Fin m`), then the family is linearly independent. -/
lemma linearIndependent_of_not_mem_span_predecessors
    {V : Type*} [AddCommGroup V] [Module k V]
    {m : ℕ} (v : Fin m → V)
    (h : ∀ j : Fin m, v j ∉ Submodule.span k (v '' {i : Fin m | i.val < j.val})) :
    LinearIndependent k v := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ p ih =>
    rw [linearIndependent_fin_succ']
    constructor
    · apply ih
      intro ⟨j, hj⟩ hmem
      apply h ⟨j, by omega⟩
      apply Submodule.span_mono _ hmem
      rintro x ⟨i, hi, hx⟩
      simp [Fin.init] at hx
      exact ⟨i.castSucc, hi, hx⟩
    · intro hmem
      apply h (Fin.last p)
      apply Submodule.span_mono _ hmem
      rintro x ⟨i, rfl⟩
      simp [Fin.init]
      exact ⟨i.castSucc, i.isLt, rfl⟩


/-- Proof of `BasisFromFlagHyp`: from any maximal proper flag $0 \subsetneq V_1 \subsetneq
\cdots \subsetneq V_{n-1} \subsetneq k^n$, extract $n$ lines $L_i$ that decompose $k^n$ as
$k^n = L_1 \oplus \cdots \oplus L_n$ and such that each $V_j$ is a join of some subset of
the $L_i$ — i.e.\ extract an adapted basis. -/
noncomputable def basisFromFlagHyp (k : Type*) [Field k] (n : ℕ) :
    BasisFromFlagHyp k n where
  extract := fun chain hchain hlen hproper => by
    classical

    by_cases hn : n = 0
    · subst hn
      refine ⟨Fin.elim0, fun i => i.elim0, ?_, ?_, ?_⟩
      · exact iSupIndep_subsingleton _
      · rw [iSup_of_empty]
        apply Submodule.eq_top_of_finrank_eq; simp
      · intro V hV; simp_all
    have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn


    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Vec k n) := inferInstance


    let ext : Fin (n + 1) → Submodule k (Vec k n) := fun j =>
      if hj : j.val = 0 then ⊥
      else if _ : j.val ≤ n - 1 then chain.get ⟨j.val - 1, by omega⟩
      else ⊤

    have hext : StrictMono ext := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [Fin.lt_def] at hab
      simp only [ext]
      split_ifs with h1 h2 h3 h4
      · omega
      · exact bot_lt_iff_ne_bot.mpr
          (hproper _ (List.get_mem chain ⟨b - 1, by omega⟩)).1
      · exact bot_lt_top
      · omega
      · exact (List.isChain_iff_pairwise.mp hchain).rel_get_of_lt
          (by simp [Fin.lt_def]; omega)
      · exact lt_top_iff_ne_top.mpr
          (hproper _ (List.get_mem chain ⟨a - 1, by omega⟩)).2
      · omega
      · omega
      · omega

    have hext_last : ext ⟨n, by omega⟩ = ⊤ := by
      simp only [ext]
      simp [show (n : ℕ) ≠ 0 from by omega, show ¬(n ≤ n - 1) from by omega]

    have hext_succ : ∀ (j : ℕ) (hj : j < n - 1),
        ext ⟨j + 1, by omega⟩ = chain.get ⟨j, by omega⟩ := by
      intro j hj; simp only [ext]
      simp [show j + 1 ≤ n - 1 from by omega]


    have hgap : ∀ i : Fin n, ext ⟨i.val, by omega⟩ < ext ⟨i.val + 1, by omega⟩ :=
      fun i => hext (by simp [Fin.lt_def])

    let v : Fin n → Vec k n := fun i =>
      (SetLike.exists_of_lt (hgap i)).choose
    have hv_upper : ∀ i, v i ∈ ext ⟨i.val + 1, by omega⟩ :=
      fun i => (SetLike.exists_of_lt (hgap i)).choose_spec.1
    have hv_lower : ∀ i, v i ∉ ext ⟨i.val, by omega⟩ :=
      fun i => (SetLike.exists_of_lt (hgap i)).choose_spec.2

    have hv_ne : ∀ i, v i ≠ 0 := by
      intro i hvi; apply hv_lower i; rw [hvi]
      exact (ext ⟨i.val, by omega⟩).zero_mem


    have hv_in_ext : ∀ (i : Fin n) (j : ℕ) (hj : j < n + 1),
        i.val + 1 ≤ j → v i ∈ ext ⟨j, hj⟩ := by
      intro i j hj hij
      exact hext.monotone (show (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≤ ⟨j, hj⟩ from
        Fin.mk_le_mk.mpr (by omega)) (hv_upper i)


    have hspan_le : ∀ (j : ℕ) (hj : j < n + 1),
        Submodule.span k (v '' {i : Fin n | i.val < j}) ≤ ext ⟨j, hj⟩ := by
      intro j hj; apply Submodule.span_le.mpr
      rintro x ⟨i, (hi : i.val < j), rfl⟩
      exact hv_in_ext i j hj (by omega)


    have hv_indep : LinearIndependent k v := by
      apply linearIndependent_of_not_mem_span_predecessors
      intro j hmem
      exact hv_lower j (hspan_le j.val (by omega) hmem)


    have hfinrank_ext : ∀ (j : ℕ) (hj : j < n + 1),
        Module.finrank k (ext ⟨j, hj⟩) = j := by
      intro j hj
      have key := strictMono_nat_id
        (fun i => Module.finrank k (ext i))
        (fun a b hab => Submodule.finrank_lt_finrank_of_lt (hext hab))
        (by show Module.finrank k (ext ⟨0, _⟩) = 0; simp [ext])
        (by show Module.finrank k (ext ⟨n, _⟩) = n
            rw [hext_last, finrank_top, Module.finrank_fin_fun])
      exact key ⟨j, hj⟩


    let lines : Fin n → Submodule k (Vec k n) := fun i => k ∙ v i

    have h_dim : ∀ i, Module.finrank k (lines i) = 1 :=
      fun i => finrank_span_singleton (hv_ne i)

    have h_indep : iSupIndep lines :=
      hv_indep.iSupIndep_span_singleton

    have h_span : ⨆ i, lines i = ⊤ := by
      have hsupr : (⨆ i, lines i) = Submodule.span k (Set.range v) := by
        have : (⨆ i, lines i) = ⨆ i, Submodule.span k {v i} := rfl
        rw [this, ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range]
      rw [hsupr]
      exact hv_indep.span_eq_top_of_card_eq_finrank'
        (by rw [Fintype.card_fin, Module.finrank_fin_fun])


    have h_compat : ∀ V ∈ chain, ∃ S : Finset (Fin n), V = ⨆ j ∈ S, lines j := by
      intro V hV
      obtain ⟨⟨idx_val, hidx_lt⟩, hidx_eq⟩ := List.mem_iff_get.mp hV
      have hidx_bound : idx_val < n - 1 := by omega
      have hV_eq_ext : V = ext ⟨idx_val + 1, by omega⟩ := by
        rw [← hidx_eq]; exact (hext_succ idx_val hidx_bound).symm
      let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val ≤ idx_val)
      use S


      let w : Fin (idx_val + 1) → Vec k n := fun j => v ⟨j.val, by omega⟩
      have hw_indep : LinearIndependent k w := by
        apply hv_indep.comp
        intro ⟨a, _⟩ ⟨b, _⟩ hab
        have := Fin.val_eq_of_eq hab
        simp at this
        exact Fin.ext this
      have hspan_w_le :
          Submodule.span k (Set.range w) ≤ ext ⟨idx_val + 1, by omega⟩ := by
        apply Submodule.span_le.mpr
        rintro x ⟨⟨j, hj⟩, rfl⟩
        exact hv_in_ext ⟨j, by omega⟩ (idx_val + 1) (by omega)
          (show (⟨j, (by omega : j < n)⟩ : Fin n).val + 1 ≤ idx_val + 1 by simp; omega)
      have hfinrank_span :
          Module.finrank k (Submodule.span k (Set.range w)) = idx_val + 1 := by
        rw [finrank_span_eq_card hw_indep, Fintype.card_fin]
      have hfinrank_ext_idx :
          Module.finrank k (ext ⟨idx_val + 1, by omega⟩) = idx_val + 1 :=
        hfinrank_ext (idx_val + 1) (by omega)
      have hspan_eq :
          Submodule.span k (Set.range w) = ext ⟨idx_val + 1, by omega⟩ := by
        apply Submodule.eq_of_le_of_finrank_le hspan_w_le
        rw [hfinrank_ext_idx, hfinrank_span]

      rw [hV_eq_ext, ← hspan_eq]
      apply le_antisymm

      · apply Submodule.span_le.mpr
        rintro x ⟨⟨j, hj⟩, rfl⟩
        have hmem_S : (⟨j, by omega⟩ : Fin n) ∈ S := by
          simp [S, Finset.mem_filter]; omega
        have hmem_line : w ⟨j, hj⟩ ∈ lines ⟨j, by omega⟩ :=
          Submodule.mem_span_singleton_self _
        exact (le_iSup₂ (f := fun j (_ : j ∈ S) => lines j)
          ⟨j, by omega⟩ hmem_S) hmem_line

      · apply iSup₂_le; intro j hj
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        apply Submodule.span_mono
        intro x hx; rw [Set.mem_singleton_iff.mp hx]
        exact ⟨⟨j.val, by omega⟩, rfl⟩

    exact ⟨lines, h_dim, h_indep, h_span, h_compat⟩

end GLnBuilding
