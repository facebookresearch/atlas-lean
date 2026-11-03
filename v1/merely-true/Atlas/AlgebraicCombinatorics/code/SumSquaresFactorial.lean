/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.HasseWalkFormula
import Atlas.AlgebraicCombinatorics.code.WalkTypeCount
import Mathlib.Combinatorics.Young.YoungDiagram

set_option autoImplicit false

open scoped Nat
open HasseWalkFormula HasseWalks

section YoungDiagramFinset

lemma young_cell_fst_lt {μ : YoungDiagram} {i j : ℕ}
    (h : (i, j) ∈ μ) : i < μ.card := by
  have hmem : ∀ r ∈ Finset.range (i + 1), (r, (0 : ℕ)) ∈ μ.cells :=
    fun r hr => by
      simp only [Finset.mem_range] at hr
      exact μ.up_left_mem (by omega) (Nat.zero_le j) h
  have hinj : Set.InjOn (fun r => (r, (0 : ℕ))) (↑(Finset.range (i + 1)) : Set ℕ) :=
    fun a _ b _ hab => (Prod.mk.inj hab).1
  have hle : (Finset.range (i + 1)).card ≤ μ.cells.card :=
    Finset.card_le_card_of_injOn (fun r => (r, (0 : ℕ)))
      (fun r hr => hmem r hr) hinj
  simpa [Finset.card_range] using hle

lemma young_cell_snd_lt {μ : YoungDiagram} {i j : ℕ}
    (h : (i, j) ∈ μ) : j < μ.card := by
  have hmem : ∀ c ∈ Finset.range (j + 1), ((0 : ℕ), c) ∈ μ.cells :=
    fun c hc => by
      simp only [Finset.mem_range] at hc
      exact μ.up_left_mem (Nat.zero_le i) (by omega) h
  have hinj : Set.InjOn (fun c => ((0 : ℕ), c)) (↑(Finset.range (j + 1)) : Set ℕ) :=
    fun a _ b _ hab => (Prod.mk.inj hab).2
  have hle : (Finset.range (j + 1)).card ≤ μ.cells.card :=
    Finset.card_le_card_of_injOn (fun c => ((0 : ℕ), c))
      (fun c hc => hmem c hc) hinj
  simpa [Finset.card_range] using hle

lemma YoungDiagram.cells_subset_range_sq (μ : YoungDiagram) :
    μ.cells ⊆ Finset.range μ.card ×ˢ Finset.range μ.card := by
  intro ⟨i, j⟩ hcell
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨young_cell_fst_lt hcell, young_cell_snd_lt hcell⟩

lemma finite_youngDiagrams_of_size (n : ℕ) :
    Set.Finite {μ : YoungDiagram | μ.card = n} := by
  have hinj : Set.InjOn YoungDiagram.cells {μ : YoungDiagram | μ.card = n} := by
    intro a _ b _ h
    rwa [YoungDiagram.ext_iff]
  have hmaps : Set.MapsTo YoungDiagram.cells
      {μ : YoungDiagram | μ.card = n}
      ↑((Finset.range n ×ˢ Finset.range n).powerset : Finset (Finset (ℕ × ℕ))) := by
    intro μ (hμ : μ.card = n)
    simp only [Finset.mem_coe, Finset.mem_powerset]
    rw [← hμ]; exact μ.cells_subset_range_sq
  exact Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)

noncomputable def youngDiagramsOfSize (n : ℕ) : Finset YoungDiagram :=
  (finite_youngDiagrams_of_size n).toFinset

@[simp]
lemma mem_youngDiagramsOfSize {n : ℕ} {μ : YoungDiagram} :
    μ ∈ youngDiagramsOfSize n ↔ μ.card = n := by
  simp [youngDiagramsOfSize, Set.Finite.mem_toFinset]

end YoungDiagramFinset

def dnUn (n : ℕ) : List HStep :=
  List.replicate n HStep.U ++ List.replicate n HStep.D

lemma WalkTypeCount.applyStepWord_append (w₁ w₂ : List HStep)
    (f : YoungDiagram →₀ ℤ) :
    WalkTypeCount.applyStepWord (w₁ ++ w₂) f =
      WalkTypeCount.applyStepWord w₂ (WalkTypeCount.applyStepWord w₁ f) := by
  induction w₁ generalizing f with
  | nil => simp [WalkTypeCount.applyStepWord]
  | cons s rest ih =>
    cases s with
    | U => simp only [List.cons_append, WalkTypeCount.applyStepWord]; exact ih _
    | D => simp only [List.cons_append, WalkTypeCount.applyStepWord]; exact ih _




theorem hasseWalkCount_allD_to_bot_eq_numSYT (n : ℕ) (μ : YoungDiagram) (hμ : μ.card = n) :
    Nat.card (HasseWalk (List.replicate n HStep.D) μ ⊥) = numSYT μ := by
  subst hμ
  unfold HasseWalkFormula.numSYT
  apply Nat.card_congr
  have hlen : (List.replicate μ.card HStep.D).length = μ.card := List.length_replicate
  have hcast : (List.replicate μ.card HStep.D).length + 1 = μ.card + 1 := by omega
  refine {
    toFun := fun w => ?_
    invFun := fun s => ?_
    left_inv := fun w => ?_
    right_inv := fun s => ?_
  }
  ·
    refine ⟨fun i => w.diagram (Fin.cast hcast.symm ⟨μ.card - i.val, by omega⟩), ?_, ?_,
      fun i => ?_⟩
    ·
      simp only [Nat.sub_zero]
      convert w.target_eq using 2
      exact Fin.ext (by simp [Fin.cast, hlen])
    ·
      simp only [Nat.sub_self]
      convert w.start_eq using 2
    ·
      have hi_lt : μ.card - i.val - 1 < (List.replicate μ.card HStep.D).length := by
        simp only [hlen]; omega
      have hi_eq : (List.replicate μ.card HStep.D)[μ.card - i.val - 1]'hi_lt = HStep.D := by
        simp [List.getElem_replicate]
      have hsd := w.step_down ⟨μ.card - i.val - 1, hi_lt⟩ hi_eq
      convert hsd using 2
      exact Fin.ext (by dsimp [Fin.cast]; omega)
  ·
    obtain ⟨chain, hstart, htarget, hstep⟩ := s
    refine ⟨fun i => chain ⟨μ.card - (Fin.cast hcast i).val, by omega⟩, ?_, ?_,
      fun i hi_u => ?_, fun i hi_d => ?_⟩
    ·
      convert htarget using 2
    ·
      convert hstart using 2
      exact Fin.ext (by simp [Fin.cast, hlen])
    ·
      exact absurd hi_u (by simp [List.getElem_replicate])
    ·
      have hi_lt_n : μ.card - i.val - 1 < μ.card := by
        have := i.isLt; simp only [hlen] at this; omega
      have := hstep ⟨μ.card - i.val - 1, hi_lt_n⟩
      convert this using 2
      exact Fin.ext (by dsimp [Fin.cast]; omega)
  ·
    rcases w with ⟨d, s, t, su, sd⟩
    simp only [HasseWalk.mk.injEq]
    funext ⟨i, hi⟩
    exact congr_arg d (Fin.ext (by simp [Fin.cast]; omega))
  ·
    obtain ⟨chain, h1, h2, h3⟩ := s
    exact Subtype.ext (funext fun ⟨i, hi⟩ => congr_arg chain (Fin.ext (by
      simp [Fin.cast]; omega)))


theorem walkTypeCount_allU_eq_numSYT (n : ℕ) (μ : YoungDiagram) (hμ : μ.card = n) :
    WalkTypeCount.walkTypeCount (List.replicate n HStep.U) μ = numSYT μ := by
  subst hμ

  suffices h : WalkTypeCount.walkTypeCount (List.replicate μ.card HStep.U) μ =
    HasseWalkFormula.upWalkCount μ.card μ by
    rw [h]; unfold HasseWalkFormula.upWalkCount HasseWalkFormula.numSYT; rfl

  unfold WalkTypeCount.walkTypeCount HasseWalkFormula.upWalkCount
  apply Nat.card_congr
  have hlen : (List.replicate μ.card HStep.U).length = μ.card := List.length_replicate
  refine {
    toFun := fun w => ?_
    invFun := fun s => ?_
    left_inv := fun w => ?_
    right_inv := fun s => ?_
  }
  ·
    refine ⟨fun i => w.diagram (Fin.cast (by omega) i), w.start_eq, ?_, fun i => ?_⟩
    ·
      convert w.target_eq using 2
      exact Fin.ext (by simp [hlen])
    ·
      have hi_lt : i.val < (List.replicate μ.card HStep.U).length := by omega
      have hi_eq : (List.replicate μ.card HStep.U)[i.val]'hi_lt = HStep.U := by
        simp [List.getElem_replicate]
      have := w.step_up (⟨i.val, hi_lt⟩ : Fin (List.replicate μ.card HStep.U).length) hi_eq
      convert this using 2
  ·
    obtain ⟨chain, hstart, htarget, hstep⟩ := s
    refine ⟨fun i => chain (Fin.cast (by omega) i), hstart, ?_, fun i hi_u => ?_, fun i hi_d => ?_⟩
    ·
      convert htarget using 2
      exact Fin.ext (by simp [hlen])
    ·
      have hi_lt : i.val < μ.card := by omega
      have := hstep (⟨i.val, hi_lt⟩ : Fin μ.card)
      convert this using 2
    ·
      exact absurd hi_d (by simp [List.getElem_replicate])
  ·
    rcases w with ⟨d, s, t, su, sd⟩
    simp only [HasseWalk.mk.injEq]
    funext i; exact congr_arg d (Fin.ext rfl)
  ·
    obtain ⟨chain, h1, h2, h3⟩ := s
    exact Subtype.ext (funext fun i => congr_arg chain (Fin.ext rfl))



lemma dnUn_length (n : ℕ) : (dnUn n).length = n + n := by
  simp [dnUn]

lemma dnUn_getElem_U {n : ℕ} (i : Fin (dnUn n).length) (hlt : i.val < n) :
    (dnUn n)[i] = HStep.U := by
  show (dnUn n)[i.val] = HStep.U
  simp only [dnUn]
  rw [List.getElem_append_left (by simp; omega)]
  simp

lemma dnUn_getElem_D {n : ℕ} (i : Fin (dnUn n).length) (hge : n ≤ i.val) :
    (dnUn n)[i] = HStep.D := by
  show (dnUn n)[i.val] = HStep.D
  simp only [dnUn]
  rw [List.getElem_append_right (by simp; omega)]
  simp

lemma dnUn_downPositions_mem {n : ℕ} (i : Fin (dnUn n).length) :
    i ∈ WalkTypeCount.downPositions (dnUn n) ↔ n ≤ i.val := by
  simp only [WalkTypeCount.downPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra h
    have h' : i.val < n := by omega
    have hU := dnUn_getElem_U i h'
    rw [hU] at hi
    exact absurd hi (by decide)
  · intro hi
    exact dnUn_getElem_D i hi

lemma dnUn_take {n : ℕ} (i : Fin (dnUn n).length) (hge : n ≤ i.val) :
    (dnUn n).take i.val = List.replicate n HStep.U ++ List.replicate (i.val - n) HStep.D := by
  have hlen : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
  simp only [dnUn]
  rw [List.take_append]
  simp only [List.length_replicate, List.take_replicate]
  congr 1
  · congr 1; omega
  · congr 1; omega

lemma dnUn_numURight_D {n : ℕ} (i : Fin (dnUn n).length) (hge : n ≤ i.val) :
    WalkTypeCount.numURight (dnUn n) i = n := by
  simp only [WalkTypeCount.numURight, dnUn_take i hge, List.filter_append,
    List.filter_replicate, List.length_append]
  simp (config := { decide := true })

lemma dnUn_numDRight_D {n : ℕ} (i : Fin (dnUn n).length) (hge : n ≤ i.val) :
    WalkTypeCount.numDRight (dnUn n) i = i.val - n := by
  simp only [WalkTypeCount.numDRight, dnUn_take i hge, List.filter_append,
    List.filter_replicate, List.length_append]
  simp (config := { decide := true })

lemma dnUn_downStepProduct_eq_factorial (n : ℕ) :
    WalkTypeCount.downStepProduct (dnUn n) = ↑(n.factorial) := by
  unfold WalkTypeCount.downStepProduct
  suffices hfact : (↑(n.factorial) : ℤ) = ∏ i ∈ Finset.range n, (↑(n - i) : ℤ) by
    rw [hfact]
    apply Finset.prod_nbij (fun i => i.val - n)
    · intro i hi
      rw [Finset.mem_range]
      have hge := (dnUn_downPositions_mem i).mp hi
      have hlt : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
      omega
    · intro a ha b hb (hab : a.val - n = b.val - n)
      have hage := (dnUn_downPositions_mem a).mp ha
      have hbge := (dnUn_downPositions_mem b).mp hb
      exact Fin.ext (by omega)
    · intro k hk
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      have hkl : k + n < (dnUn n).length := by rw [dnUn_length]; omega
      exact ⟨⟨k + n, hkl⟩, (dnUn_downPositions_mem _).mpr (by simp), by simp⟩
    · intro i hi
      have hge := (dnUn_downPositions_mem i).mp hi
      rw [dnUn_numURight_D i hge, dnUn_numDRight_D i hge]
      have hlt : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
      omega


  have key : ∀ m : ℕ, (↑(m.factorial) : ℤ) = ∏ i ∈ Finset.range m, (↑i + 1 : ℤ) := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
      push_cast; ring
  rw [key n]
  apply Finset.prod_nbij (fun i => n - 1 - i)
  · intro i hi; simp at hi ⊢; omega
  · intro a ha b hb hab
    simp at ha hb
    show a = b
    have : n - 1 - a = n - 1 - b := hab
    omega
  · intro k hk
    simp at hk ⊢
    exact ⟨n - 1 - k, by omega, by omega⟩
  · intro i hi
    simp at hi
    have h : n - (n - 1 - i) = i + 1 := by omega
    rw [h]; push_cast; ring

lemma dnUn_runningLevel_le (n k : ℕ) (hk : k ≤ n) :
    WalkTypeCount.runningLevel (dnUn n) k = (k : ℤ) := by
  simp only [WalkTypeCount.runningLevel, dnUn]
  have htake : (List.replicate n HStep.U ++ List.replicate n HStep.D).take k =
    List.replicate k HStep.U := by
    rw [List.take_append]
    simp only [List.length_replicate, List.take_replicate]
    have h1 : min k n = k := min_eq_left hk
    have h2 : k - n = 0 := Nat.sub_eq_zero_of_le hk
    simp [h1, h2]
  rw [htake]
  simp only [List.filter_replicate]
  simp (config := { decide := true })

lemma dnUn_runningLevel_ge (n k : ℕ) (hge : n ≤ k) (hle : k ≤ n + n) :
    WalkTypeCount.runningLevel (dnUn n) k = (2 * n - k : ℤ) := by
  simp only [WalkTypeCount.runningLevel, dnUn]
  have htake : (List.replicate n HStep.U ++ List.replicate n HStep.D).take k =
    List.replicate n HStep.U ++ List.replicate (k - n) HStep.D := by
    rw [List.take_append]
    simp only [List.length_replicate, List.take_replicate]
    congr 1
    · congr 1; omega
    · congr 1; omega
  rw [htake]
  simp only [List.filter_append, List.filter_replicate, List.length_append]
  simp (config := { decide := true })
  omega

lemma isValidStepWord_dnUn (n : ℕ) : WalkTypeCount.IsValidStepWord (dnUn n) 0 := by
  constructor
  ·
    have hlen : (dnUn n).length = n + n := dnUn_length n
    rw [hlen, dnUn_runningLevel_ge n (n + n) (Nat.le_add_right n n) (le_refl _)]
    push_cast; omega

  ·
    intro k hk
    have hlen : (dnUn n).length = n + n := dnUn_length n
    rw [hlen] at hk
    by_cases h : k ≤ n
    · rw [dnUn_runningLevel_le n k h]
      exact Nat.cast_nonneg k
    · rw [dnUn_runningLevel_ge n k (by omega) hk]
      omega



