/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

namespace WreathOrbits

variable {m n : ℕ}

def rowSize (S : Finset (Fin m × Fin n)) (i : Fin m) : ℕ :=
  (S.filter (fun p => p.1 = i)).card

def rowSizeMultiset (S : Finset (Fin m × Fin n)) : Multiset ℕ :=
  Finset.univ.val.map (rowSize S)

structure WreathElem (m n : ℕ) where
  σ : Equiv.Perm (Fin m)
  τ : Fin m → Equiv.Perm (Fin n)

def WreathElem.actOn (g : WreathElem m n) (p : Fin m × Fin n) : Fin m × Fin n :=
  (g.σ p.1, g.τ p.1 p.2)

def WreathElem.actOnSet (g : WreathElem m n) (S : Finset (Fin m × Fin n)) :
    Finset (Fin m × Fin n) :=
  S.image g.actOn

def SameOrbit (S T : Finset (Fin m × Fin n)) : Prop :=
  ∃ g : WreathElem m n, g.actOnSet S = T

lemma WreathElem.actOn_injective (g : WreathElem m n) : Function.Injective g.actOn := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  simp only [WreathElem.actOn, Prod.mk.injEq] at h
  have hi : i₁ = i₂ := g.σ.injective h.1
  subst hi; exact Prod.ext rfl (by exact (g.τ i₁).injective h.2)

lemma rowSize_actOnSet (g : WreathElem m n) (S : Finset (Fin m × Fin n)) (i : Fin m) :
    rowSize (g.actOnSet S) (g.σ i) = rowSize S i := by
  simp only [rowSize, WreathElem.actOnSet]
  have : (S.image g.actOn).filter (fun p => p.1 = g.σ i) =
         (S.filter (fun p => p.1 = i)).image g.actOn := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, WreathElem.actOn, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨x, y⟩, hxy, rfl, rfl⟩, h⟩
      refine ⟨⟨x, y⟩, ⟨hxy, g.σ.injective h⟩, rfl, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hxy, hxi⟩, rfl, rfl⟩
      exact ⟨⟨⟨x, y⟩, hxy, rfl, rfl⟩, by rw [hxi]⟩
  rw [this, Finset.card_image_of_injective _ g.actOn_injective]

def rowCols (S : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n) :=
  (S.filter (fun p => p.1 = i)).image Prod.snd

lemma mem_rowCols_iff (S : Finset (Fin m × Fin n)) (i : Fin m) (j : Fin n) :
    j ∈ rowCols S i ↔ (i, j) ∈ S := by
  constructor
  · intro hj
    simp only [rowCols, Finset.mem_image, Finset.mem_filter] at hj
    obtain ⟨⟨a, b⟩, ⟨hab, ha_eq⟩, hb_eq⟩ := hj
    simpa [← ha_eq, ← hb_eq] using hab
  · intro hj
    simp only [rowCols, Finset.mem_image, Finset.mem_filter]
    exact ⟨(i, j), ⟨hj, rfl⟩, rfl⟩

lemma rowCols_card (S : Finset (Fin m × Fin n)) (i : Fin m) :
    (rowCols S i).card = rowSize S i := by
  simp only [rowCols, rowSize]
  rw [Finset.card_image_of_injOn]
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  exact Prod.ext (by rw [(Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2]) heq

lemma exists_perm_image_eq (A B : Finset (Fin n)) (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin n), A.image σ = B := by
  classical
  let e' : {x : Fin n // x ∈ A} ≃ {x : Fin n // x ∈ B} := Finset.equivOfCardEq h
  refine ⟨e'.extendSubtype, ?_⟩
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Equiv.extendSubtype_mem e' a ha
  · intro hx
    refine ⟨(e'.symm ⟨x, hx⟩).val, (e'.symm ⟨x, hx⟩).prop, ?_⟩
    rw [Equiv.extendSubtype_apply_of_mem e' _ (e'.symm ⟨x, hx⟩).prop]
    simp

lemma fiber_card_eq (S T : Finset (Fin m × Fin n))
    (h : rowSizeMultiset S = rowSizeMultiset T) (v : ℕ) :
    Fintype.card {i : Fin m // rowSize S i = v} =
    Fintype.card {i : Fin m // rowSize T i = v} := by
  suffices key : ∀ (f : Fin m → ℕ),
      Fintype.card {i : Fin m // f i = v} =
      Multiset.count v (Finset.univ.val.map f) by
    rw [key, key]; exact congr_arg _ h
  intro f
  rw [Fintype.card_subtype, Multiset.count_map,
      show Multiset.filter (fun a => v = f a) Finset.univ.val =
           (Finset.univ.filter (fun a => v = f a)).val from rfl,
      Finset.card_val]
  congr 1; ext x; simp [eq_comm]

lemma rowSizeMultiset_eq_of_sameOrbit (S T : Finset (Fin m × Fin n))
    (h : SameOrbit S T) : rowSizeMultiset S = rowSizeMultiset T := by
  obtain ⟨g, rfl⟩ := h
  simp only [rowSizeMultiset]
  conv_rhs =>
    rw [show Finset.univ.val.map (rowSize (g.actOnSet S)) =
      (Finset.univ.val.map g.σ.symm).map (rowSize S) from by
        rw [Multiset.map_map]; congr 1; ext i
        simp only [Function.comp, ← rowSize_actOnSet g S (g.σ.symm i), Equiv.apply_symm_apply]]
  congr 1; ext x; simp

lemma sameOrbit_of_rowSizeMultiset_eq (S T : Finset (Fin m × Fin n))
    (h : rowSizeMultiset S = rowSizeMultiset T) : SameOrbit S T := by
  classical

  let σ : Equiv.Perm (Fin m) := Equiv.ofFiberEquiv (f := rowSize S) (g := rowSize T)
    (fun v => Fintype.equivOfCardEq (fiber_card_eq S T h v))
  have hσ : ∀ i, rowSize S i = rowSize T (σ i) :=
    fun i => (Equiv.ofFiberEquiv_map _ i).symm

  have hrow_eq : ∀ i, (rowCols S i).card = (rowCols T (σ i)).card := by
    intro i; rw [rowCols_card, rowCols_card, hσ]
  choose τ hτ using fun i => exists_perm_image_eq _ _ (hrow_eq i)

  refine ⟨⟨σ, τ⟩, ?_⟩
  ext ⟨a, b⟩
  simp only [WreathElem.actOnSet, Finset.mem_image, WreathElem.actOn, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl, rfl⟩
    exact (mem_rowCols_iff T (σ i) (τ i j)).mp
      (by rw [← hτ i]; exact Finset.mem_image_of_mem _ ((mem_rowCols_iff S i j).mpr hij))
  · intro hab
    let i := σ.symm a
    have hi : σ i = a := Equiv.apply_symm_apply σ a
    have hb : b ∈ (rowCols S i).image (τ i) := by
      rw [hτ, hi]; exact (mem_rowCols_iff T a b).mpr hab
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨⟨i, j⟩, (mem_rowCols_iff S i j).mp hj, hi, rfl⟩

theorem sameOrbit_iff_rowSizeMultiset_eq (S T : Finset (Fin m × Fin n)) :
    SameOrbit S T ↔ rowSizeMultiset S = rowSizeMultiset T :=
  ⟨rowSizeMultiset_eq_of_sameOrbit S T, sameOrbit_of_rowSizeMultiset_eq S T⟩

lemma rowSize_le (S : Finset (Fin m × Fin n)) (i : Fin m) : rowSize S i ≤ n := by
  unfold rowSize
  calc (S.filter (fun p => p.1 = i)).card
      ≤ (Finset.univ.filter (fun p : Fin m × Fin n => p.1 = i)).card := by
        apply Finset.card_le_card; intro x hx; simp [Finset.mem_filter] at hx ⊢; exact hx.2
    _ = n := by
        have : (Finset.univ.filter (fun p : Fin m × Fin n => p.1 = i)) =
               (Finset.univ : Finset (Fin n)).map
                 ⟨fun j => (i, j), fun a b h => by simp at h; exact h⟩ := by
          ext ⟨a, b⟩; simp [Finset.mem_filter, Finset.mem_map]; exact eq_comm
        rw [this, Finset.card_map, Finset.card_fin]

def IsLeftJustified (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ (i : Fin m) (j j' : Fin n), (i, j) ∈ S → j' < j → (i, j') ∈ S

def IsGridYoung (S : Finset (Fin m × Fin n)) : Prop :=
  IsLeftJustified S ∧ Antitone (rowSize S)

lemma mem_iff_lt_rowSize {S : Finset (Fin m × Fin n)} (hS : IsLeftJustified S)
    (i : Fin m) (j : Fin n) : (i, j) ∈ S ↔ j.val < rowSize S i := by
  unfold rowSize
  set Ri := S.filter (fun p => p.1 = i) with hRi_def
  constructor
  ·
    intro hj
    have hmem : ∀ (k : Fin n), k ≤ j → (i, k) ∈ Ri := by
      intro k hk
      simp only [hRi_def]
      apply Finset.mem_filter.mpr
      constructor
      · rcases eq_or_lt_of_le hk with h | h
        · rw [h]; exact hj
        · exact hS i j k hj h
      · rfl
    have hcard : (Finset.Iic j).card ≤ Ri.card := by
      have hf : ∀ k ∈ Finset.Iic j, (fun k => (i, k)) k ∈ Ri :=
        fun k hk => hmem k (Finset.mem_Iic.mp hk)
      have hinj : Set.InjOn (fun k : Fin n => (i, k)) (Finset.Iic j : Set (Fin n)) :=
        fun a _ b _ hab => by simp [Prod.ext_iff] at hab; exact hab
      calc (Finset.Iic j).card
          ≤ ((Finset.Iic j).image (fun k => (i, k))).card := by
            rw [Finset.card_image_of_injOn hinj]
        _ ≤ Ri.card := Finset.card_le_card (by
            intro x hx; simp [Finset.mem_image] at hx
            obtain ⟨k, hk, rfl⟩ := hx; exact hf k (Finset.mem_Iic.mpr hk))
    rw [Fin.card_Iic] at hcard; omega
  ·
    intro hlt
    by_contra hj
    have hnotin : ∀ j' : Fin n, j ≤ j' → (i, j') ∉ S := by
      intro j' hle hmem
      rcases eq_or_lt_of_le hle with heq | hlt'
      · exact hj (heq ▸ hmem)
      · exact hj (hS i j' j hmem hlt')
    have hsub : Ri ⊆ (Finset.Iio j).image (fun k => (i, k)) := by
      intro ⟨a, b⟩ hmem'
      simp only [hRi_def, Finset.mem_filter] at hmem'
      simp only [Finset.mem_image, Finset.mem_Iio]
      exact ⟨b, by_contra (fun hle => hnotin b (not_lt.mp hle) (hmem'.2 ▸ hmem'.1)),
             by simp [hmem'.2]⟩
    have hcard : Ri.card ≤ j.val := by
      calc Ri.card
          ≤ ((Finset.Iio j).image (fun k => (i, k))).card := Finset.card_le_card hsub
        _ ≤ (Finset.Iio j).card := Finset.card_image_le
        _ = j.val := Fin.card_Iio j
    omega

theorem leftJustified_eq_of_rowSize_eq {S T : Finset (Fin m × Fin n)}
    (hS : IsLeftJustified S) (hT : IsLeftJustified T)
    (h : ∀ i, rowSize S i = rowSize T i) : S = T := by
  ext ⟨i, j⟩
  rw [mem_iff_lt_rowSize hS, mem_iff_lt_rowSize hT, h]

lemma map_finRange_pairwise_ge {f : Fin m → ℕ} (hf : Antitone f) :
    ((List.finRange m).map f).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  exact (List.pairwise_le_finRange m).imp (fun hab => hf hab)

lemma univ_val_eq_coe_finRange :
    (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := by
  ext x; simp

theorem antitone_eq_of_multiset_eq {f g : Fin m → ℕ} (hf : Antitone f) (hg : Antitone g)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : f = g := by
  have hpw_f := map_finRange_pairwise_ge hf
  have hpw_g := map_finRange_pairwise_ge hg
  have hmulti : (↑((List.finRange m).map f) : Multiset ℕ) = ↑((List.finRange m).map g) := by
    simp only [← Multiset.map_coe, ← univ_val_eq_coe_finRange, h]
  have hperm := Multiset.coe_eq_coe.mp hmulti
  have heq : (List.finRange m).map f = (List.finRange m).map g :=
    hperm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) hpw_f hpw_g
  funext i
  exact (List.map_eq_map_iff.mp heq) i (List.mem_finRange i)

theorem gridYoung_unique {S T : Finset (Fin m × Fin n)}
    (hS : IsGridYoung S) (hT : IsGridYoung T)
    (h : rowSizeMultiset S = rowSizeMultiset T) : S = T := by
  apply leftJustified_eq_of_rowSize_eq hS.1 hT.1
  exact fun i => congr_fun (antitone_eq_of_multiset_eq hS.2 hT.2 h) i

noncomputable def sortedRowSizes (S : Finset (Fin m × Fin n)) : List ℕ :=
  (Finset.univ.val.map (rowSize S)).sort (· ≥ ·)

lemma sortedRowSizes_length (S : Finset (Fin m × Fin n)) :
    (sortedRowSizes S).length = m := by
  simp [sortedRowSizes]

lemma sortedRowSizes_pairwise (S : Finset (Fin m × Fin n)) :
    (sortedRowSizes S).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort ..

lemma sortedRowSizes_multiset_eq (S : Finset (Fin m × Fin n)) :
    ↑(sortedRowSizes S) = Finset.univ.val.map (rowSize S) :=
  Multiset.sort_eq ..

lemma sortedRowSizes_le (S : Finset (Fin m × Fin n)) (k : ℕ)
    (hk : k < (sortedRowSizes S).length) : (sortedRowSizes S)[k] ≤ n := by
  have hmem : (sortedRowSizes S)[k] ∈ (Finset.univ.val.map (rowSize S)) := by
    rw [← sortedRowSizes_multiset_eq]; exact Multiset.mem_coe.mpr (List.getElem_mem hk)
  rw [Multiset.mem_map] at hmem
  obtain ⟨i, -, heq⟩ := hmem
  rw [← heq]; exact rowSize_le S i

lemma getD_le_n (S : Finset (Fin m × Fin n)) (i : Fin m) :
    (sortedRowSizes S).getD i.val 0 ≤ n := by
  have hlen : i.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i.isLt
  rw [List.getD_eq_getElem _ 0 hlen]
  exact sortedRowSizes_le S i.val hlen

noncomputable def canonicalYoung (S : Finset (Fin m × Fin n)) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p => p.2.val < (sortedRowSizes S).getD p.1.val 0

lemma mem_canonicalYoung (S : Finset (Fin m × Fin n)) (i : Fin m) (j : Fin n) :
    (i, j) ∈ canonicalYoung S ↔ j.val < (sortedRowSizes S).getD i.val 0 := by
  simp [canonicalYoung, Finset.mem_filter]

lemma canonicalYoung_isLeftJustified (S : Finset (Fin m × Fin n)) :
    IsLeftJustified (canonicalYoung S) := by
  intro i j j' hj hlt
  rw [mem_canonicalYoung] at hj ⊢; omega

lemma filter_lt_card (k : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < (k : ℕ))).card =
      k.val := by
  by_cases hk : k.val < n
  · have : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < (k : ℕ))) =
           Finset.Iio (⟨k.val, hk⟩ : Fin n) := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have hkn : k.val = n := by omega
    have : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < (k : ℕ))) = Finset.univ := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter]; omega
    rw [this, Finset.card_fin, hkn]

lemma rowSize_canonicalYoung (S : Finset (Fin m × Fin n)) (i : Fin m) :
    rowSize (canonicalYoung S) i = (sortedRowSizes S).getD i.val 0 := by
  simp only [rowSize, canonicalYoung]; rw [Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun p : Fin m × Fin n =>
    p.2.val < (sortedRowSizes S).getD p.1.val 0 ∧ p.1 = i)) =
    (Finset.univ.filter (fun p : Fin m × Fin n =>
      p.1 = i ∧ p.2.val < (sortedRowSizes S).getD i.val 0)) := by
    ext ⟨a, b⟩; simp [Finset.mem_filter]
    exact ⟨fun ⟨h1, rfl⟩ => ⟨rfl, h1⟩, fun ⟨rfl, h1⟩ => ⟨h1, rfl⟩⟩
  rw [h1]
  have h2 : (Finset.univ.filter (fun p : Fin m × Fin n =>
      p.1 = i ∧ p.2.val < (sortedRowSizes S).getD i.val 0)) =
    ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
      j.val < (sortedRowSizes S).getD i.val 0)).map
      ⟨Prod.mk i, fun a b h => by simpa using h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨rfl, h1⟩ => ⟨b, h1, rfl, rfl⟩,
           fun ⟨j, hlt, ha, hb⟩ => by cases ha; cases hb; exact ⟨rfl, hlt⟩⟩
  rw [h2, Finset.card_map]
  exact filter_lt_card ⟨_, Nat.lt_succ_of_le (getD_le_n S i)⟩

lemma canonicalYoung_antitone (S : Finset (Fin m × Fin n)) :
    Antitone (rowSize (canonicalYoung S)) := by
  intro i₁ i₂ h
  rw [rowSize_canonicalYoung, rowSize_canonicalYoung]
  have hsort := sortedRowSizes_pairwise S
  have h1 : i₁.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i₁.isLt
  have h2 : i₂.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i₂.isLt
  rw [List.getD_eq_getElem _ 0 h1, List.getD_eq_getElem _ 0 h2]
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact (List.pairwise_iff_getElem.mp hsort i₁.val i₂.val h1 h2 hlt)

lemma canonicalYoung_isGridYoung (S : Finset (Fin m × Fin n)) :
    IsGridYoung (canonicalYoung S) :=
  ⟨canonicalYoung_isLeftJustified S, canonicalYoung_antitone S⟩

lemma finRange_map_getD (l : List ℕ) (hl : l.length = m) :
    (List.finRange m).map (fun i : Fin m => l.getD i.val 0) = l := by
  apply List.ext_getElem (by simp [hl])
  intro k hk1 hk2
  simp [List.getElem_map, List.getElem_finRange]
  rw [List.getElem?_eq_getElem hk2]; simp

lemma map_getD_eq_coe (l : List ℕ) (hl : l.length = m) :
    Finset.univ.val.map (fun i : Fin m => l.getD i.val 0) = ↑l := by
  have : (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := by ext x; simp
  rw [this, Multiset.map_coe, finRange_map_getD l hl]

lemma rowSizeMultiset_canonicalYoung (S : Finset (Fin m × Fin n)) :
    rowSizeMultiset (canonicalYoung S) = rowSizeMultiset S := by
  simp only [rowSizeMultiset]
  have h1 : Finset.univ.val.map (rowSize (canonicalYoung S)) =
            Finset.univ.val.map (fun i : Fin m => (sortedRowSizes S).getD i.val 0) := by
    congr 1; funext i; exact rowSize_canonicalYoung S i
  rw [h1, map_getD_eq_coe _ (sortedRowSizes_length S), sortedRowSizes_multiset_eq]

theorem exists_gridYoung_of_rowSizeMultiset (S : Finset (Fin m × Fin n)) :
    ∃ T : Finset (Fin m × Fin n), IsGridYoung T ∧
      rowSizeMultiset T = rowSizeMultiset S :=
  ⟨canonicalYoung S, canonicalYoung_isGridYoung S, rowSizeMultiset_canonicalYoung S⟩

theorem existsUnique_gridYoung_sameOrbit (S : Finset (Fin m × Fin n)) :
    ∃! T : Finset (Fin m × Fin n), IsGridYoung T ∧ SameOrbit S T := by

  obtain ⟨T, hTy, hTm⟩ := exists_gridYoung_of_rowSizeMultiset S
  refine ⟨T, ⟨hTy, (sameOrbit_iff_rowSizeMultiset_eq S T).mpr hTm.symm⟩, ?_⟩

  intro T' ⟨hT'y, hT'o⟩
  have hT'o' := (sameOrbit_iff_rowSizeMultiset_eq S T').mp hT'o
  exact gridYoung_unique hT'y hTy (hT'o'.symm.trans hTm.symm)

end WreathOrbits
