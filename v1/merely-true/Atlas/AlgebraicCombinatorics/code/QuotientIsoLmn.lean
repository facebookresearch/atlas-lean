/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.WreathOrbits
import Atlas.AlgebraicCombinatorics.code.YoungLattice

set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn

namespace QuotientIsoLmn

variable {m n : ℕ}

def GridYoungDiagram (m n : ℕ) : Type :=
  {S : Finset (Fin m × Fin n) // WreathOrbits.IsGridYoung S}

instance : PartialOrder (GridYoungDiagram m n) where
  le S T := S.val ⊆ T.val
  le_refl S := Finset.Subset.refl S.val
  le_trans _ _ _ hab hbc := Finset.Subset.trans hab hbc
  le_antisymm S T hST hTS := Subtype.ext (Finset.Subset.antisymm hST hTS)

def lmnToFinset (p : Lmn m n) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun cell => cell.2.val < (p.val cell.1).val

lemma mem_lmnToFinset (p : Lmn m n) (i : Fin m) (j : Fin n) :
    (i, j) ∈ lmnToFinset p ↔ j.val < (p.val i).val := by
  simp [lmnToFinset, Finset.mem_filter]

lemma lmnToFinset_isLeftJustified (p : Lmn m n) :
    WreathOrbits.IsLeftJustified (lmnToFinset p) := by
  intro i j j' hj hlt; rw [mem_lmnToFinset] at hj ⊢; omega

lemma lmnToFinset_rowSize (p : Lmn m n) (i : Fin m) :
    WreathOrbits.rowSize (lmnToFinset p) i = (p.val i).val := by
  unfold WreathOrbits.rowSize
  simp only [lmnToFinset, Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun cell : Fin m × Fin n =>
      (cell.2.val < (p.val cell.1).val) ∧ cell.1 = i)) =
    (Finset.univ.filter (fun cell : Fin m × Fin n =>
      cell.1 = i ∧ cell.2.val < (p.val i).val)) := by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, rfl⟩ => ⟨rfl, h1⟩, fun ⟨rfl, h1⟩ => ⟨h1, rfl⟩⟩
  rw [h1]
  have h2 : (Finset.univ.filter (fun cell : Fin m × Fin n =>
      cell.1 = i ∧ cell.2.val < (p.val i).val)) =
    ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
      j.val < (p.val i).val)).map
      ⟨Prod.mk i, fun a b h => by simpa using h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨rfl, h1⟩ => ⟨b, h1, rfl, rfl⟩,
           fun ⟨j, hlt, ha, hb⟩ => by cases ha; cases hb; exact ⟨rfl, hlt⟩⟩
  rw [h2, Finset.card_map]
  by_cases hn : (p.val i).val < n
  · have : ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
        j.val < (p.val i).val)) = Finset.Iio (⟨(p.val i).val, hn⟩ : Fin n) := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have hpn : (p.val i).val = n := by omega
    have : ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
        j.val < (p.val i).val)) = Finset.univ := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter]; omega
    rw [this, Finset.card_fin, hpn]

lemma lmnToFinset_isGridYoung (p : Lmn m n) :
    WreathOrbits.IsGridYoung (lmnToFinset p) :=
  ⟨lmnToFinset_isLeftJustified p, fun i j hij => by
    rw [lmnToFinset_rowSize, lmnToFinset_rowSize]; exact p.property hij⟩

def lmnToGridYoung (p : Lmn m n) : GridYoungDiagram m n :=
  ⟨lmnToFinset p, lmnToFinset_isGridYoung p⟩

def gridYoungToLmn (S : GridYoungDiagram m n) : Lmn m n :=
  ⟨fun i => ⟨WreathOrbits.rowSize S.val i,
             Nat.lt_succ_of_le (WreathOrbits.rowSize_le S.val i)⟩,
   fun i j hij => S.property.2 hij⟩

lemma gridYoungToLmn_lmnToGridYoung (p : Lmn m n) :
    gridYoungToLmn (lmnToGridYoung p) = p := by
  apply Lmn.ext; intro i; simp only [gridYoungToLmn, lmnToGridYoung]
  ext; exact lmnToFinset_rowSize p i

lemma lmnToGridYoung_gridYoungToLmn (S : GridYoungDiagram m n) :
    lmnToGridYoung (gridYoungToLmn S) = S := by
  apply Subtype.ext; ext ⟨i, j⟩
  show (i, j) ∈ lmnToFinset (gridYoungToLmn S) ↔ (i, j) ∈ S.val
  rw [mem_lmnToFinset]; exact (WreathOrbits.mem_iff_lt_rowSize S.property.1 i j).symm

lemma rowSize_le_of_subset {S T : Finset (Fin m × Fin n)}
    (hST : S ⊆ T) (i : Fin m) :
    WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i := by
  unfold WreathOrbits.rowSize; apply Finset.card_le_card
  intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hST hx.1, hx.2⟩

lemma gridYoungToLmn_le_iff (S T : GridYoungDiagram m n) :
    gridYoungToLmn S ≤ gridYoungToLmn T ↔ S ≤ T := by
  constructor
  · intro h; show S.val ⊆ T.val; intro ⟨i, j⟩ hmem
    rw [WreathOrbits.mem_iff_lt_rowSize S.property.1 i j] at hmem
    rw [WreathOrbits.mem_iff_lt_rowSize T.property.1 i j]
    exact lt_of_lt_of_le hmem (h i)
  · intro h i; exact rowSize_le_of_subset h i

noncomputable def quotientIsoLmn (m n : ℕ) :
    GridYoungDiagram m n ≃o Lmn m n where
  toFun := gridYoungToLmn
  invFun := lmnToGridYoung
  left_inv := lmnToGridYoung_gridYoungToLmn
  right_inv := gridYoungToLmn_lmnToGridYoung
  map_rel_iff' := gridYoungToLmn_le_iff _ _

def wreathSetoid (m n : ℕ) : Setoid (Finset (Fin m × Fin n)) where
  r := WreathOrbits.SameOrbit
  iseqv := {
    refl := fun S => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S S).mpr rfl
    symm := fun {S T} h => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq T S).mpr
      ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h).symm
    trans := fun {S T U} h₁ h₂ => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S U).mpr
      (((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h₁).trans
       ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq T U).mp h₂))
  }

def WreathQuotient (m n : ℕ) : Type := Quotient (wreathSetoid m n)

lemma card_eq_of_sameOrbit {S T : Finset (Fin m × Fin n)}
    (h : WreathOrbits.SameOrbit S T) : S.card = T.card := by
  obtain ⟨g, rfl⟩ := h
  exact (Finset.card_image_of_injective _ g.actOn_injective).symm

def wreathQuotientMk (S : Finset (Fin m × Fin n)) : WreathQuotient m n :=
  @Quotient.mk _ (wreathSetoid m n) S

lemma wreathQuotientMk_eq_iff (S T : Finset (Fin m × Fin n)) :
    wreathQuotientMk S = wreathQuotientMk T ↔ WreathOrbits.SameOrbit S T :=
  Quotient.eq (r := wreathSetoid m n)

lemma actOnSet_subset_of_subset (g : WreathElem m n)
    {S T : Finset (Fin m × Fin n)} (h : S ⊆ T) :
    g.actOnSet S ⊆ g.actOnSet T := by
  intro x hx; simp only [WreathElem.actOnSet, Finset.mem_image] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, h hy, rfl⟩

lemma wreathQuotientMk_actOnSet (g : WreathElem m n) (S : Finset (Fin m × Fin n)) :
    wreathQuotientMk (g.actOnSet S) = wreathQuotientMk S :=
  (wreathQuotientMk_eq_iff _ _).mpr
    ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
      ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mp ⟨g, rfl⟩).symm)

instance wreathQuotientPartialOrder : PartialOrder (WreathQuotient m n) where
  le a b := ∃ (S T : Finset (Fin m × Fin n)),
      wreathQuotientMk S = a ∧ wreathQuotientMk T = b ∧ S ⊆ T
  le_refl a := by
    induction a using Quotient.inductionOn with
    | _ S => exact ⟨S, S, rfl, rfl, Finset.Subset.refl _⟩
  le_trans a b c := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    obtain ⟨g, hg⟩ := (wreathQuotientMk_eq_iff T₁ S₂).mp (hT₁.trans hS₂.symm)
    refine ⟨g.actOnSet S₁, T₂, ?_, hT₂, ?_⟩
    · rw [wreathQuotientMk_actOnSet]; exact hS₁
    · exact (actOnSet_subset_of_subset g hsub₁).trans (hg ▸ Finset.Subset.refl _) |>.trans hsub₂
  le_antisymm a b := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hce : S₁.card = T₂.card :=
      card_eq_of_sameOrbit ((wreathQuotientMk_eq_iff S₁ T₂).mp (hS₁.trans hT₂.symm))
    have : S₁.card = T₁.card := by
      have h1 := Finset.card_le_card hsub₁; have h2 := Finset.card_le_card hsub₂
      have hce2 : T₁.card = S₂.card :=
        card_eq_of_sameOrbit ((wreathQuotientMk_eq_iff T₁ S₂).mp (hT₁.trans hS₂.symm))
      omega
    rw [← hS₁, ← hT₁, Finset.eq_of_subset_of_card_le hsub₁ this.symm.le]

lemma finset_filter_card_eq_sorted_filter_length
    (S : Finset (Fin m × Fin n)) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin m => p (WreathOrbits.rowSize S i))).card =
    ((WreathOrbits.sortedRowSizes S).filter (fun x => decide (p x))).length := by
  classical
  have hmulti := WreathOrbits.sortedRowSizes_multiset_eq S

  have rhs_eq : ((WreathOrbits.sortedRowSizes S).filter (fun x => decide (p x))).length =
      (Multiset.filter p (Finset.univ.val.map (WreathOrbits.rowSize S))).card := by
    rw [← hmulti]; simp [Multiset.filter_coe, Multiset.coe_card]
  rw [rhs_eq]


  have : Multiset.countP p (Finset.univ.val.map (WreathOrbits.rowSize S)) =
      (Finset.univ.filter (fun i : Fin m => p (WreathOrbits.rowSize S i))).card := by
    rw [Multiset.countP_map]; rfl
  rw [← this, Multiset.countP_eq_card_filter]

lemma card_filter_ge_of_sorted {S : Finset (Fin m × Fin n)} (k : Fin m) (v : ℕ)
    (hv : v ≤ (WreathOrbits.sortedRowSizes S).getD k.val 0) :
    k.val + 1 ≤ (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize S i)).card := by
  classical
  have hlen := WreathOrbits.sortedRowSizes_length S
  have hk : k.val < (WreathOrbits.sortedRowSizes S).length := by rw [hlen]; exact k.isLt
  rw [List.getD_eq_getElem _ 0 hk] at hv
  have hsorted := WreathOrbits.sortedRowSizes_pairwise S
  rw [finset_filter_card_eq_sorted_filter_length S (v ≤ ·)]

  have hge : ∀ j : ℕ, j ≤ k.val → (hj : j < (WreathOrbits.sortedRowSizes S).length) →
      v ≤ (WreathOrbits.sortedRowSizes S)[j] := by
    intro j hj hj_lt
    rcases eq_or_lt_of_le hj with rfl | hjk
    · exact hv
    · exact le_trans hv (List.pairwise_iff_getElem.mp hsorted j k.val hj_lt hk hjk)
  have htake_filter : ((WreathOrbits.sortedRowSizes S).take (k.val + 1)).filter
      (fun x => decide (v ≤ x)) = (WreathOrbits.sortedRowSizes S).take (k.val + 1) := by
    rw [List.filter_eq_self]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [decide_eq_true_eq]
    have hj_lt : j < k.val + 1 := by
      rwa [List.length_take, min_eq_left (by omega)] at hj
    have hj_lt_l : j < (WreathOrbits.sortedRowSizes S).length := by omega

    have heq : ((WreathOrbits.sortedRowSizes S).take (k.val + 1))[j]'hj =
        (WreathOrbits.sortedRowSizes S)[j]'hj_lt_l := List.getElem_take ..
    rw [heq]
    exact hge j (by omega) hj_lt_l
  rw [show (WreathOrbits.sortedRowSizes S).filter (fun x => decide (v ≤ x)) =
      ((WreathOrbits.sortedRowSizes S).take (k.val + 1)).filter (fun x => decide (v ≤ x)) ++
      ((WreathOrbits.sortedRowSizes S).drop (k.val + 1)).filter (fun x => decide (v ≤ x)) from by
    rw [← List.filter_append, List.take_append_drop],
    List.length_append, htake_filter, List.length_take, min_eq_left (by omega)]
  omega

lemma card_filter_ge_le_of_sorted {T : Finset (Fin m × Fin n)} (k : Fin m) (v : ℕ)
    (hv : (WreathOrbits.sortedRowSizes T).getD k.val 0 < v) :
    (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize T i)).card ≤ k.val := by
  classical
  have hlen := WreathOrbits.sortedRowSizes_length T
  have hk : k.val < (WreathOrbits.sortedRowSizes T).length := by rw [hlen]; exact k.isLt
  rw [List.getD_eq_getElem _ 0 hk] at hv
  have hsorted := WreathOrbits.sortedRowSizes_pairwise T
  rw [finset_filter_card_eq_sorted_filter_length T (v ≤ ·)]
  have hdrop : ((WreathOrbits.sortedRowSizes T).drop k.val).filter
      (fun x => decide (v ≤ x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hj_bound : k.val + j < (WreathOrbits.sortedRowSizes T).length := by
      rw [List.length_drop] at hj; omega
    simp only [decide_eq_true_eq]
    intro hge_contra
    have helem : (List.drop k.val (WreathOrbits.sortedRowSizes T))[j] =
        (WreathOrbits.sortedRowSizes T)[k.val + j] := List.getElem_drop ..
    rw [helem] at hge_contra
    have : (WreathOrbits.sortedRowSizes T)[k.val + j] ≤
        (WreathOrbits.sortedRowSizes T)[k.val] := by
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj0
      · simp
      · exact List.pairwise_iff_getElem.mp hsorted k.val (k.val + j) hk hj_bound (by omega)
    omega
  rw [show (WreathOrbits.sortedRowSizes T).filter (fun x => decide (v ≤ x)) =
      ((WreathOrbits.sortedRowSizes T).take k.val).filter (fun x => decide (v ≤ x)) ++
      ((WreathOrbits.sortedRowSizes T).drop k.val).filter (fun x => decide (v ≤ x)) from by
    rw [← List.filter_append, List.take_append_drop],
    List.length_append, hdrop, List.length_nil, Nat.add_zero]
  exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)

lemma sortedRowSizes_le_of_rowSize_le (S T : Finset (Fin m × Fin n))
    (h : ∀ i, WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i) (k : Fin m) :
    (WreathOrbits.sortedRowSizes S).getD k.val 0 ≤
    (WreathOrbits.sortedRowSizes T).getD k.val 0 := by
  classical
  by_contra hlt
  push Not at hlt
  set v := (WreathOrbits.sortedRowSizes S).getD k.val 0
  have hcount_S := card_filter_ge_of_sorted k v (le_refl _)
  have hcount_T := card_filter_ge_le_of_sorted k v hlt
  have hsubset : (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize S i)) ⊆
      (Finset.univ.filter (fun i : Fin m => v ≤ WreathOrbits.rowSize T i)) := by
    intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi (h i)
  have := le_trans hcount_S (Finset.card_le_card hsubset)
  omega

lemma canonicalYoung_subset_of_subset {S T : Finset (Fin m × Fin n)}
    (h : S ⊆ T) : WreathOrbits.canonicalYoung S ⊆ WreathOrbits.canonicalYoung T := by
  intro ⟨i, j⟩ hmem
  rw [WreathOrbits.mem_iff_lt_rowSize (WreathOrbits.canonicalYoung_isGridYoung S).1 i j] at hmem
  rw [WreathOrbits.mem_iff_lt_rowSize (WreathOrbits.canonicalYoung_isGridYoung T).1 i j]
  calc j.val < WreathOrbits.rowSize (WreathOrbits.canonicalYoung S) i := hmem
    _ ≤ WreathOrbits.rowSize (WreathOrbits.canonicalYoung T) i := by
        rw [WreathOrbits.rowSize_canonicalYoung, WreathOrbits.rowSize_canonicalYoung]
        exact sortedRowSizes_le_of_rowSize_le S T (fun k => rowSize_le_of_subset h k) i

lemma canonicalYoung_eq_of_sameOrbit {S T : Finset (Fin m × Fin n)}
    (h : WreathOrbits.SameOrbit S T) :
    WreathOrbits.canonicalYoung S = WreathOrbits.canonicalYoung T :=
  WreathOrbits.gridYoung_unique
    (WreathOrbits.canonicalYoung_isGridYoung S)
    (WreathOrbits.canonicalYoung_isGridYoung T)
    (by rw [WreathOrbits.rowSizeMultiset_canonicalYoung, WreathOrbits.rowSizeMultiset_canonicalYoung]
        exact (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h)

lemma canonicalYoung_sameOrbit (S : Finset (Fin m × Fin n)) :
    WreathOrbits.SameOrbit S (WreathOrbits.canonicalYoung S) :=
  (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S _).mpr
    (WreathOrbits.rowSizeMultiset_canonicalYoung S).symm

noncomputable def wreathQuotientToGridYoung :
    WreathQuotient m n → GridYoungDiagram m n :=
  Quotient.lift
    (fun S => (⟨WreathOrbits.canonicalYoung S,
               WreathOrbits.canonicalYoung_isGridYoung S⟩ : GridYoungDiagram m n))
    (fun S T (h : WreathOrbits.SameOrbit S T) =>
      Subtype.ext (canonicalYoung_eq_of_sameOrbit h))

def gridYoungToWreathQuotient : GridYoungDiagram m n → WreathQuotient m n :=
  fun S => wreathQuotientMk S.val

lemma gridYoungToWreathQuotient_wreathQuotientToGridYoung :
    ∀ q : WreathQuotient m n,
    gridYoungToWreathQuotient (wreathQuotientToGridYoung q) = q := by
  intro q; induction q using Quotient.inductionOn with
  | _ S =>
    show wreathQuotientMk (WreathOrbits.canonicalYoung S) = wreathQuotientMk S
    exact (wreathQuotientMk_eq_iff _ _).mpr
      ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
        (WreathOrbits.rowSizeMultiset_canonicalYoung S))

lemma wreathQuotientToGridYoung_gridYoungToWreathQuotient :
    ∀ D : GridYoungDiagram m n,
    wreathQuotientToGridYoung (gridYoungToWreathQuotient D) = D := by
  intro ⟨D, hD⟩; apply Subtype.ext
  exact WreathOrbits.gridYoung_unique (WreathOrbits.canonicalYoung_isGridYoung D) hD
    (WreathOrbits.rowSizeMultiset_canonicalYoung D)

lemma wreathQuotientToGridYoung_le_iff (a b : WreathQuotient m n) :
    wreathQuotientToGridYoung a ≤ wreathQuotientToGridYoung b ↔ a ≤ b := by
  constructor
  · intro h
    induction a using Quotient.inductionOn with | _ S =>
    induction b using Quotient.inductionOn with | _ T =>
    refine ⟨WreathOrbits.canonicalYoung S, WreathOrbits.canonicalYoung T, ?_, ?_, h⟩
    · exact (wreathQuotientMk_eq_iff _ _).mpr
        ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
          (WreathOrbits.rowSizeMultiset_canonicalYoung S))
    · exact (wreathQuotientMk_eq_iff _ _).mpr
        ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
          (WreathOrbits.rowSizeMultiset_canonicalYoung T))
  · intro h
    obtain ⟨S', T', hS', hT', hsub⟩ := h
    induction a using Quotient.inductionOn with | _ S =>
    induction b using Quotient.inductionOn with | _ T =>
    change (WreathOrbits.canonicalYoung S) ⊆ (WreathOrbits.canonicalYoung T)
    have hSo : WreathOrbits.SameOrbit S S' :=
      (wreathQuotientMk_eq_iff S S').mp (hS' ▸ rfl)
    have hTo : WreathOrbits.SameOrbit T T' :=
      (wreathQuotientMk_eq_iff T T').mp (hT' ▸ rfl)
    rw [canonicalYoung_eq_of_sameOrbit hSo, canonicalYoung_eq_of_sameOrbit hTo]
    exact canonicalYoung_subset_of_subset hsub

noncomputable def wreathQuotientIsoGridYoung (m n : ℕ) :
    WreathQuotient m n ≃o GridYoungDiagram m n where
  toFun := wreathQuotientToGridYoung
  invFun := gridYoungToWreathQuotient
  left_inv := gridYoungToWreathQuotient_wreathQuotientToGridYoung
  right_inv := wreathQuotientToGridYoung_gridYoungToWreathQuotient
  map_rel_iff' := wreathQuotientToGridYoung_le_iff _ _

noncomputable def wreathQuotientIsoLmn (m n : ℕ) :
    WreathQuotient m n ≃o Lmn m n :=
  (wreathQuotientIsoGridYoung m n).trans (quotientIsoLmn m n)

end QuotientIsoLmn
