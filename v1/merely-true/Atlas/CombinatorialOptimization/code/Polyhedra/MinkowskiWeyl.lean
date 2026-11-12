/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

open Finset Matrix BigOperators

lemma exists_t_of_fm_constraints {m : ℕ} (c : Fin m → ℝ) (d : Fin m → ℝ)
    (hfm_zero : ∀ k : Fin m, c k = 0 → 0 ≤ d k)
    (hfm_pair : ∀ i j : Fin m, c i > 0 → c j < 0 →
      (-c j) * d i + (c i) * d j ≥ 0) :
    ∃ t : ℝ, ∀ i : Fin m, c i * t ≤ d i := by
  by_cases hP : ∃ i : Fin m, c i > 0
  · obtain ⟨i₀, hi₀⟩ := hP
    let P := Finset.univ.filter (fun i : Fin m => c i > 0)
    have hP_ne : P.Nonempty := ⟨i₀, by simp [P]; exact hi₀⟩
    use P.inf' hP_ne (fun i => d i / c i)
    intro i
    rcases lt_trichotomy (c i) 0 with hci | hci | hci
    · suffices h : d i / c i ≤ P.inf' hP_ne (fun j => d j / c j) by
        have := mul_le_mul_of_nonpos_left h hci.le
        rwa [mul_div_cancel₀ (d i) (ne_of_lt hci)] at this
      apply Finset.le_inf'
      intro j hj; simp [P] at hj
      have hpair := hfm_pair j i hj hci
      have key : d i * c j ≥ d j * c i := by nlinarith
      have hprod_neg : c i * c j < 0 := mul_neg_of_neg_of_pos hci hj
      have hci_ne : c i ≠ 0 := ne_of_lt hci
      have hcj_ne : c j ≠ 0 := ne_of_gt hj
      suffices hsub : d i / c i - d j / c j ≤ 0 by linarith
      have heq : d i / c i - d j / c j = (d i * c j - d j * c i) / (c i * c j) := by
        field_simp
      rw [heq]
      exact div_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hprod_neg)
    · rw [hci, zero_mul]; exact hfm_zero i hci
    · have hi_in_P : i ∈ P := by simp [P]; exact hci
      have h := Finset.inf'_le (fun j => d j / c j) hi_in_P
      calc c i * P.inf' hP_ne (fun j => d j / c j)
          ≤ c i * (d i / c i) := mul_le_mul_of_nonneg_left h hci.le
        _ = d i := mul_div_cancel₀ (d i) (ne_of_gt hci)
  · push_neg at hP
    by_cases hN : ∃ j : Fin m, c j < 0
    · obtain ⟨j₀, hj₀⟩ := hN
      let N := Finset.univ.filter (fun i : Fin m => c i < 0)
      have hN_ne : N.Nonempty := ⟨j₀, by simp [N]; exact hj₀⟩
      use N.sup' hN_ne (fun i => d i / c i)
      intro i
      rcases eq_or_lt_of_le (hP i) with hci | hci
      · have hci' : c i = 0 := by linarith
        rw [hci', zero_mul]; exact hfm_zero i hci'
      · have hi_in_N : i ∈ N := by simp [N]; exact hci
        have h := Finset.le_sup' (fun j => d j / c j) hi_in_N
        calc c i * N.sup' hN_ne (fun j => d j / c j)
            ≤ c i * (d i / c i) := mul_le_mul_of_nonpos_left h hci.le
          _ = d i := mul_div_cancel₀ (d i) (ne_of_lt hci)
    · push_neg at hN
      use 0
      intro i
      have hci : c i = 0 := le_antisymm (hP i) (hN i)
      rw [hci, zero_mul]; exact hfm_zero i hci

lemma polyhedron_projection {n m : ℕ}
    (C : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (d : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      {y : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, ∀ i : Fin m,
        (∑ j, C i j * y j) + c i * t ≤ d i} =
      {y : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m', ∑ j, A' i j * (y j) ≤ b' i} := by
  classical
  let I := { i : Fin m // c i = 0 } ⊕ ({ i : Fin m // c i > 0 } × { j : Fin m // c j < 0 })
  let m' := Fintype.card I
  let e : I ≃ Fin m' := Fintype.equivFin I
  let A' : Matrix (Fin m') (Fin n) ℝ := fun idx j =>
    match e.symm idx with
    | Sum.inl ⟨i, _⟩ => C i j
    | Sum.inr (⟨i, _⟩, ⟨k, _⟩) => (-c k) * C i j + (c i) * C k j
  let b' : Fin m' → ℝ := fun idx =>
    match e.symm idx with
    | Sum.inl ⟨i, _⟩ => d i
    | Sum.inr (⟨i, _⟩, ⟨k, _⟩) => (-c k) * d i + (c i) * d k
  refine ⟨m', A', b', ?_⟩
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht⟩ idx
    show ∑ j : Fin n, A' idx j * y j ≤ b' idx
    rcases h : e.symm idx with ⟨i, hi⟩ | ⟨⟨i, hi⟩, ⟨k, hk⟩⟩
    · have hA_eq : ∀ j, A' idx j = C i j := by
        intro j; simp only [A']; rw [show e.symm idx = Sum.inl ⟨i, hi⟩ from h]
      have hb_eq : b' idx = d i := by
        simp only [b']; rw [show e.symm idx = Sum.inl ⟨i, hi⟩ from h]
      rw [show ∑ j, A' idx j * y j = ∑ j, C i j * y j from by
        congr 1; funext j; rw [hA_eq j]]
      rw [hb_eq]
      have := ht i
      rw [hi, zero_mul, add_zero] at this
      exact this
    · have hA_eq : ∀ j, A' idx j = (-c k) * C i j + (c i) * C k j := by
        intro j; simp only [A']; rw [show e.symm idx = Sum.inr (⟨i, hi⟩, ⟨k, hk⟩) from h]
      have hb_eq : b' idx = (-c k) * d i + (c i) * d k := by
        simp only [b']; rw [show e.symm idx = Sum.inr (⟨i, hi⟩, ⟨k, hk⟩) from h]
      rw [show ∑ j, A' idx j * y j = ∑ j, ((-c k) * C i j + (c i) * C k j) * y j from by
        congr 1; funext j; rw [hA_eq j]]
      rw [hb_eq]
      have hti := ht i
      have htk := ht k
      have lhs_eq : ∑ j, ((-c k) * C i j + (c i) * C k j) * y j =
        (-c k) * (∑ j, C i j * y j) + (c i) * (∑ j, C k j * y j) := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1 <;> (rw [Finset.mul_sum]; congr 1; funext j; ring)
      rw [lhs_eq]
      have h1 : (-c k) * (∑ j, C i j * y j) ≤ (-c k) * (d i - c i * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
      have h2 : (c i) * (∑ j, C k j * y j) ≤ (c i) * (d k - c k * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
      linarith [h1, h2]
  · intro hy
    suffices h : ∃ t : ℝ, ∀ i : Fin m, c i * t ≤ d i - ∑ j, C i j * y j by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, fun i => by linarith [ht i]⟩
    apply exists_t_of_fm_constraints c (fun i => d i - ∑ j, C i j * y j)
    · intro k hk
      have := hy (e (Sum.inl ⟨k, hk⟩ : I))
      simp only [A', b'] at this
      rw [show e.symm (e (Sum.inl ⟨k, hk⟩ : I)) = Sum.inl ⟨k, hk⟩ from by simp] at this
      linarith [this]
    · intro i j hi hj
      have := hy (e (Sum.inr (⟨i, hi⟩, ⟨j, hj⟩) : I))
      simp only [A', b'] at this
      rw [show e.symm (e (Sum.inr (⟨i, hi⟩, ⟨j, hj⟩) : I)) =
        Sum.inr (⟨i, hi⟩, ⟨j, hj⟩) from by simp] at this
      have lhs_eq : ∑ l, ((-c j) * C i l + c i * C j l) * (y l) =
        (-c j) * (∑ l, C i l * y l) + c i * (∑ l, C j l * y l) := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1 <;> (rw [Finset.mul_sum]; congr 1; funext l; ring)
      linarith [lhs_eq]

lemma convexHull_polyhedron_point_eq_projection {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hP : ∃ x : EuclideanSpace ℝ (Fin n), ∀ i, ∑ j, A i j * (x j) ≤ b i)
    (hbdd : ∀ d : EuclideanSpace ℝ (Fin n), (∀ i, ∑ j, A i j * d j ≤ 0) → d = 0) :
    ∃ (m₁ : ℕ) (C : Matrix (Fin m₁) (Fin n) ℝ) (c : Fin m₁ → ℝ) (d : Fin m₁ → ℝ),
      convexHull ℝ ({x : EuclideanSpace ℝ (Fin n) | ∀ i, ∑ j, A i j * (x j) ≤ b i} ∪ {v}) =
      {y : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, ∀ i : Fin m₁,
        (∑ j, C i j * y j) + c i * t ≤ d i} := by
  classical
  let P := {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, ∑ j, A i j * (x j) ≤ b i}
  let m₁ := m + 2
  let C : Matrix (Fin m₁) (Fin n) ℝ := fun idx j =>
    if h : idx.val < m then A ⟨idx.val, h⟩ j else 0
  let cv : Fin m₁ → ℝ := fun idx =>
    if h : idx.val < m then (∑ j, A ⟨idx.val, h⟩ j * (v j)) - b ⟨idx.val, h⟩
    else if idx.val = m then -1 else 1
  let dv : Fin m₁ → ℝ := fun idx =>
    if h : idx.val < m then ∑ j, A ⟨idx.val, h⟩ j * (v j)
    else if idx.val = m then 0 else 1
  refine ⟨m₁, C, cv, dv, ?_⟩
  have hPconv : Convex ℝ P := by
    intro x hx z hz a c₁ ha hc₁ hac i
    simp only [Set.mem_setOf_eq] at *
    have hlin : ∑ j, A i j * (a • x + c₁ • z) j =
      a * (∑ j, A i j * x j) + c₁ * (∑ j, A i j * z j) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1; funext j; ring
    rw [hlin]
    have h3 : (a + c₁) * b i = b i := by rw [hac, one_mul]
    linarith [mul_le_mul_of_nonneg_left (hx i) ha, mul_le_mul_of_nonneg_left (hz i) hc₁]
  have hPne : P.Nonempty := hP
  have hconv_eq : convexHull ℝ (P ∪ {v}) = convexJoin ℝ P {v} :=
    Convex.convexHull_union hPconv (convex_singleton v) hPne ⟨v, rfl⟩
  ext y; simp only [Set.mem_setOf_eq]
  constructor
  ·
    intro hy
    rw [hconv_eq, convexJoin_singleton_right] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hxP, hy_seg⟩ := hy
    rw [segment_eq_image ℝ x v] at hy_seg
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hxy⟩ := hy_seg
    have hy_eq : y = (1 - θ) • x + θ • v := hxy.symm
    refine ⟨1 - θ, fun idx => ?_⟩
    simp only [C, cv, dv]
    by_cases hidx : idx.val < m
    · simp only [hidx, dite_true]
      subst hy_eq
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hlhs : ∑ j, A ⟨idx.val, hidx⟩ j * ((1 - θ) * x j + θ * v j) =
        (1 - θ) * (∑ j, A ⟨idx.val, hidx⟩ j * x j) + θ * (∑ j, A ⟨idx.val, hidx⟩ j * v j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1; funext j; ring
      rw [hlhs]
      nlinarith [hxP (⟨idx.val, hidx⟩ : Fin m)]
    · simp only [hidx, dite_false]
      by_cases hidx2 : idx.val = m
      · simp only [hidx2, ite_true, zero_mul, Finset.sum_const_zero, zero_add, neg_mul, one_mul]
        linarith
      · simp only [hidx2, ite_false, zero_mul, Finset.sum_const_zero, zero_add, one_mul]
        linarith
  ·
    intro ⟨t, ht⟩
    have ht_ge : 0 ≤ t := by
      have h := ht ⟨m, by omega⟩
      simp only [C, cv, dv, show ¬(m < m) from lt_irrefl m, dite_false,
        ite_true, zero_mul, Finset.sum_const_zero, zero_add, neg_mul, one_mul] at h
      linarith
    have ht_le : t ≤ 1 := by
      have h := ht ⟨m + 1, by omega⟩
      simp only [C, cv, dv, show ¬(m + 1 < m) from by omega, dite_false,
        show ¬(m + 1 = m) from by omega, ite_false, zero_mul,
        Finset.sum_const_zero, zero_add, one_mul] at h
      linarith

    have hconstr : ∀ i : Fin m, ∑ j, A i j * (y j) +
        ((∑ j, A i j * (v j)) - b i) * t ≤ ∑ j, A i j * (v j) := by
      intro i
      have h := ht ⟨i.val, by omega⟩
      simp only [C, cv, dv, show i.val < m from i.isLt, dite_true] at h
      convert h using 2
    rw [hconv_eq, convexJoin_singleton_right]
    simp only [Set.mem_iUnion]
    by_cases ht0 : t = 0
    · have hd : ∀ i : Fin m, ∑ j, A i j * ((y - v) j) ≤ 0 := by
        intro i
        have := hconstr i
        simp only [ht0, mul_zero, add_zero] at this
        simp only [PiLp.sub_apply]
        have heq : ∑ j, A i j * (y j - v j) = (∑ j, A i j * y j) - (∑ j, A i j * v j) := by
          rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring
        linarith [heq]
      have heq := hbdd (y - v) hd
      have hy_eq : y = v := eq_of_sub_eq_zero heq
      obtain ⟨x₀, hx₀P⟩ := hPne
      refine ⟨x₀, hx₀P, ?_⟩; rw [hy_eq]; exact right_mem_segment ℝ x₀ v

    · have ht_pos : 0 < t := lt_of_le_of_ne ht_ge (Ne.symm ht0)
      let x := v + t⁻¹ • (y - v)
      have hxP : x ∈ P := by
        intro i
        simp only [x, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        have hineq := hconstr i
        have hlhs : ∑ j : Fin n, A i j * (v j + t⁻¹ * (y j - v j)) =
          (∑ j, A i j * v j) + t⁻¹ * (∑ j, A i j * (y j - v j)) := by
          have : ∀ j, A i j * (v j + t⁻¹ * (y j - v j)) =
            A i j * v j + t⁻¹ * (A i j * (y j - v j)) := by intro j; ring
          simp_rw [this, Finset.sum_add_distrib, Finset.mul_sum]
        rw [hlhs]
        have hdiff : (∑ j, A i j * (y j - v j)) = (∑ j, A i j * y j) - (∑ j, A i j * v j) := by
          rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring
        have hkey : (∑ j, A i j * (y j - v j)) ≤ (b i - ∑ j, A i j * v j) * t := by
          linarith [hdiff]
        have h1 : t⁻¹ * ∑ j, A i j * (y j - v j) ≤ t⁻¹ * ((b i - ∑ j, A i j * v j) * t) :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr ht_pos))
        have h2 : t⁻¹ * ((b i - ∑ j, A i j * v j) * t) = b i - ∑ j, A i j * v j := by
          rw [mul_comm (b i - _) t, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht_pos), one_mul]
        linarith [h1, h2]
      refine ⟨x, hxP, ?_⟩
      rw [segment_eq_image ℝ x v]
      refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
      ext j
      simp only [x, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring

lemma polyhedron_convex_hull_point {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hP : ∃ x : EuclideanSpace ℝ (Fin n), ∀ i, ∑ j, A i j * (x j) ≤ b i)
    (hbdd : ∀ d : EuclideanSpace ℝ (Fin n), (∀ i, ∑ j, A i j * d j ≤ 0) → d = 0) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      (convexHull ℝ ({x : EuclideanSpace ℝ (Fin n) | ∀ i, ∑ j, A i j * (x j) ≤ b i} ∪ {v})) =
      {x | ∀ i : Fin m', ∑ j, A' i j * (x j) ≤ b' i} := by
  obtain ⟨m₁, C, c, d, hconv⟩ := convexHull_polyhedron_point_eq_projection A b v hP hbdd
  obtain ⟨m', A', b', hproj⟩ := polyhedron_projection C c d
  exact ⟨m', A', b', by rw [hconv, hproj]⟩

lemma polytope_trivial_recession_cone {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n)))
    (hS : S.Nonempty) {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hAb : (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) =
      {x | ∀ i : Fin m, ∑ j, A i j * (x j) ≤ b i}) :
    ∀ d : EuclideanSpace ℝ (Fin n), (∀ i, ∑ j, A i j * d j ≤ 0) → d = 0 := by
  intro d hd
  by_contra hne
  have hSne := hS
  obtain ⟨x₀, hx₀⟩ := hSne
  have hx₀_P : x₀ ∈ {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, ∑ j, A i j * (x j) ≤ b i} := by
    rw [← hAb]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hx₀)
  have h_in : ∀ r : ℝ, 0 ≤ r → (x₀ + r • d) ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))) := by
    intro r hr; rw [hAb]; intro i
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have : ∑ j, A i j * (x₀ j + r * d j) = (∑ j, A i j * x₀ j) + r * (∑ j, A i j * d j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; funext j; ring
    rw [this]; nlinarith [hx₀_P i, hd i]
  have ⟨j₀, hj₀⟩ : ∃ j : Fin n, d j ≠ 0 := by
    by_contra hall; push_neg at hall; apply hne; ext j; simp; exact hall j
  set ub := S.sup' hS (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) with hub_def
  set lb := S.inf' hS (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) with hlb_def
  have hup : ∀ p ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))), p j₀ ≤ ub := by
    apply convexHull_min
    · intro s hs
      exact Finset.le_sup' (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) (Finset.mem_coe.mp hs)
    · intro a ha b₁ hb₁ t₁ t₂ ht₁ ht₂ ht
      show (t₁ • a + t₂ • b₁) j₀ ≤ ub
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have ha' : a j₀ ≤ ub := ha
      have hb₁' : b₁ j₀ ≤ ub := hb₁
      have h1 : t₁ * a j₀ ≤ t₁ * ub := mul_le_mul_of_nonneg_left ha' ht₁
      have h2 : t₂ * b₁ j₀ ≤ t₂ * ub := mul_le_mul_of_nonneg_left hb₁' ht₂
      linarith [show t₁ * ub + t₂ * ub = ub from by have := congr_arg (· * ub) ht; simp [add_mul, one_mul] at this; linarith]

  have hlow : ∀ p ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))), lb ≤ p j₀ := by
    apply convexHull_min
    · intro s hs
      exact Finset.inf'_le (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) (Finset.mem_coe.mp hs)
    · intro a ha b₁ hb₁ t₁ t₂ ht₁ ht₂ ht
      show lb ≤ (t₁ • a + t₂ • b₁) j₀
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have ha' : lb ≤ a j₀ := ha
      have hb₁' : lb ≤ b₁ j₀ := hb₁
      have h1 : t₁ * lb ≤ t₁ * a j₀ := mul_le_mul_of_nonneg_left ha' ht₁
      have h2 : t₂ * lb ≤ t₂ * b₁ j₀ := mul_le_mul_of_nonneg_left hb₁' ht₂
      linarith [show t₁ * lb + t₂ * lb = lb from by have := congr_arg (· * lb) ht; simp [add_mul, one_mul] at this; linarith]

  rcases lt_or_gt_of_ne hj₀ with hd_neg | hd_pos
  · have hr : (0 : ℝ) ≤ (lb - x₀ j₀ - 1) / d j₀ :=
      div_nonneg_iff.mpr (Or.inr ⟨by linarith [Finset.inf'_le (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) hx₀], hd_neg.le⟩)
    have hmem := h_in _ hr
    have hbnd := hlow _ hmem
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hbnd
    have hcalc : (lb - x₀ j₀ - 1) / d j₀ * d j₀ = lb - x₀ j₀ - 1 :=
      div_mul_cancel₀ _ (ne_of_lt hd_neg)
    linarith
  · have hr : (0 : ℝ) ≤ (ub - x₀ j₀ + 1) / d j₀ :=
      div_nonneg (by linarith [Finset.le_sup' (fun s : EuclideanSpace ℝ (Fin n) => (s j₀ : ℝ)) hx₀]) hd_pos.le
    have hmem := h_in _ hr
    have hbnd := hup _ hmem
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hbnd
    have hcalc : (ub - x₀ j₀ + 1) / d j₀ * d j₀ = ub - x₀ j₀ + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hd_pos)
    linarith

theorem minkowski_weyl {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty) :
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) =
      {x | ∀ i, ∑ j, A i j * (x j) ≤ b i} := by
  induction hS using Nonempty.cons_induction with
  | singleton a =>
    refine ⟨n + n, ?_, ?_, ?_⟩
    · exact fun i j => if h : (i : ℕ) < n then
        if (⟨i.val, h⟩ : Fin n) = j then 1 else 0
      else
        if (⟨i.val - n, by omega⟩ : Fin n) = j then -1 else 0
    · exact fun i => if h : (i : ℕ) < n then a ⟨i.val, h⟩
      else -(a ⟨i.val - n, by omega⟩)
    · ext x
      constructor
      · intro hx
        rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hx
        subst hx
        intro i
        simp only [Set.mem_setOf_eq]
        by_cases h : (i : ℕ) < n
        · simp [h]
        · simp only [h, dite_false]; simp
      · intro hx
        rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff]
        ext j
        have h1 := hx ⟨j.val, by omega⟩
        have h2 := hx ⟨n + j.val, by omega⟩
        simp only [Set.mem_setOf_eq] at h1 h2
        simp [show (j.val : ℕ) < n from j.isLt] at h1
        simp only [show ¬((n + j.val : ℕ) < n) from by omega, dite_false] at h2
        simp only [show (n + j.val - n : ℕ) = j.val from by omega] at h2
        simp [show (⟨j.val, by omega⟩ : Fin n) = j from by ext; rfl] at h2
        linarith
  | cons a s ha hs ih =>
    obtain ⟨m', A', b', hA'⟩ := ih
    have hP' : ∃ x : EuclideanSpace ℝ (Fin n), ∀ i, ∑ j, A' i j * (x j) ≤ b' i := by
      obtain ⟨s₀, hs₀⟩ := hs
      exact ⟨s₀, fun i => by
        have : s₀ ∈ {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m', ∑ j, A' i j * (x j) ≤ b' i} := by
          rw [← hA']; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hs₀)
        exact this i⟩
    have hbdd' : ∀ d : EuclideanSpace ℝ (Fin n), (∀ i, ∑ j, A' i j * d j ≤ 0) → d = 0 :=
      polytope_trivial_recession_cone s hs A' b' hA'
    obtain ⟨m'', A'', b'', hfinal⟩ := polyhedron_convex_hull_point A' b' a hP' hbdd'
    refine ⟨m'', A'', b'', ?_⟩
    have hcoe : (↑(cons a s ha) : Set (EuclideanSpace ℝ (Fin n))) = (↑s : Set _) ∪ {a} := by
      ext x; simp
    rw [hcoe, ← convexHull_convexHull_union_left (↑s) {a}, hA', hfinal]
