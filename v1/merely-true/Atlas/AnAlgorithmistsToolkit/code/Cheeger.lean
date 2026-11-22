/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.InnerProductSpace.Basic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edgeCut (S : Finset V) : ℕ :=
  (G.interedges S Sᶜ).card

noncomputable def cutRatio (S : Finset V) : ℚ :=
  (G.edgeCut S : ℚ) / (min S.card Sᶜ.card : ℚ)

noncomputable def edgeExpansion : ℚ :=
  let candidates := (Finset.univ : Finset (Finset V)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (G.cutRatio)
  else
    0

noncomputable def volume (S : Finset V) : ℕ :=
  ∑ v ∈ S, G.degree v

noncomputable def setConductance (S : Finset V) : ℚ :=
  (G.edgeCut S : ℚ) / (min (G.volume S : ℚ) (G.volume Sᶜ : ℚ))

noncomputable def conductance : ℚ :=
  let candidates := (Finset.univ : Finset (Finset V)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (G.setConductance)
  else
    0

end SimpleGraph

namespace Cheeger

variable {n : ℕ}

noncomputable def sqNorm (f : Fin n → ℝ) : ℝ := ∑ i, f i ^ 2

noncomputable def quadForm (edges : Finset (Fin n × Fin n)) (f : Fin n → ℝ) : ℝ :=
  ∑ e ∈ edges, (f e.1 - f e.2) ^ 2

lemma quadForm_nonneg (edges : Finset (Fin n × Fin n)) (f : Fin n → ℝ) :
    0 ≤ quadForm edges f := by
  unfold quadForm
  apply Finset.sum_nonneg
  intros; positivity

lemma quadForm_shift (edges : Finset (Fin n × Fin n)) (x : Fin n → ℝ) (c : ℝ) :
    quadForm edges x = quadForm edges (fun i => x i - c) := by
  unfold quadForm
  congr 1; ext e; ring

lemma sqNorm_shift_ge (x : Fin n → ℝ) (c : ℝ) (hx : ∑ i, x i = 0) :
    sqNorm x ≤ sqNorm (fun i => x i - c) := by
  unfold sqNorm
  have expand : ∑ i : Fin n, (x i - c) ^ 2 =
      ∑ i, x i ^ 2 - 2 * c * ∑ i, x i + ↑n * c ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ∑ i : Fin n, 2 * x i * c = 2 * c * ∑ i, x i := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    linarith
  rw [expand, hx, mul_zero, sub_zero]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [sq_nonneg c]

theorem claim6 (edges : Finset (Fin n × Fin n))
    (x : Fin n → ℝ) (c : ℝ) (hx : ∑ i, x i = 0)
    (hxn : 0 < sqNorm x) :
    quadForm edges (fun i => x i - c) / sqNorm (fun i => x i - c) ≤
    quadForm edges x / sqNorm x := by
  have hnum : quadForm edges x = quadForm edges (fun i => x i - c) :=
    quadForm_shift edges x c
  have hdenom : sqNorm x ≤ sqNorm (fun i => x i - c) :=
    sqNorm_shift_ge x c hx
  rw [hnum]
  exact div_le_div_of_nonneg_left (quadForm_nonneg edges _) hxn hdenom

noncomputable def splitQuadForm (crossing : Finset (Fin n × Fin n))
    (f : Fin n → ℝ) (m : Fin n) : ℝ :=
  ∑ e ∈ crossing, ((f e.1 - f m) ^ 2 + (f m - f e.2) ^ 2)

lemma quadForm_ge_splitQuadForm (crossing : Finset (Fin n × Fin n))
    (y : Fin n → ℝ) (m : Fin n)
    (hm : y m = 0) (hcross : ∀ e ∈ crossing, y e.1 * y e.2 ≤ 0) :
    splitQuadForm crossing y m ≤ quadForm crossing y := by
  unfold splitQuadForm quadForm
  apply Finset.sum_le_sum
  intro e he
  have h := hcross e he
  rw [hm, sub_zero, zero_sub, neg_sq]
  have expand : (y e.1 - y e.2) ^ 2 = y e.1 ^ 2 - 2 * (y e.1 * y e.2) + y e.2 ^ 2 := by ring
  linarith

theorem claim7 (noncrossing crossing : Finset (Fin n × Fin n))
    (y : Fin n → ℝ) (m : Fin n)
    (hm : y m = 0)
    (hcross : ∀ e ∈ crossing, y e.1 * y e.2 ≤ 0)
    (hdisjoint : Disjoint noncrossing crossing)
    (hd : 0 < sqNorm y) :
    (quadForm noncrossing y + splitQuadForm crossing y m) / sqNorm y ≤
    quadForm (noncrossing ∪ crossing) y / sqNorm y := by
  apply div_le_div_of_nonneg_right _ (le_of_lt hd)
  have hqsplit := quadForm_ge_splitQuadForm crossing y m hm hcross
  have hunion : quadForm (noncrossing ∪ crossing) y =
      quadForm noncrossing y + quadForm crossing y := by
    unfold quadForm
    rw [Finset.sum_union hdisjoint]
  linarith

lemma abel_summation (m : ℕ) (a : ℕ → ℝ) :
    ∑ k ∈ Finset.range m, ((k : ℝ) + 1) * (a (k + 1) - a k) =
    (m : ℝ) * a m - ∑ k ∈ Finset.range m, a k := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast; ring

theorem lemma8_summation_by_parts (m : ℕ) (z : ℕ → ℝ) (φ : ℝ)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hzm : z m = 0)
    (C : ℕ → ℝ)
    (hC : ∀ k, k < m → φ * ((k : ℝ) + 1) ≤ C k) :
    φ * (∑ k ∈ Finset.range m, (-z k)) ≤
      ∑ k ∈ Finset.range m, C k * (z (k + 1) - z k) := by
  have hincr : ∀ k, k < m → 0 ≤ z (k + 1) - z k := by
    intro k hk
    linarith [hmono k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)]
  calc φ * (∑ k ∈ Finset.range m, (-z k))
      = φ * (-(∑ k ∈ Finset.range m, z k)) := by
        congr 1; rw [Finset.sum_neg_distrib]
    _ = φ * ((m : ℝ) * z m - ∑ k ∈ Finset.range m, z k) := by
        rw [hzm, mul_zero, zero_sub]
    _ = φ * (∑ k ∈ Finset.range m, ((k : ℝ) + 1) * (z (k + 1) - z k)) := by
        rw [← abel_summation m z]
    _ = ∑ k ∈ Finset.range m, (φ * ((k : ℝ) + 1)) * (z (k + 1) - z k) := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
    _ ≤ ∑ k ∈ Finset.range m, C k * (z (k + 1) - z k) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        exact mul_le_mul_of_nonneg_right (hC k hk) (hincr k hk)

theorem lemma8_summation_by_parts_abs (m : ℕ) (z : ℕ → ℝ) (φ : ℝ)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hzm : z m = 0)
    (C : ℕ → ℝ)
    (hC : ∀ k, k < m → φ * ((k : ℝ) + 1) ≤ C k) :
    φ * (∑ k ∈ Finset.range m, |z k|) ≤
      ∑ k ∈ Finset.range m, C k * (z (k + 1) - z k) := by
  have habs_eq : ∀ k ∈ Finset.range m, |z k| = -z k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : z k ≤ 0 := by
      have h := hmono k m (Nat.le_of_lt hk) (le_refl m)
      linarith
    exact abs_of_nonpos hle
  rw [Finset.sum_congr rfl habs_eq]
  exact lemma8_summation_by_parts m z φ hmono hzm C hC

theorem crossing_number_decomposition (m : ℕ) (z : ℕ → ℝ)
    (edges : Finset (ℕ × ℕ))
    (hedge : ∀ e ∈ edges, e.1 < e.2 ∧ e.2 ≤ m) :
    ∑ e ∈ edges, (z e.2 - z e.1) =
      ∑ k ∈ Finset.range m,
        ((edges.filter (fun e => e.1 ≤ k ∧ k < e.2)).card : ℝ) * (z (k + 1) - z k) := by

  have htele : ∀ e ∈ edges, z e.2 - z e.1 =
      ∑ k ∈ Finset.Ico e.1 e.2, (z (k + 1) - z k) := by
    intro e he
    exact (Finset.sum_Ico_sub z (hedge e he).1.le).symm

  have hext : ∀ e ∈ edges, ∑ k ∈ Finset.Ico e.1 e.2, (z (k + 1) - z k) =
      ∑ k ∈ Finset.range m, if e.1 ≤ k ∧ k < e.2 then z (k + 1) - z k else 0 := by
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨Nat.lt_of_lt_of_le h2 (hedge e he).2, h1, h2⟩
    · intro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩

  conv_lhs =>
    rw [Finset.sum_congr rfl htele]
    rw [Finset.sum_congr rfl hext]
  rw [Finset.sum_comm]

  congr 1; ext k
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem lemma8_summation_by_parts_edges (m : ℕ) (z : ℕ → ℝ) (φ : ℝ)
    (edges : Finset (ℕ × ℕ))
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hzm : z m = 0)
    (hedge : ∀ e ∈ edges, e.1 < e.2 ∧ e.2 ≤ m)
    (hC : ∀ k, k < m → φ * ((k : ℝ) + 1) ≤
      ((edges.filter (fun e => e.1 ≤ k ∧ k < e.2)).card : ℝ)) :
    φ * (∑ k ∈ Finset.range m, |z k|) ≤
      ∑ e ∈ edges, |z e.2 - z e.1| := by


  have habs_edge : ∀ e ∈ edges, |z e.2 - z e.1| = z e.2 - z e.1 := by
    intro e he
    have ⟨hlt, hle⟩ := hedge e he
    exact abs_of_nonneg (sub_nonneg.mpr (hmono e.1 e.2 hlt.le hle))
  rw [Finset.sum_congr rfl habs_edge]

  rw [crossing_number_decomposition m z edges hedge]

  exact lemma8_summation_by_parts_abs m z φ hmono hzm _ hC

noncomputable def indicatorVec (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (Sᶜ.card : ℝ) else -(S.card : ℝ)

lemma indicatorVec_sum (S : Finset (Fin n)) :
    ∑ i : Fin n, indicatorVec S i = 0 := by
  unfold indicatorVec
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h : ({x : Fin n | x ∉ S} : Finset (Fin n)).card = Sᶜ.card := by
    congr 1; ext x; simp [Finset.mem_compl]
  rw [h]; ring

lemma sqNorm_indicatorVec (S : Finset (Fin n)) :
    sqNorm (indicatorVec S) = (S.card : ℝ) * (Sᶜ.card : ℝ) * (n : ℝ) := by
  unfold sqNorm indicatorVec
  have key : ∀ i : Fin n, (if i ∈ S then (Sᶜ.card : ℝ) else -(S.card : ℝ)) ^ 2 =
      if i ∈ S then (Sᶜ.card : ℝ) ^ 2 else (S.card : ℝ) ^ 2 := by
    intro i; split_ifs <;> simp
  simp_rw [key]; rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h : ({x : Fin n | x ∉ S} : Finset (Fin n)).card = Sᶜ.card := by
    congr 1; ext x; simp [Finset.mem_compl]
  rw [h]
  have hn : (n : ℝ) = (S.card : ℝ) + (Sᶜ.card : ℝ) := by
    have hh := Finset.card_add_card_compl S; rw [Fintype.card_fin] at hh; push_cast [← hh]; ring
  rw [hn]; ring

lemma sqNorm_indicatorVec_pos (S : Finset (Fin n))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    0 < sqNorm (indicatorVec S) := by
  rw [sqNorm_indicatorVec]
  have hs : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hsc : (0 : ℝ) < (Sᶜ.card : ℝ) := by exact_mod_cast hSc.card_pos
  have hn : (0 : ℝ) < (n : ℝ) := by
    have hh := Finset.card_add_card_compl S; rw [Fintype.card_fin] at hh
    have : (n : ℝ) = (S.card : ℝ) + (Sᶜ.card : ℝ) := by push_cast [← hh]; ring
    linarith
  positivity

set_option linter.unusedVariables false in

noncomputable def prefixCutRatio (edges : Finset (Fin n × Fin n)) (i : ℕ) : ℝ :=
  let crossingEdges := edges.filter (fun e =>
    ((e.1 : ℕ) < i ∧ ¬((e.2 : ℕ) < i)) ∨ (¬((e.1 : ℕ) < i) ∧ (e.2 : ℕ) < i))
  (crossingEdges.card : ℝ) / (min (i : ℝ) ((n : ℝ) - (i : ℝ)))

lemma prefixCutRatio_nonneg (edges : Finset (Fin n × Fin n)) (i : ℕ)
    (hi : 0 < i) (hin : i < n) : 0 ≤ prefixCutRatio edges i := by
  unfold prefixCutRatio; apply div_nonneg (Nat.cast_nonneg _)
  apply le_of_lt; apply lt_min (Nat.cast_pos.mpr hi)
  have : (i : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hin; linarith

lemma sum_fst_fiber (edges : Finset (Fin n × Fin n)) (f : Fin n → ℝ) :
    ∑ e ∈ edges, f e.1 =
      ∑ v : Fin n, ((edges.filter (fun e => e.1 = v)).card : ℝ) * f v := by
  have h := (Finset.sum_fiberwise (g := fun e => e.1) edges (fun e => f e.1)).symm
  rw [h]; congr 1; ext v
  rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

lemma sum_endpoints_sq_le (edges : Finset (Fin n × Fin n)) (x : Fin n → ℝ) (dmax : ℝ)
    (hno : ∀ e ∈ edges, e.1 ≠ e.2)
    (hd : ∀ v : Fin n, ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) ≤ dmax) :
    ∑ e ∈ edges, (x e.1 ^ 2 + x e.2 ^ 2) ≤ dmax * sqNorm x := by
  have h_split : ∑ e ∈ edges, (x e.1 ^ 2 + x e.2 ^ 2) =
      ∑ e ∈ edges, x e.1 ^ 2 + ∑ e ∈ edges, x e.2 ^ 2 := Finset.sum_add_distrib
  have h_fst := sum_fst_fiber edges (fun v => x v ^ 2)
  have h_snd : ∑ e ∈ edges, x e.2 ^ 2 =
      ∑ v : Fin n, ((edges.filter (fun e => e.2 = v)).card : ℝ) * x v ^ 2 := by
    have := (Finset.sum_fiberwise (g := fun e => e.2) edges (fun e => x e.2 ^ 2)).symm
    rw [this]; congr 1; ext v
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_split, h_fst, h_snd, ← Finset.sum_add_distrib]
  have h_card : ∀ v : Fin n,
      ((edges.filter (fun e => e.1 = v)).card : ℝ) + ((edges.filter (fun e => e.2 = v)).card : ℝ) =
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) := by
    intro v
    have hdisj : Disjoint (edges.filter (fun e => e.1 = v)) (edges.filter (fun e => e.2 = v)) := by
      rw [Finset.disjoint_filter]
      intro e he h1 h2; exact hno e he (h1 ▸ h2.symm)
    have hunion : (edges.filter (fun e => e.1 = v)) ∪ (edges.filter (fun e => e.2 = v)) =
        edges.filter (fun e => e.1 = v ∨ e.2 = v) := by
      ext e; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj, hunion]
  calc ∑ v : Fin n, (((edges.filter (fun e => e.1 = v)).card : ℝ) * x v ^ 2 +
        ((edges.filter (fun e => e.2 = v)).card : ℝ) * x v ^ 2)
      = ∑ v : Fin n, (((edges.filter (fun e => e.1 = v)).card : ℝ) +
        ((edges.filter (fun e => e.2 = v)).card : ℝ)) * x v ^ 2 := by
        congr 1; ext v; ring
    _ = ∑ v : Fin n, ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * x v ^ 2 := by
        congr 1; ext v; rw [h_card]
    _ ≤ ∑ v : Fin n, dmax * x v ^ 2 := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_right (hd v) (sq_nonneg _)
    _ = dmax * sqNorm x := by unfold sqNorm; rw [Finset.mul_sum]

lemma degree_bound_sum_add_sq (edges : Finset (Fin n × Fin n)) (x : Fin n → ℝ) (dmax : ℝ)
    (hno : ∀ e ∈ edges, e.1 ≠ e.2)
    (hd : ∀ v : Fin n, ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) ≤ dmax) :
    ∑ e ∈ edges, (x e.1 + x e.2) ^ 2 ≤ 2 * dmax * sqNorm x := by
  have h_ineq : ∀ e ∈ edges, (x e.1 + x e.2) ^ 2 ≤ 2 * (x e.1 ^ 2 + x e.2 ^ 2) := by
    intro e _; nlinarith [sq_nonneg (x e.1 - x e.2)]
  calc ∑ e ∈ edges, (x e.1 + x e.2) ^ 2
      ≤ ∑ e ∈ edges, (2 * (x e.1 ^ 2 + x e.2 ^ 2)) := Finset.sum_le_sum h_ineq
    _ = 2 * ∑ e ∈ edges, (x e.1 ^ 2 + x e.2 ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * (dmax * sqNorm x) := by
        apply mul_le_mul_of_nonneg_left (sum_endpoints_sq_le edges x dmax hno hd)
          (by norm_num : (0:ℝ) ≤ 2)
    _ = 2 * dmax * sqNorm x := by ring

theorem theorem5_sorted_rayleigh_bound
    (edges : Finset (Fin n × Fin n)) (x : Fin n → ℝ) (dmax : ℝ)
    (_hn : 2 ≤ n) (hdmax : 0 < dmax)
    (_hx_orth : ∑ i, x i = 0)
    (_hx_sorted : ∀ i j : Fin n, i ≤ j → x i ≤ x j)
    (hx_nonzero : x ≠ 0)
    (hdmax_bound : ∀ v : Fin n,
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) ≤ dmax)
    (h_edges_sorted : ∀ e ∈ edges, (e.1 : ℕ) < (e.2 : ℕ))

    (i₀ : ℕ) (hi₀_pos : 0 < i₀) (hi₀_lt : i₀ < n)

    (neg_norm : ℝ) (h_neg_nn : 0 ≤ neg_norm)
    (h_neg_bound : prefixCutRatio edges i₀ * neg_norm ≤
        ∑ e ∈ edges.filter (fun e => (e.2 : ℕ) ≤ i₀), |x e.1 ^ 2 - x e.2 ^ 2|)

    (pos_norm : ℝ) (h_pos_nn : 0 ≤ pos_norm)
    (h_pos_bound : prefixCutRatio edges i₀ * pos_norm ≤
        ∑ e ∈ edges.filter (fun e => i₀ ≤ (e.1 : ℕ)), |x e.1 ^ 2 - x e.2 ^ 2|)

    (h_sqnorm_decomp : sqNorm x = neg_norm + pos_norm) :
    ∃ i : ℕ, 0 < i ∧ i < n ∧
      prefixCutRatio edges i ^ 2 / (2 * dmax) ≤ quadForm edges x / sqNorm x := by

  have hφ := prefixCutRatio_nonneg edges i₀ hi₀_pos hi₀_lt
  have hno_selfloop : ∀ e ∈ edges, e.1 ≠ e.2 := by
    intro e he; have := h_edges_sorted e he; exact Fin.ne_of_val_ne (by omega)
  have h_lem8 : prefixCutRatio edges i₀ * sqNorm x ≤
      ∑ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2| := by
    rw [h_sqnorm_decomp, mul_add]


    have h_disj : Disjoint (edges.filter (fun e => (e.2 : ℕ) ≤ i₀))
        (edges.filter (fun e => i₀ ≤ (e.1 : ℕ))) := by
      rw [Finset.disjoint_filter]
      intro e he h1e h2e
      have := h_edges_sorted e he
      omega
    have h_union_le : ∑ e ∈ edges.filter (fun e => (e.2 : ℕ) ≤ i₀), |x e.1 ^ 2 - x e.2 ^ 2| +
        ∑ e ∈ edges.filter (fun e => i₀ ≤ (e.1 : ℕ)), |x e.1 ^ 2 - x e.2 ^ 2| ≤
        ∑ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2| := by
      rw [← Finset.sum_union h_disj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)) (fun _ _ _ => abs_nonneg _)
    have h3 := mul_nonneg hφ h_neg_nn
    have h4 := mul_nonneg hφ h_pos_nn
    linarith [h_neg_bound, h_pos_bound]

  have hx_pos : 0 < sqNorm x := by
    unfold sqNorm
    have : ∃ j, x j ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h; exact hx_nonzero (funext h)
    obtain ⟨j, hj⟩ := this
    calc 0 < x j ^ 2 := by positivity
      _ ≤ ∑ k, x k ^ 2 := Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
  refine ⟨i₀, hi₀_pos, hi₀_lt, ?_⟩
  have h2d : (0 : ℝ) < 2 * dmax := by linarith
  have h_deg := degree_bound_sum_add_sq edges x dmax hno_selfloop hdmax_bound
  rw [div_le_div_iff₀ h2d hx_pos]
  have h_sq : (prefixCutRatio edges i₀ * sqNorm x) ^ 2 ≤
      (∑ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2|) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hφ (le_of_lt hx_pos)) h_lem8 2
  have h_cs : (∑ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2|) ^ 2 ≤
      (∑ e ∈ edges, (x e.1 - x e.2) ^ 2) * (∑ e ∈ edges, (x e.1 + x e.2) ^ 2) := by
    have hf : ∀ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2| = |x e.1 - x e.2| * |x e.1 + x e.2| := by
      intro e _
      rw [show x e.1 ^ 2 - x e.2 ^ 2 = (x e.1 - x e.2) * (x e.1 + x e.2) from by ring]
      exact abs_mul _ _
    rw [Finset.sum_congr rfl hf]
    have := Finset.sum_mul_sq_le_sq_mul_sq edges
      (fun e => |x e.1 - x e.2|) (fun e => |x e.1 + x e.2|)
    simp only [sq_abs] at this; exact this
  have hqf_nn : (0 : ℝ) ≤ ∑ e ∈ edges, (x e.1 - x e.2) ^ 2 :=
    Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have h_comb : (prefixCutRatio edges i₀) ^ 2 * (sqNorm x) ^ 2 ≤
      quadForm edges x * (2 * dmax * sqNorm x) := by
    calc (prefixCutRatio edges i₀) ^ 2 * (sqNorm x) ^ 2
        = (prefixCutRatio edges i₀ * sqNorm x) ^ 2 := by ring
      _ ≤ (∑ e ∈ edges, |x e.1 ^ 2 - x e.2 ^ 2|) ^ 2 := h_sq
      _ ≤ (∑ e ∈ edges, (x e.1 - x e.2) ^ 2) * (∑ e ∈ edges, (x e.1 + x e.2) ^ 2) := h_cs
      _ ≤ quadForm edges x * (2 * dmax * sqNorm x) :=
          mul_le_mul_of_nonneg_left h_deg hqf_nn
  nlinarith [sq_nonneg (prefixCutRatio edges i₀), sq_nonneg (sqNorm x)]

noncomputable def dirEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e : Fin n × Fin n => G.Adj e.1 e.2)

lemma dirEdges_filter_cut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    (dirEdges G).filter (fun e => e.1 ∈ S ∧ e.2 ∉ S) = G.interedges S Sᶜ := by
  ext e
  simp only [dirEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_interedges_iff, Finset.mem_compl]
  tauto


theorem normalized_rayleigh_indicatorVec_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSc : (Sᶜ : Finset (Fin n)).Nonempty) :
    quadForm (dirEdges G) (indicatorVec S) / (2 * sqNorm (indicatorVec S)) ≤
    2 * (G.cutRatio S : ℝ) := by

  have hs : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hsc : (0 : ℝ) < (Sᶜ.card : ℝ) := by exact_mod_cast hSc.card_pos
  have hn : (n : ℝ) = (S.card : ℝ) + (Sᶜ.card : ℝ) := by
    have hh := Finset.card_add_card_compl S; rw [Fintype.card_fin] at hh; push_cast [← hh]; ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqnorm_pos := sqNorm_indicatorVec_pos S hS hSc
  have h2sqnorm_pos : (0 : ℝ) < 2 * sqNorm (indicatorVec S) := by linarith


  have hqf : quadForm (dirEdges G) (indicatorVec S) =
      ((G.interedges S Sᶜ).card + (G.interedges Sᶜ S).card : ℝ) * (n : ℝ) ^ 2 := by
    unfold quadForm indicatorVec
    have hn' : (Sᶜ.card : ℝ) + (S.card : ℝ) = (n : ℝ) := by linarith [hn]

    have hval : ∀ e ∈ dirEdges G,
        ((if e.1 ∈ S then (Sᶜ.card : ℝ) else -(S.card : ℝ)) -
         (if e.2 ∈ S then (Sᶜ.card : ℝ) else -(S.card : ℝ))) ^ 2 =
        if (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S) then (n : ℝ) ^ 2 else 0 := by
      intro e _
      by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;> simp [h1, h2] <;> nlinarith [hn']
    rw [show ∑ e ∈ dirEdges G, _ = ∑ e ∈ dirEdges G,
        (if (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S) then (n : ℝ) ^ 2 else 0) from
        Finset.sum_congr rfl hval]
    rw [← Finset.sum_filter]

    have hfilt : (dirEdges G).filter (fun e => (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)) =
        (dirEdges G).filter (fun e => e.1 ∈ S ∧ e.2 ∉ S) ∪
        (dirEdges G).filter (fun e => e.1 ∉ S ∧ e.2 ∈ S) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_union]; tauto
    rw [hfilt, Finset.sum_union]
    · simp only [Finset.sum_const, nsmul_eq_mul]

      have hf1 : (dirEdges G).filter (fun e => e.1 ∈ S ∧ e.2 ∉ S) = G.interedges S Sᶜ :=
        dirEdges_filter_cut G S
      have hf2 : (dirEdges G).filter (fun e => e.1 ∉ S ∧ e.2 ∈ S) = G.interedges Sᶜ S := by
        ext e
        simp only [dirEdges, Finset.mem_filter, Finset.mem_univ, true_and,
          SimpleGraph.mem_interedges_iff, Finset.mem_compl]
        tauto
      rw [hf1, hf2]; ring
    ·
      apply Finset.disjoint_filter.mpr
      intro e _ h1 h2; exact absurd h1.1 h2.1

  have hcard_symm : (G.interedges Sᶜ S).card = (G.interedges S Sᶜ).card := by
    exact Rel.card_interedges_comm G.symm Sᶜ S

  have hqf_val : quadForm (dirEdges G) (indicatorVec S) =
      2 * (G.edgeCut S : ℝ) * (n : ℝ) ^ 2 := by
    rw [hqf, hcard_symm]
    unfold SimpleGraph.edgeCut
    ring


  have hlhs : quadForm (dirEdges G) (indicatorVec S) / (2 * sqNorm (indicatorVec S)) =
      (G.edgeCut S : ℝ) * (n : ℝ) / ((S.card : ℝ) * (Sᶜ.card : ℝ)) := by
    rw [hqf_val, sqNorm_indicatorVec]
    field_simp

  rw [hlhs]


  by_cases hcut : G.edgeCut S = 0
  · unfold SimpleGraph.cutRatio
    simp [hcut]
  · have hcut_pos : (0 : ℝ) < (G.edgeCut S : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcut
    have hmin_pos : (0 : ℝ) < (min (S.card : ℝ) (Sᶜ.card : ℝ)) := lt_min hs hsc

    suffices h : (G.edgeCut S : ℝ) * (n : ℝ) / ((S.card : ℝ) * (Sᶜ.card : ℝ)) ≤
        2 * (G.edgeCut S : ℝ) / (min (S.card : ℝ) (Sᶜ.card : ℝ)) by
      calc (G.edgeCut S : ℝ) * (n : ℝ) / ((S.card : ℝ) * (Sᶜ.card : ℝ))
          ≤ 2 * (G.edgeCut S : ℝ) / (min (S.card : ℝ) (Sᶜ.card : ℝ)) := h
        _ = 2 * (G.cutRatio S : ℝ) := by
            unfold SimpleGraph.cutRatio
            push_cast [Nat.cast_min]
            ring


    rw [div_le_div_iff₀ (mul_pos hs hsc) hmin_pos]
    have key : (n : ℝ) * min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
        2 * ((S.card : ℝ) * (Sᶜ.card : ℝ)) := by
      rw [hn]
      rcases le_total (S.card : ℝ) (Sᶜ.card : ℝ) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    nlinarith




end Cheeger
