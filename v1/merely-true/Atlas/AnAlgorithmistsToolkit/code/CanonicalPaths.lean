/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CanonicalPaths

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def edgesCut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    ∃ v w, e = s(v, w) ∧ v ∈ S ∧ w ∉ S)).card

noncomputable def volume (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, G.degree v

noncomputable def conductanceSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  if min (volume G S) (volume G (Finset.univ \ S)) = 0 then 0
  else (edgesCut G S : ℝ) / (min (volume G S) (volume G (Finset.univ \ S)) : ℝ)

noncomputable def conductance (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf {x : ℝ | ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧ x = conductanceSet G S}

noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (G.degree ·)

def CanonicalPathSystem (G : SimpleGraph V) :=
  (v : V) → (w : V) → G.Walk v w

noncomputable def congestion (G : SimpleGraph V) [DecidableRel G.Adj]
    (paths : CanonicalPathSystem G) (e : Sym2 V) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
    e ∈ (paths p.1 p.2).edges)).card

omit [Fintype V] in
lemma walk_crosses_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {u v : V} (hu : u ∈ S) (hv : v ∉ S)
    (p : G.Walk u v) :
    ∃ e ∈ p.edges, ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S := by
  induction p with
  | nil => exact absurd hu (hv ·)
  | @cons u w v hadj p' ih =>
    by_cases hw : w ∈ S
    · obtain ⟨e, he, a, b, hab, ha, hb⟩ := ih hw hv
      exact ⟨e, List.mem_cons.mpr (Or.inr he), a, b, hab, ha, hb⟩
    · exact ⟨s(u, w), List.mem_cons.mpr (Or.inl rfl), u, w, rfl, hu, hw⟩


theorem conductance_lower_bound
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (paths : CanonicalPathSystem G)
  (b : ℝ)
  (hb : 0 < b)
  (hdmax : 0 < (maxDegree G : ℝ))
  (hV : 0 < Fintype.card V)
  (hcong : ∀ e ∈ G.edgeFinset,
    (congestion G paths e : ℝ) ≤ b * (Fintype.card V : ℝ)) :
  conductance G ≥ 1 / (4 * b * (maxDegree G : ℝ)) := by
  have hdmax_nat : 0 < maxDegree G := by exact_mod_cast hdmax
  have hcard2 : 1 < Fintype.card V := by
    unfold maxDegree at hdmax_nat
    have hne : ¬ (∀ v ∈ (Finset.univ : Finset V), G.degree v = 0) := by
      intro hall; have := (Finset.sup_eq_zero (f := fun v => G.degree v)).mpr hall; omega
    push_neg at hne
    obtain ⟨v, _, hv⟩ := hne
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
    exact Fintype.one_lt_card_iff.mpr ⟨v, w, hw.ne⟩
  unfold conductance; rw [ge_iff_le]
  apply le_csInf
  ·
    obtain ⟨a, _, _⟩ := Fintype.one_lt_card_iff.mp hcard2
    exact ⟨conductanceSet G {a}, {a}, Finset.singleton_nonempty a,
           fun h => by have := congr_arg Finset.card h; simp [Finset.card_univ] at this; omega, rfl⟩
  ·
    intro x hx
    obtain ⟨S, hSne, hSuniv, hxeq⟩ := hx; rw [hxeq]
    have hScne : (Finset.univ \ S).Nonempty := by
      rwa [Finset.sdiff_nonempty, Finset.univ_subset_iff, ← ne_eq]

    have hmin_vol_pos : 0 < min (volume G S) (volume G (Finset.univ \ S)) := by
      rw [Nat.pos_iff_ne_zero]; intro h; rw [Nat.min_eq_zero_iff] at h
      cases h with
      | inl hv =>
        have hz := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hv
        obtain ⟨v, hv⟩ := hSne; obtain ⟨w, hw⟩ := hScne
        cases paths v w with
        | nil => exact (Finset.mem_sdiff.mp hw).2 hv
        | cons hadj _ =>
          exact absurd (hz v hv)
            (by have := (G.degree_pos_iff_exists_adj v).mpr ⟨_, hadj⟩; omega)
      | inr hv =>
        have hz := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hv
        obtain ⟨w, hw⟩ := hScne; obtain ⟨v, hv⟩ := hSne
        cases paths w v with
        | nil => exact (Finset.mem_sdiff.mp hw).2 hv
        | cons hadj _ =>
          exact absurd (hz w hw)
            (by have := (G.degree_pos_iff_exists_adj w).mpr ⟨_, hadj⟩; omega)
    have hmin_ne : min (volume G S) (volume G (Finset.univ \ S)) ≠ 0 := by omega
    unfold conductanceSet; rw [if_neg hmin_ne]

    have hmin_vol_posR : (0 : ℝ) < min (volume G S : ℝ) (volume G (Finset.univ \ S) : ℝ) := by
      rw [← Nat.cast_min]; exact_mod_cast hmin_vol_pos

    have hedge_bound : (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) ≤
        (edgesCut G S : ℝ) * (b * (Fintype.card V : ℝ)) := by
      have hcount : (S ×ˢ (Finset.univ \ S)).card ≤
          ∑ e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
            congestion G paths e := by
        have hsub : S ×ˢ (Finset.univ \ S) ⊆
            (G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S)).biUnion
              (fun e => (Finset.univ ×ˢ Finset.univ).filter
                (fun q : V × V => e ∈ (paths q.1 q.2).edges)) := by
          intro p hp
          rw [Finset.mem_biUnion]
          have hprod := Finset.mem_product.mp hp
          obtain ⟨e, he, a, c, heq, ha, hc⟩ :=
            walk_crosses_cut G S hprod.1 (Finset.mem_sdiff.mp hprod.2).2 (paths p.1 p.2)
          exact ⟨e, Finset.mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr ((paths p.1 p.2).edges_subset_edgeSet he),
             a, c, heq, ha, hc⟩,
            Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, he⟩⟩
        exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have hsum_bound :
          (∑ e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
            (congestion G paths e : ℝ)) ≤ (edgesCut G S : ℝ) * (b * (Fintype.card V : ℝ)) := by
        calc (∑ e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
              (congestion G paths e : ℝ))
            ≤ ∑ _e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
              (b * (Fintype.card V : ℝ)) :=
              Finset.sum_le_sum (fun e he => hcong e (Finset.mem_filter.mp he).1)
          _ = (edgesCut G S : ℝ) * (b * (Fintype.card V : ℝ)) := by
              simp only [Finset.sum_const, edgesCut, nsmul_eq_mul]
      have hcountR : (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) ≤
          (∑ e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
            (congestion G paths e : ℝ)) := by
        have h := Finset.card_product S (Finset.univ \ S)
        have hle := hcount; rw [h] at hle
        have h2 : (↑(S.card * (Finset.univ \ S).card) : ℝ) ≤
            (↑(∑ e ∈ G.edgeFinset.filter (fun e => ∃ a c, e = s(a, c) ∧ a ∈ S ∧ c ∉ S),
              congestion G paths e) : ℝ) := Nat.cast_le.mpr hle
        simp only [Nat.cast_mul, Nat.cast_sum] at h2
        exact h2
      linarith

    have hvol_S : (volume G S : ℝ) ≤ (S.card : ℝ) * (maxDegree G : ℝ) := by
      exact_mod_cast (Finset.sum_le_card_nsmul S _ _ (fun v _ =>
        Finset.le_sup (f := fun v => G.degree v) (Finset.mem_univ v)) :
        volume G S ≤ S.card * maxDegree G)
    have hvol_Sc : (volume G (Finset.univ \ S) : ℝ) ≤
        ((Finset.univ \ S).card : ℝ) * (maxDegree G : ℝ) := by
      exact_mod_cast (Finset.sum_le_card_nsmul _ _ _ (fun v _ =>
        Finset.le_sup (f := fun v => G.degree v) (Finset.mem_univ v)) :
        volume G (Finset.univ \ S) ≤ (Finset.univ \ S).card * maxDegree G)

    have hnV_eq : (Fintype.card V : ℝ) = (S.card : ℝ) + ((Finset.univ \ S).card : ℝ) := by
      exact_mod_cast (Finset.card_univ_diff S ▸
        Nat.add_sub_cancel' (Finset.card_le_univ S) :
        S.card + (Finset.univ \ S).card = Fintype.card V).symm

    have hmin_vol_bound : min (volume G S : ℝ) (volume G (Finset.univ \ S) : ℝ) ≤
        min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) * (maxDegree G : ℝ) :=
      (min_le_min hvol_S hvol_Sc).trans
        (min_mul_of_nonneg _ _ (by positivity : (0:ℝ) ≤ ↑(maxDegree G))).symm.le

    have hkey : min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) * (Fintype.card V : ℝ) ≤
        4 * (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) := by
      rw [hnV_eq]
      rcases le_total (S.card : ℝ) ((Finset.univ \ S).card : ℝ) with h | h
      · simp only [min_eq_left h]
        nlinarith [sq_nonneg ((S.card : ℝ) - ((Finset.univ \ S).card : ℝ))]
      · simp only [min_eq_right h]
        nlinarith [sq_nonneg ((S.card : ℝ) - ((Finset.univ \ S).card : ℝ))]

    rw [le_div_iff₀ hmin_vol_posR]
    suffices h : min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) / (4 * b) ≤
        (edgesCut G S : ℝ) by
      calc 1 / (4 * b * ↑(maxDegree G)) *
            min ↑(volume G S) ↑(volume G (Finset.univ \ S))
          ≤ 1 / (4 * b * ↑(maxDegree G)) *
            (min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) * ↑(maxDegree G)) :=
            mul_le_mul_of_nonneg_left hmin_vol_bound (by positivity)
        _ = min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) / (4 * b) := by field_simp
        _ ≤ (edgesCut G S : ℝ) := h
    calc min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) / (4 * b)
        ≤ (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) /
          (b * (Fintype.card V : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * b)
            (by positivity : (0:ℝ) < b * ↑(Fintype.card V))]
          nlinarith [hkey]
      _ ≤ (edgesCut G S : ℝ) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < b * ↑(Fintype.card V))]
          linarith


end CanonicalPaths
