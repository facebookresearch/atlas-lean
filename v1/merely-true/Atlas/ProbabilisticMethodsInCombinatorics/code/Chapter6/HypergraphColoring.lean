/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 800000

open Set Topology

namespace HypergraphColoring

variable {V : Type*}


/-- Set of 2-colorings of `V` that properly color every hyperedge `e ∈ edges` contained in the
finite vertex set `X` (no edge entirely monochromatic). -/
def goodColorings (edges : Set (Finset V)) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ e ∈ edges, (↑e : Set V) ⊆ ↑X →
    ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false)}

/-- For a finite edge `e` and a Boolean `b`, the set of colorings not identically `b` on `e`
is closed in the product (discrete) topology on `V → Bool`. -/
lemma isClosed_not_all_eq (e : Finset V) (b : Bool) :
    IsClosed {c : V → Bool | ¬(∀ v ∈ e, c v = b)} := by
  have heq : {c : V → Bool | ¬(∀ v ∈ e, c v = b)} = (Set.pi (↑e) (fun _ => {b}))ᶜ := by
    ext c; simp [Set.mem_pi]
  rw [heq]
  exact (isOpen_set_pi e.finite_toSet (fun _ _ => @isOpen_discrete Bool _ _ {b})).isClosed_compl

/-- The set `goodColorings edges X` of proper 2-colorings is closed in `V → Bool`. -/
lemma isClosed_goodColorings (edges : Set (Finset V)) (X : Finset V) :
    IsClosed (goodColorings edges X) := by
  have heq : goodColorings edges X =
      ⋂ (e : Finset V) (_ : e ∈ edges) (_ : (↑e : Set V) ⊆ ↑X),
        ({c : V → Bool | ¬(∀ v ∈ e, c v = true)} ∩
         {c | ¬(∀ v ∈ e, c v = false)}) := by
    ext c; simp only [goodColorings, mem_setOf_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro _
  apply isClosed_iInter; intro _
  exact IsClosed.inter (isClosed_not_all_eq e true) (isClosed_not_all_eq e false)

/-- Antitonicity: enlarging the vertex set `X` shrinks the set of good colorings. -/
lemma goodColorings_anti (edges : Set (Finset V)) {X Y : Finset V} (hYX : Y ⊆ X) :
    goodColorings edges X ⊆ goodColorings edges Y := by
  intro c hc e he hes
  exact hc e he (hes.trans (Finset.coe_subset.mpr hYX))



/-- A hypergraph is $k$-regular if every vertex is contained in exactly $k$ edges. -/
def IsRegular (edges : Set (Finset V)) (k : ℕ) : Prop :=
  ∀ v : V, Set.ncard {e ∈ edges | v ∈ e} = k

/-- In a $k$-uniform $k$-regular hypergraph, each edge intersects at most $k(k-1)$ other edges:
sum over its $k$ vertices, each lying in $k-1$ other edges. -/
lemma edge_degree_bound_of_regular
    (edges : Set (Finset V)) (k : ℕ) (hk : k ≥ 1)
    (huniform : ∀ e ∈ edges, e.card = k)
    (hregular : IsRegular edges k) :
    ∀ e ∈ edges, Set.ncard {f ∈ edges | f ≠ e ∧ (↑e ∩ ↑f : Set V).Nonempty} ≤ k * (k - 1) := by
  intro e he
  have h_sub : {f ∈ edges | f ≠ e ∧ (↑e ∩ ↑f : Set V).Nonempty} ⊆
      ⋃ v ∈ e, ({f ∈ edges | v ∈ f} \ {e} : Set (Finset V)) := by
    intro f ⟨hfe, hfne, v, hve, hvf⟩
    simp only [Finset.mem_coe] at hve hvf
    exact Set.mem_biUnion hve ⟨⟨hfe, hvf⟩, hfne⟩
  have h_fin_vertex : ∀ v : V, ({f ∈ edges | v ∈ f} : Set (Finset V)).Finite :=
    fun v => Set.finite_of_ncard_ne_zero (by rw [hregular v]; omega)
  have h_fin : (⋃ v ∈ e, ({f ∈ edges | v ∈ f} \ {e} : Set (Finset V))).Finite :=
    Set.Finite.biUnion e.finite_toSet (fun v _ => (h_fin_vertex v).diff)
  calc Set.ncard {f ∈ edges | f ≠ e ∧ (↑e ∩ ↑f : Set V).Nonempty}
      ≤ (⋃ v ∈ e, ({f ∈ edges | v ∈ f} \ {e} : Set (Finset V))).ncard :=
        Set.ncard_le_ncard h_sub h_fin
    _ ≤ ∑ v ∈ e, Set.ncard ({f ∈ edges | v ∈ f} \ {e} : Set (Finset V)) :=
        Finset.set_ncard_biUnion_le e _
    _ ≤ e.card • (k - 1) := by
        apply Finset.sum_le_card_nsmul
        intro v hv
        have hmem : e ∈ ({f ∈ edges | v ∈ f} : Set (Finset V)) := ⟨he, hv⟩
        rw [Set.ncard_diff_singleton_of_mem hmem, hregular v]
    _ = k * (k - 1) := by rw [huniform e he, smul_eq_mul]

/-- Numerical lemma underlying Corollary 6.2.2: for all $k \ge 9$,
$k(k-1) + 1 \le e^{-1} \cdot 2^{k-1}$. -/
lemma lll_numerical_bound_k_ge_9 (k : ℕ) (hk : k ≥ 9) :
    (↑(k * (k - 1)) : ℝ) + 1 ≤ (Real.exp 1)⁻¹ * (2 : ℝ) ^ (k - 1 : ℕ) := by
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  suffices h : Real.exp 1 * ((↑(k * (k - 1)) : ℝ) + 1) ≤ (2 : ℝ) ^ (k - 1 : ℕ) by
    rw [show (Real.exp 1)⁻¹ * (2 : ℝ) ^ (k - 1 : ℕ) = (2 : ℝ) ^ (k - 1 : ℕ) / Real.exp 1
        from by rw [div_eq_inv_mul]]
    rw [le_div_iff₀ hexp_pos]
    linarith [mul_comm (Real.exp 1) ((↑(k * (k - 1)) : ℝ) + 1)]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 9 := ⟨k - 9, by omega⟩
  induction n with
  | zero =>
    norm_num
    linarith [Real.exp_one_lt_d9]
  | succ m ih =>
    have hm9 := ih (by omega : m + 9 ≥ 9)
    have h_step : ((m + 10) * (m + 9) + 1 : ℕ) ≤ 2 * ((m + 9) * (m + 8) + 1) := by
      nlinarith
    have h_pow : (2 : ℝ) ^ (m + 10 - 1 : ℕ) = 2 * (2 : ℝ) ^ (m + 9 - 1 : ℕ) := by
      norm_num; ring
    rw [h_pow]
    have h_cast : (↑((m + 10) * (m + 9)) : ℝ) + 1 ≤ 2 * ((↑((m + 9) * (m + 8)) : ℝ) + 1) := by
      have := @Nat.cast_le ℝ _ _ _ |>.mpr h_step
      push_cast at this ⊢; linarith
    calc Real.exp 1 * ((↑((m + 10) * (m + 9)) : ℝ) + 1)
        ≤ Real.exp 1 * (2 * ((↑((m + 9) * (m + 8)) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h_cast (le_of_lt hexp_pos)
      _ = 2 * (Real.exp 1 * ((↑((m + 9) * (m + 8)) : ℝ) + 1)) := by ring
      _ ≤ 2 * (2 : ℝ) ^ (m + 9 - 1 : ℕ) :=
          mul_le_mul_of_nonneg_left hm9 (by norm_num : (0:ℝ) ≤ 2)


end HypergraphColoring
