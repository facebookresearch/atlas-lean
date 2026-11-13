/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Finset.Basic
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory ENNReal Set Finset

namespace LopsidedLLL

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that all events $A_j$ for $j \in S$ fail to occur, i.e. $\bigcap_{j \in S} A_j^c$. -/
def avoidSet {ι : Type*} (A : ι → Set Ω) (S : Finset ι) : Set Ω :=
  ⋂ j ∈ (S : Set ι), (A j)ᶜ

/-- If each $A_i$ is measurable, then `avoidSet A S = ⋂_{j ∈ S} (A j)ᶜ` is measurable. -/
lemma avoidSet_measurableSet {ι : Type*} {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    MeasurableSet (avoidSet A S) :=
  MeasurableSet.biInter S.countable_toSet (fun i _ => (hA i).compl)

omit [MeasurableSpace Ω] in
/-- Recursive identity: `avoidSet A (insert j S) = avoidSet A S ∩ (A j)ᶜ`. -/
lemma avoidSet_insert_eq {ι : Type*} [DecidableEq ι] (A : ι → Set Ω)
    (S : Finset ι) (j : ι) :
    avoidSet A (insert j S) = avoidSet A S ∩ (A j)ᶜ := by
  simp only [avoidSet, Finset.coe_insert, Set.biInter_insert, Set.inter_comm]

omit [MeasurableSpace Ω] in
/-- `avoidSet` turns finset union into set intersection: `avoidSet A (S ∪ T) = avoidSet A S ∩ avoidSet A T`. -/
lemma avoidSet_union_eq {ι : Type*} [DecidableEq ι] (A : ι → Set Ω)
    (S T : Finset ι) : avoidSet A (S ∪ T) = avoidSet A S ∩ avoidSet A T := by
  simp only [avoidSet, Finset.coe_union, Set.biInter_union]

/-- If $x_i < 1$ for each $i \in S$ (in `ℝ≥0∞`), then $\prod_{j \in S}(1 - x_j) \neq 0$. -/
lemma prod_one_sub_ne_zero {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ≥0∞) (hx : ∀ i ∈ S, x i < 1) :
    ∏ j ∈ S, (1 - x j) ≠ 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hjS ih =>
    rw [Finset.prod_insert hjS]
    exact mul_ne_zero (ne_of_gt (tsub_pos_of_lt (hx j (mem_insert_self j S))))
      (ih (fun i hi => hx i (mem_insert_of_mem hi)))

/-- The `ℝ≥0∞`-product $\prod_{j \in S}(1 - x_j)$ is bounded above by $1$, hence is never $\infty$. -/
lemma prod_one_sub_ne_top {ι : Type*} (S : Finset ι) (x : ι → ℝ≥0∞) :
    ∏ j ∈ S, (1 - x j) ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (prod_le_one (fun _ _ => zero_le _) (fun _ _ => tsub_le_self))

/-- If each factor satisfies $f_i \le 1$, then enlarging the index set can only decrease the product: $\prod_{i \in S_2} f_i \le \prod_{i \in S_1} f_i$ when $S_1 \subseteq S_2$. -/
lemma prod_le_prod_of_superset {ι : Type*} [DecidableEq ι]
    {S₁ S₂ : Finset ι} {f : ι → ℝ≥0∞}
    (h : S₁ ⊆ S₂) (hf : ∀ i ∈ S₂, f i ≤ 1) :
    ∏ i ∈ S₂, f i ≤ ∏ i ∈ S₁, f i := by
  rw [← Finset.prod_sdiff h]
  calc (∏ x ∈ S₂ \ S₁, f x) * ∏ x ∈ S₁, f x
      ≤ 1 * ∏ x ∈ S₁, f x := by
        exact mul_le_mul' (prod_le_one (fun i _ => zero_le _)
          (fun i hi => hf i (Finset.sdiff_subset hi))) le_rfl
    _ = ∏ x ∈ S₁, f x := one_mul _

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Iteratively expanding conditional probabilities: under the hypothesis that for every $j \in S$ and every subset $T \subseteq S$ with $j \notin T$ one has $\nu(A_j \mid \text{avoidSet}\ A\ T) \le x_j$, one obtains the lower bound $\nu(\text{avoidSet}\ A\ S) \ge \prod_{j \in S}(1 - x_j)$. -/
lemma avoidSet_ge_prod {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    {A : Fin n → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    {x : Fin n → ℝ≥0∞} (hx_lt : ∀ i, x i < 1)
    (S : Finset (Fin n))
    (hkey : ∀ j ∈ S, ∀ T ⊆ S, j ∉ T → ν[A j | avoidSet A T] ≤ x j) :
    ν (avoidSet A S) ≥ ∏ j ∈ S, (1 - x j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [avoidSet]
  | @insert j S hjS ih =>
    rw [avoidSet_insert_eq A S j]
    have hms := avoidSet_measurableSet hA S
    have ih_applied := ih (fun j' hj' T hT hj'T =>
      hkey j' (mem_insert_of_mem hj') T (Finset.Subset.trans hT (subset_insert j S)) hj'T)
    have havoid_ne : ν (avoidSet A S) ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (pos_iff_ne_zero.mpr (prod_one_sub_ne_zero S x (fun i _ => hx_lt i)))
        ih_applied)
    rw [(cond_mul_eq_inter' hms (measure_ne_top ν _) (A j)ᶜ).symm]
    have : IsProbabilityMeasure ν[|avoidSet A S] := cond_isProbabilityMeasure havoid_ne
    rw [prob_compl_eq_one_sub (hA j), Finset.prod_insert hjS]
    exact mul_le_mul' (tsub_le_tsub_left
      (hkey j (mem_insert_self j S) S (subset_insert j S) hjS) 1) ih_applied

/-- Core inductive estimate for the Lopsided Local Lemma: under the lopsidependency hypothesis `hlop` and the bound $\mu(A_i) \le x_i \prod_{j \in N(i)}(1-x_j)$, one has $\mu(A_i \mid \text{avoidSet}\ A\ S) \le x_i$ for every $i \notin S$. -/
lemma key_bound {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : Fin n → Finset (Fin n))
    (x : Fin n → ℝ≥0∞) (hx_lt : ∀ i, x i < 1)
    (hlop : ∀ (i : Fin n) (S : Finset (Fin n)),
      S ⊆ Finset.univ \ (N i ∪ {i}) →
      μ[A i | avoidSet A S] ≤ μ (A i))
    (hbound : ∀ i, μ (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (S : Finset (Fin n)) (i : Fin n) (hiS : i ∉ S) :
    μ[A i | avoidSet A S] ≤ x i := by
  classical
  revert i
  induction S using Finset.strongInduction with
  | H S ih =>
  intro i hiS

  by_cases havoid_zero : μ (avoidSet A S) = 0
  · have := cond_eq_zero_of_meas_eq_zero havoid_zero
    simp [this]

  set S₁ := S ∩ N i
  set S₂ := S \ N i
  have hS_eq : S₂ ∪ S₁ = S := by
    ext x; simp [S₁, S₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hS1_sub_Ni : S₁ ⊆ N i := Finset.inter_subset_right
  have hDisj : Disjoint S₂ S₁ := Finset.disjoint_sdiff_inter S (N i)
  have hS2_sub : S₂ ⊆ Finset.univ \ (N i ∪ {i}) := by
    intro x hx
    simp only [S₂, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton] at hx ⊢
    push Not; exact ⟨hx.2, fun h => hiS (h ▸ hx.1)⟩
  have hmS₁ := avoidSet_measurableSet hA S₁
  have hmS₂ := avoidSet_measurableSet hA S₂
  have havoid_eq : avoidSet A S = avoidSet A S₂ ∩ avoidSet A S₁ := by
    rw [← avoidSet_union_eq A S₂ S₁, hS_eq]

  have hcond_eq : μ[|avoidSet A S] = μ[|avoidSet A S₂][|avoidSet A S₁] := by
    rw [cond_cond_eq_cond_inter' hmS₂ hmS₁ (measure_ne_top μ _)]
    rw [havoid_eq]

  rw [show μ[A i | avoidSet A S] = μ[|avoidSet A S₂][A i | avoidSet A S₁] from
    congr_fun (congr_arg _ hcond_eq) (A i)]
  rw [cond_apply hmS₁ μ[|avoidSet A S₂] (A i)]
  set ν := μ[|avoidSet A S₂]

  have hnum : ν (avoidSet A S₁ ∩ A i) ≤ x i * ∏ j ∈ N i, (1 - x j) :=
    calc ν (avoidSet A S₁ ∩ A i)
        ≤ ν (A i) := measure_mono Set.inter_subset_right
      _ ≤ μ (A i) := hlop i S₂ hS2_sub
      _ ≤ x i * ∏ j ∈ N i, (1 - x j) := hbound i

  have hS₂_pos : μ (avoidSet A S₂) ≠ 0 := by
    intro h; apply havoid_zero
    exact le_antisymm (nonpos_iff_eq_zero.mpr (measure_mono_null
      (havoid_eq ▸ Set.inter_subset_left) h)) (zero_le _)
  have hνprob : IsProbabilityMeasure ν := cond_isProbabilityMeasure hS₂_pos


  have hdenom : ∏ j ∈ S₁, (1 - x j) ≤ ν (avoidSet A S₁) :=
    avoidSet_ge_prod ν hA hx_lt S₁ (fun j hjS₁ T hT hjT => by

      show ν[A j | avoidSet A T] ≤ x j
      have hcond_ν : ν[A j | avoidSet A T] = μ[A j | avoidSet A (S₂ ∪ T)] := by
        show μ[|avoidSet A S₂][A j | avoidSet A T] = _
        have := cond_cond_eq_cond_inter' hmS₂ (avoidSet_measurableSet hA T) (measure_ne_top μ _)
        rw [← avoidSet_union_eq A S₂ T] at this
        exact congr_fun (congr_arg _ this) (A j)
      rw [hcond_ν]

      have hjS₂ : j ∉ S₂ := fun h => (Finset.disjoint_right.mp hDisj hjS₁) h
      apply ih (S₂ ∪ T) _ j
      ·
        simp only [Finset.mem_union]; push Not; exact ⟨hjS₂, hjT⟩
      ·
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro x hx; rw [← hS_eq]
          simp only [Finset.mem_union] at hx ⊢
          exact hx.elim Or.inl (fun h => Or.inr (hT h))
        · intro heq
          have : j ∈ S₂ ∪ T := heq ▸ (hS_eq ▸ Finset.mem_union_right _ hjS₁)
          exact (Finset.mem_union.mp this).elim hjS₂ hjT)

  calc (ν (avoidSet A S₁))⁻¹ * ν (avoidSet A S₁ ∩ A i)
      ≤ (∏ j ∈ S₁, (1 - x j))⁻¹ * (x i * ∏ j ∈ N i, (1 - x j)) :=
        mul_le_mul' (ENNReal.inv_le_inv' hdenom) hnum
    _ ≤ x i := by
        rw [show (∏ j ∈ S₁, (1 - x j))⁻¹ * (x i * ∏ j ∈ N i, (1 - x j)) =
          x i * ((∏ j ∈ S₁, (1 - x j))⁻¹ * ∏ j ∈ N i, (1 - x j)) from by ring]
        calc x i * ((∏ j ∈ S₁, (1 - x j))⁻¹ * ∏ j ∈ N i, (1 - x j))
            ≤ x i * ((∏ j ∈ S₁, (1 - x j))⁻¹ * ∏ j ∈ S₁, (1 - x j)) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl
                (prod_le_prod_of_superset hS1_sub_Ni (fun _ _ => tsub_le_self)))
          _ = x i * 1 := by
              rw [ENNReal.inv_mul_cancel (prod_one_sub_ne_zero S₁ x (fun j _ => hx_lt j))
                (prod_one_sub_ne_top S₁ x)]
          _ = x i := mul_one _

/-- Lopsided Local Lemma (Theorem 6.5.1, general form): given events $A_1,\dots,A_n$ with a lopsidependency neighbourhood $N$, weights $x_i \in [0,1)$, the lopsidependency hypothesis $\mu(A_i \mid \bigcap_{j \in S}\overline{A_j}) \le \mu(A_i)$ for $S$ disjoint from $N(i) \cup \{i\}$, and $\mu(A_i) \le x_i \prod_{j \in N(i)}(1-x_j)$, one has $\mu(\bigcap_i \overline{A_i}) \ge \prod_i (1 - x_i)$. -/
theorem lopsided_local_lemma {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : Fin n → Finset (Fin n))
    (x : Fin n → ℝ≥0∞) (hx_lt : ∀ i, x i < 1)
    (hlop : ∀ (i : Fin n) (S : Finset (Fin n)),
      S ⊆ Finset.univ \ (N i ∪ {i}) →
      μ[A i | avoidSet A S] ≤ μ (A i))
    (hbound : ∀ i, μ (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    μ (⋂ i, (A i)ᶜ) ≥ ∏ i : Fin n, (1 - x i) := by
  classical
  have heq : (⋂ i, (A i)ᶜ) = avoidSet A Finset.univ := by
    simp only [avoidSet, Finset.coe_univ, Set.mem_univ, Set.iInter_true]
  rw [heq]
  have hkey := key_bound A hA N x hx_lt hlop hbound
  have := avoidSet_ge_prod μ hA hx_lt Finset.univ (fun j _ T _ hjT => hkey T j hjT)
  exact this

end LopsidedLLL
