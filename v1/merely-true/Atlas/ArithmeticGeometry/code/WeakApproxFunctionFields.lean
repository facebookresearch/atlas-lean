/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.IndependenceOfValuations

open Finset

variable {F : Type*} [Field F]

/-- If $v(a) < 0$, then $v(1+a) = v(a)$ by the ultrametric inequality
applied to $\min(v(1), v(a)) = v(a)$. -/
lemma val_one_add_of_neg (v : AddValuation F (WithTop ℤ)) {a : F}
    (hva : v a < (0 : WithTop ℤ)) :
    v (1 + a) = v a := by
  have h1 : v 1 = (0 : WithTop ℤ) := v.map_one
  have hne : v 1 ≠ v a := by rw [h1]; exact ne_of_gt hva
  rw [AddValuation.map_add_of_distinct_val v hne, h1, min_eq_right (le_of_lt hva)]

/-- If $v(a) > 0$, then $v(1+a) = 0$ by the ultrametric inequality applied
to $\min(v(1), v(a)) = 0$. -/
lemma val_one_add_of_pos (v : AddValuation F (WithTop ℤ)) {a : F}
    (hva : (0 : WithTop ℤ) < v a) :
    v (1 + a) = (0 : WithTop ℤ) := by
  have h1 : v 1 = (0 : WithTop ℤ) := v.map_one
  have hne : v 1 ≠ v a := by rw [h1]; exact ne_of_lt hva
  rw [AddValuation.map_add_of_distinct_val v hne, h1, min_eq_left (le_of_lt hva)]

/-- If $v(a) < 0$ then $1 + a \neq 0$: otherwise $v(1+a) = \infty$, contradicting
$v(1+a) = v(a) < 0$. -/
lemma one_add_ne_zero_of_neg_val' (v : AddValuation F (WithTop ℤ)) {a : F}
    (hva : v a < (0 : WithTop ℤ)) : 1 + a ≠ 0 := by
  intro h
  have htop : v (1 + a) = ⊤ := by rw [h, AddValuation.map_zero]
  have heq : v (1 + a) = v a := val_one_add_of_neg v hva
  exact absurd (heq ▸ htop) (ne_of_lt (lt_of_lt_of_le hva le_top))

/-- Algebraic identity $\dfrac{a}{1+a} - 1 = -\dfrac{1}{1+a}$ valid whenever
$1 + a \neq 0$. -/
lemma div_one_add_sub_one {a : F} (h : 1 + a ≠ 0) :
    a * (1 + a)⁻¹ - 1 = -(1 + a)⁻¹ := by
  field_simp; ring

/-- An additive valuation turns finite products into finite sums:
$v\!\left(\prod_{i \in s} f(i)\right) = \sum_{i \in s} v(f(i))$. -/
lemma addval_finset_prod (v : AddValuation F (WithTop ℤ))
    {ι : Type*} (f : ι → F) (s : Finset ι) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [v.map_one]
  | cons a s has ih =>
    rw [Finset.prod_cons, v.map_mul, Finset.sum_cons, ih]

/-- Ultrametric inequality, threshold form: if $N < v(x)$ and $N < v(y)$
then $N < v(x+y)$. -/
lemma addval_add_gt (v : AddValuation F (WithTop ℤ)) {x y : F} {N : ℤ}
    (hx : (N : WithTop ℤ) < v x) (hy : (N : WithTop ℤ) < v y) :
    (N : WithTop ℤ) < v (x + y) :=
  lt_of_lt_of_le (lt_min hx hy) (AddValuation.map_add v x y)

/-- Threshold ultrametric inequality for finite sums: if $N < v(f(i))$ for all
$i \in s$, then $N < v\!\left(\sum_{i \in s} f(i)\right)$. -/
lemma addval_sum_gt (v : AddValuation F (WithTop ℤ)) {ι : Type*} [DecidableEq ι]
    (f : ι → F) (s : Finset ι) {N : ℤ}
    (h : ∀ i ∈ s, (N : WithTop ℤ) < v (f i)) :
    (N : WithTop ℤ) < v (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty, AddValuation.map_zero]
    exact WithTop.coe_lt_top N
  | cons a s has ih =>
    rw [Finset.sum_cons]
    exact addval_add_gt v (h a (Finset.mem_cons_self a s))
      (ih (fun i hi => h i (Finset.mem_cons_of_mem hi)))

/-- Weak Approximation for Function Fields (Corollary 20.5). Given finitely
many pairwise incomparable surjective discrete additive valuations
$v_1, \ldots, v_n$ on a field $F$, target elements $f_1, \ldots, f_n \in F$
and any threshold $N \in \mathbb{Z}$, there exists a single $g \in F$ with
$v_i(g - f_i) > N$ for every $i$. -/
theorem weak_approx_function_fields (n : ℕ)
    (v : Fin n → AddValuation F (WithTop ℤ))
    (hv_surj : ∀ i, ∃ u, v i u = (1 : ℤ))
    (hv_incomp : ∀ i j, i ≠ j → ¬(∀ x, (0 : WithTop ℤ) ≤ v i x → (0 : WithTop ℤ) ≤ v j x))
    (f : Fin n → F) (N : ℤ) :
    ∃ g : F, ∀ i, (N : WithTop ℤ) < v i (g - f i) := by

  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · exact ⟨0, fun i => Fin.elim0 i⟩

  obtain ⟨t, ht⟩ := independence_of_valuations n v hv_surj hv_incomp
  have ht_diag : ∀ i, v i (t i) = (1 : ℤ) := fun i => by
    have := ht i i; simp at this; exact this
  have ht_off : ∀ i j, i ≠ j → v i (t j) = (0 : ℤ) := fun i j hij => by
    have := ht i j; rw [if_neg hij] at this; exact this
  have ht_ne : ∀ i, t i ≠ 0 := fun i => ne_zero_of_val_coe (ht_diag i)


  set p : Fin n → F := fun i => ∏ j ∈ Finset.univ.erase i, t j
  have hp_ne : ∀ i, p i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => ht_ne j)
  have hp_self : ∀ i, v i (p i) = (0 : ℤ) := by
    intro i
    show v i (∏ j ∈ Finset.univ.erase i, t j) = (0 : ℤ)
    rw [addval_finset_prod]
    have : ∀ j ∈ Finset.univ.erase i, v i (t j) = (0 : WithTop ℤ) :=
      fun j hj => ht_off i j (Finset.ne_of_mem_erase hj).symm
    simp [Finset.sum_congr rfl this]

  have hp_other : ∀ i j, i ≠ j → v j (p i) = (1 : ℤ) := by
    intro i j hij
    show v j (∏ k ∈ Finset.univ.erase i, t k) = (1 : ℤ)
    rw [addval_finset_prod]
    have hj_mem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ _ hj_mem, ht_diag j]
    have hrest : ∀ k ∈ (Finset.univ.erase i).erase j, v j (t k) = (0 : WithTop ℤ) :=
      fun k hk => ht_off j k (Finset.ne_of_mem_erase hk).symm
    simp [Finset.sum_congr rfl hrest]

  set q : Fin n → F := fun i => p i * (t i)⁻¹
  have hq_ne : ∀ i, q i ≠ 0 := fun i => mul_ne_zero (hp_ne i) (inv_ne_zero (ht_ne i))

  have hq_self : ∀ i, v i (q i) = ((-1 : ℤ) : WithTop ℤ) := by
    intro i
    show v i (p i * (t i)⁻¹) = ((-1 : ℤ) : WithTop ℤ)
    rw [(v i).map_mul, hp_self i, addval_inv_coe (v i) (ht_diag i)]
    simp

  have hq_other : ∀ i j, i ≠ j → v j (q i) = ((1 : ℤ) : WithTop ℤ) := by
    intro i j hij
    show v j (p i * (t i)⁻¹) = ((1 : ℤ) : WithTop ℤ)
    rw [(v j).map_mul, hp_other i j hij, addval_inv_coe (v j) (ht_off j i (Ne.symm hij))]
    simp


  have hK_exists : ∃ K : ℕ, 0 < K ∧ ∀ i j, (N : WithTop ℤ) < v i (f j) + (↑(K : ℤ) : WithTop ℤ) := by
    classical


    have hfin : ∀ i j, f j ≠ 0 → ∃ s : ℤ, v i (f j) = ↑s := by
      intro i j hj
      cases hvij : v i (f j) with
      | top => exact absurd hvij (addval_ne_top (v i) hj)
      | coe a => exact ⟨a, rfl⟩

    set vals : Finset ℤ := Finset.univ.image (fun (p : Fin n × Fin n) =>
      if h : f p.2 = 0 then 0
      else (v p.1 (f p.2)).untop (addval_ne_top (v p.1) h))
    have hvals_ne : vals.Nonempty := by
      have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn_pos⟩, ⟨0, hn_pos⟩)⟩
      exact Finset.Nonempty.image Finset.univ_nonempty _
    set minval := vals.min' hvals_ne
    refine ⟨(N + 1 - minval).toNat + 1, by omega, fun i j => ?_⟩
    by_cases hj : f j = 0
    · rw [hj, AddValuation.map_zero]; exact le_top |>.trans_lt' (WithTop.coe_lt_top _) |>.trans_le le_top
    · obtain ⟨s, hs⟩ := hfin i j hj
      rw [hs]
      rw [show (↑s : WithTop ℤ) + (↑((↑((N + 1 - minval).toNat + 1) : ℤ)) : WithTop ℤ) =
        ↑(s + ↑((N + 1 - minval).toNat + 1)) from by push_cast; ring]
      rw [WithTop.coe_lt_coe]
      have hmin : minval ≤ s := by
        apply Finset.min'_le
        simp only [vals, Finset.mem_image, Prod.exists]
        exact ⟨i, j, Finset.mem_univ _, by simp [hj, hs, WithTop.untop_coe]⟩
      omega
  obtain ⟨K, hK_pos, hK_bound⟩ := hK_exists

  set a : Fin n → F := fun i => q i ^ (K : ℤ)

  have ha_ne : ∀ i, a i ≠ 0 := fun i => zpow_ne_zero K (hq_ne i)

  have ha_self : ∀ i, v i (a i) = (↑(-(K : ℤ)) : WithTop ℤ) := by
    intro i
    rw [show a i = q i ^ (K : ℤ) from rfl, addval_zpow_coe (v i) (hq_self i) K]
    congr 1; omega

  have ha_other : ∀ i j, i ≠ j → v j (a i) = (↑(K : ℤ) : WithTop ℤ) := by
    intro i j hij
    rw [show a i = q i ^ (K : ℤ) from rfl, addval_zpow_coe (v j) (hq_other i j hij) K]
    congr 1; omega

  have ha_neg : ∀ i, v i (a i) < (0 : WithTop ℤ) := by
    intro i; rw [ha_self i]; exact_mod_cast show (-(K : ℤ)) < 0 by omega

  have ha_pos : ∀ i j, i ≠ j → (0 : WithTop ℤ) < v j (a i) := by
    intro i j hij; rw [ha_other i j hij]; exact_mod_cast show (0 : ℤ) < K by omega

  have hone_a : ∀ i, 1 + a i ≠ 0 := fun i => one_add_ne_zero_of_neg_val' (v i) (ha_neg i)

  set e : Fin n → F := fun i => a i * (1 + a i)⁻¹


  have he_diag : ∀ i, v i (e i - 1) = (↑(K : ℤ) : WithTop ℤ) := by
    intro i
    rw [show e i - 1 = -(1 + a i)⁻¹ from div_one_add_sub_one (hone_a i)]
    rw [AddValuation.map_neg, AddValuation.map_inv, val_one_add_of_neg (v i) (ha_neg i),
        ha_self i]
    simp

  have he_off : ∀ i j, i ≠ j → v j (e i) = (↑(K : ℤ) : WithTop ℤ) := by
    intro i j hij
    show v j (a i * (1 + a i)⁻¹) = (↑(K : ℤ) : WithTop ℤ)
    rw [(v j).map_mul, AddValuation.map_inv, val_one_add_of_pos (v j) (ha_pos i j hij),
        ha_other i j hij]
    simp

  refine ⟨∑ i, f i * e i, fun i => ?_⟩


  have hrw : (∑ j, f j * e j) - f i =
      f i * (e i - 1) + ∑ j ∈ Finset.univ.erase i, f j * e j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  rw [hrw]
  apply addval_add_gt
  ·
    by_cases hfi : f i = 0
    · rw [hfi, zero_mul, AddValuation.map_zero]; exact WithTop.coe_lt_top N
    · rw [(v i).map_mul, he_diag i]

      exact hK_bound i i
  ·
    apply addval_sum_gt
    intro j hj
    rw [Finset.mem_erase] at hj
    by_cases hfj : f j = 0
    · rw [hfj, zero_mul, AddValuation.map_zero]; exact WithTop.coe_lt_top N
    · rw [(v i).map_mul, he_off j i hj.1]

      exact hK_bound i j
