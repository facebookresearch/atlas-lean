/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.IndependenceOfValuations

open Finset

variable {F : Type*} [Field F]

/-- The intersection $\bigcap_i R_{v_i}$ of the valuation subrings of finitely many discrete valuations $v_i$ on a field $F$, viewed as a subring of $F$. -/
noncomputable def DVRIntersection (n : ℕ) (v : Fin n → AddValuation F (WithTop ℤ)) :
    Subring F where
  carrier := {x : F | ∀ i, (0 : WithTop ℤ) ≤ v i x}
  mul_mem' := by
    intro a b ha hb i; rw [(v i).map_mul]; exact add_nonneg (ha i) (hb i)
  one_mem' := by intro i; simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb i
    exact le_trans (le_min (ha i) (hb i)) ((v i).map_add a b)
  zero_mem' := by intro i; simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha i
    have hvm1 : v i (-1 : F) = 0 := by
      have h1 := (v i).map_mul (-1 : F) (-1)
      rw [show (-1 : F) * (-1) = 1 from by ring, AddValuation.map_one] at h1
      have hne : v i (-1 : F) ≠ ⊤ := by
        rw [ne_eq, AddValuation.top_iff]; exact neg_ne_zero.mpr one_ne_zero
      set c := (v i (-1 : F)).untop hne
      have hc : v i (-1 : F) = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
      rw [hc, ← WithTop.coe_add] at h1
      have h2 : c + c = 0 := WithTop.coe_injective h1.symm
      rw [hc, show c = 0 from by linarith]; rfl
    rw [show (-a : F) = -1 * a from by ring, (v i).map_mul, hvm1, zero_add]; exact ha i

/-- A subring of a field is an integral domain; in particular the intersection of valuation subrings is a domain. -/
instance DVRIntersection_IsDomain (n : ℕ) (v : Fin n → AddValuation F (WithTop ℤ)) :
    IsDomain (DVRIntersection n v) := by
  haveI : Nontrivial (DVRIntersection n v) :=
    ⟨⟨0, 1, fun h => one_ne_zero (congr_arg Subtype.val h).symm⟩⟩
  exact IsDomain.mk

/-- An element with valuation $0$ under all $v_i$ lies in the intersection $\bigcap_i R_{v_i}$. -/
lemma val_zero_mem {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)} {x : F}
    (hv : ∀ i, v i x = (0 : ℤ)) : x ∈ DVRIntersection n v := by
  intro i; rw [hv i]; exact le_refl _

/-- If every $v_i x = 0$, then $x^{-1}$ also has all valuations $0$ and so lies in the intersection. -/
lemma val_zero_inv_mem {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)} {x : F}
    (hv : ∀ i, v i x = (0 : ℤ)) : x⁻¹ ∈ DVRIntersection n v := by
  intro i; rw [AddValuation.map_inv, hv i]; simp

/-- A nonzero element with all valuations equal to $0$ is a unit in the intersection $\bigcap_i R_{v_i}$. -/
lemma isUnit_of_val_zero {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)} {x : F}
    (hx : x ≠ 0) (hv : ∀ i, v i x = (0 : ℤ)) :
    IsUnit (⟨x, val_zero_mem hv⟩ : DVRIntersection n v) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨⟨x⁻¹, val_zero_inv_mem hv⟩, ?_⟩
  ext; simp [mul_inv_cancel₀ hx]

/-- For a nonzero element $x$ of the intersection, each valuation $v_i(x)$ equals a nonnegative integer. -/
lemma val_nonneg_int {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)} {x : F}
    (hx : x ≠ 0) (hmem : x ∈ DVRIntersection n v) (i : Fin n) :
    ∃ a : ℕ, v i x = ((a : ℤ) : WithTop ℤ) := by
  have hne : v i x ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
  set c := (v i x).untop hne
  have hc : v i x = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
  have hnn : 0 ≤ c := by
    have := hmem i; rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at this; exact this
  exact ⟨c.toNat, by rw [hc]; congr 1; omega⟩

/-- If $x \in R$ but $x^{-1} \notin R$, then $x$ is not a unit in $R$. -/
lemma not_isUnit_of_inv_not_mem {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {x : F} (hx_mem : x ∈ DVRIntersection n v) (hxi_not_mem : x⁻¹ ∉ DVRIntersection n v) :
    ¬IsUnit (⟨x, hx_mem⟩ : DVRIntersection n v) := by
  intro ⟨u, hu⟩
  apply hxi_not_mem
  have h1 : (↑u : DVRIntersection n v).val = x := congr_arg Subtype.val hu
  have h3 : x * (↑(u⁻¹) : DVRIntersection n v).val = 1 := by
    have h2 := congr_arg (fun r => (r : DVRIntersection n v).val) u.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at h2
    rwa [h1] at h2
  have h4 : (↑(u⁻¹) : DVRIntersection n v).val = x⁻¹ :=
    eq_comm.mpr (inv_eq_of_mul_eq_one_right h3)
  rw [← h4]; exact (↑(u⁻¹) : DVRIntersection n v).prop

/-- Commuting negation with coercion $\mathbb{Z} \hookrightarrow \mathbb{Z} \cup \{\infty\}$. -/
lemma withtop_neg_coe (a : ℤ) : -(↑a : WithTop ℤ) = ((-a : ℤ) : WithTop ℤ) :=
  (WithTop.LinearOrderedAddCommGroup.coe_neg a).symm

/-- Coercion $\mathbb{Z} \hookrightarrow \mathbb{Z} \cup \{\infty\}$ preserves nonnegativity. -/
lemma withtop_coe_nonneg {a : ℤ} (ha : 0 ≤ a) : (0 : WithTop ℤ) ≤ (a : WithTop ℤ) := by
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]; exact ha

/-- $-1$ is not nonnegative in $\mathbb{Z} \cup \{\infty\}$. -/
lemma withtop_not_nonneg_neg_one (h : (0 : WithTop ℤ) ≤ -(1 : WithTop ℤ)) : False := by
  have h1 : -(1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_num
  rw [h1, ← WithTop.coe_zero, WithTop.coe_le_coe] at h; omega


/-- A simultaneous uniformizer $t_j$ (with $v_i(t_j) = \delta_{ij}$) lies in $\bigcap_i R_{v_i}$. -/
lemma uniformizer_mem {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (j : Fin n) : t j ∈ DVRIntersection n v := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [ht i i, if_pos rfl]; exact withtop_coe_nonneg (by omega)
  · rw [ht i j, if_neg hij]; exact le_refl _

/-- A simultaneous uniformizer $t_j$ is nonzero (since $v_j(t_j) = 1 \neq \infty$). -/
lemma uniformizer_ne_zero {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (j : Fin n) : t j ≠ 0 := by
  intro hj
  have := ht j j; simp at this; rw [hj, AddValuation.map_zero] at this; simp at this

/-- Each simultaneous uniformizer $t_j$ is a prime element of the intersection $\bigcap_i R_{v_i}$. -/
theorem uniformizer_prime {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (j : Fin n) : Prime (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) := by

  have ht_ne := uniformizer_ne_zero ht
  have ht_mem := uniformizer_mem ht
  have ht_self : ∀ k, v k (t k) = (1 : ℤ) := by
    intro k; have := ht k k; simp at this; exact this
  refine ⟨fun h => ht_ne j (congr_arg Subtype.val h), ?_, ?_⟩
  ·
    apply not_isUnit_of_inv_not_mem (ht_mem j)
    intro hmem
    have h1 : (0 : WithTop ℤ) ≤ v j (t j)⁻¹ := hmem j
    rw [AddValuation.map_inv, ht_self j] at h1
    exact withtop_not_nonneg_neg_one h1
  ·
    intro ⟨a', ha'_mem⟩ ⟨b', hb'_mem⟩ ⟨⟨c, hc_mem⟩, hc⟩
    have hc_F := congr_arg Subtype.val hc
    simp only [Subring.coe_mul] at hc_F
    by_cases ha'_zero : a' = 0
    · left; exact ⟨⟨0, (DVRIntersection n v).zero_mem⟩, Subtype.ext (by simp [ha'_zero])⟩
    by_cases hb'_zero : b' = 0
    · right; exact ⟨⟨0, (DVRIntersection n v).zero_mem⟩, Subtype.ext (by simp [hb'_zero])⟩
    obtain ⟨ea, hea⟩ := val_nonneg_int ha'_zero ha'_mem j
    obtain ⟨eb, heb⟩ := val_nonneg_int hb'_zero hb'_mem j
    have hab_val : v j (a' * b') = ((ea + eb : ℤ) : WithTop ℤ) := by
      rw [(v j).map_mul, hea, heb, ← WithTop.coe_add]
    have hc_ne : c ≠ 0 := by
      intro h; rw [h, mul_zero] at hc_F; exact (mul_ne_zero ha'_zero hb'_zero) hc_F
    obtain ⟨ec, hec⟩ := val_nonneg_int hc_ne hc_mem j
    have htc_val : v j (t j * c) = ((1 + ec : ℤ) : WithTop ℤ) := by
      rw [(v j).map_mul, ht_self j, hec, ← WithTop.coe_add]
    have hab_eq : (ea : ℤ) + eb = 1 + ec := by
      have := congr_arg (v j) hc_F; rw [hab_val, htc_val] at this
      exact WithTop.coe_injective this
    rcases Nat.eq_zero_or_pos ea with hea0 | hea_pos
    · right
      have heb1 : 1 ≤ eb := by omega
      have hq_mem : b' * (t j)⁻¹ ∈ DVRIntersection n v := by
        intro i; rw [(v i).map_mul, AddValuation.map_inv, ht i j]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, heb, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero,
              WithTop.coe_le_coe]; omega
        · rw [if_neg hij]; simp [neg_zero]; exact hb'_mem i
      exact ⟨⟨b' * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (ht_ne j), mul_one])⟩
    · left
      have hq_mem : a' * (t j)⁻¹ ∈ DVRIntersection n v := by
        intro i; rw [(v i).map_mul, AddValuation.map_inv, ht i j]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, hea, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero,
              WithTop.coe_le_coe]; omega
        · rw [if_neg hij]; simp [neg_zero]; exact ha'_mem i
      exact ⟨⟨a' * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (ht_ne j), mul_one])⟩

/-- The principal ideal generated by a simultaneous uniformizer $t_j$ is a prime ideal of $\bigcap_i R_{v_i}$. -/
theorem uniformizer_ideal_isPrime {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (j : Fin n) :
    (Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)}).IsPrime := by
  rw [Ideal.span_singleton_prime (show (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) ≠ 0
    from fun h => uniformizer_ne_zero ht j (congr_arg Subtype.val h))]
  exact uniformizer_prime ht j


/-- Factorization in the intersection of DVRs: every nonzero $a \in \bigcap_i R_{v_i}$ factors uniquely as $a = u \cdot \prod_j t_j^{v_j(a)}$ with $u$ a unit. -/
theorem dvr_intersection_factorization {n : ℕ}
    (v : Fin n → AddValuation F (WithTop ℤ))
    (t : Fin n → F)
    (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (a : F) (ha_ne : a ≠ 0) (ha_mem : a ∈ DVRIntersection n v) :

    ∃ (e : Fin n → ℕ) (u : (DVRIntersection n v)ˣ),
      (∀ i, v i a = ((e i : ℤ) : WithTop ℤ)) ∧
      (⟨a, ha_mem⟩ : DVRIntersection n v) =
        ↑u * ∏ j : Fin n, (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) ^ e j := by
  have ht_ne := uniformizer_ne_zero ht
  have ht_mem := uniformizer_mem ht
  have ht_self : ∀ k, v k (t k) = (1 : ℤ) := by
    intro k; have := ht k k; simp at this; exact this

  choose e he using fun i => val_nonneg_int ha_ne ha_mem i

  set prod_t := ∏ j : Fin n, (t j) ^ (e j) with hprod_t_def
  have hprod_ne : prod_t ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (ht_ne i))

  have hval_prod : ∀ i, v i prod_t = ((e i : ℤ) : WithTop ℤ) := by
    intro i; rw [hprod_t_def, addval_prod]
    simp_rw [fun j => addval_npow_coe (v i) (e j) (ht i j), mul_ite, mul_one, mul_zero]
    rw [show ∑ x : Fin n, (↑(if i = x then (e x : ℤ) else 0) : WithTop ℤ) =
      ↑(∑ x : Fin n, (if i = x then (e x : ℤ) else 0)) from by rw [WithTop.coe_sum]]
    congr 1; simp [Finset.mem_univ]

  set u_F := a * prod_t⁻¹ with hu_def
  have hu_ne : u_F ≠ 0 := mul_ne_zero ha_ne (inv_ne_zero hprod_ne)
  have hval_u : ∀ i, v i u_F = (0 : ℤ) := by
    intro i; rw [hu_def, (v i).map_mul, AddValuation.map_inv, he i, hval_prod i]; simp

  have hu_unit : IsUnit (⟨u_F, val_zero_mem hval_u⟩ : DVRIntersection n v) :=
    isUnit_of_val_zero hu_ne hval_u

  have hprod_mem : prod_t ∈ DVRIntersection n v := by
    intro i; rw [hval_prod i]; exact withtop_coe_nonneg (Int.natCast_nonneg _)

  have ha_eq : a = u_F * prod_t := by
    rw [hu_def, mul_assoc, inv_mul_cancel₀ hprod_ne, mul_one]

  obtain ⟨w, hw⟩ := hu_unit
  refine ⟨e, w, he, ?_⟩
  apply Subtype.ext
  simp only [Subring.coe_mul, SubmonoidClass.coe_finset_prod, Subring.coe_pow]

  rw [ha_eq]
  congr 1
  exact (congr_arg Subtype.val hw).symm


/-- Membership in the prime ideal $(t_j)$: $x \in (t_j) \iff v_j(x) \geq 1$. -/
lemma mem_uniformizer_ideal_iff {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (j : Fin n) (x : DVRIntersection n v) :
    x ∈ Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)} ↔
      (1 : WithTop ℤ) ≤ v j x.val := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨y, hy_mem⟩, rfl⟩
    simp only [Subring.coe_mul]
    rw [(v j).map_mul]
    have htj : v j (t j) = (1 : ℤ) := by have := ht j j; simp at this; exact this
    rw [htj]
    have hnn : (0 : WithTop ℤ) ≤ v j y := hy_mem j
    rw [← WithTop.coe_one]
    rcases eq_or_ne y 0 with rfl | hy_ne
    · simp [AddValuation.map_zero]
    · have hne : v j y ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
      set c := (v j y).untop hne
      have hc : v j y = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
      rw [hc, ← WithTop.coe_add, WithTop.coe_le_coe]
      rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at hnn
      omega
  · intro hval
    by_cases hx : x.val = 0
    · exact ⟨0, Subtype.ext (by simp [hx])⟩
    · have hq_mem : x.val * (t j)⁻¹ ∈ DVRIntersection n v := by
        intro i
        rw [(v i).map_mul, AddValuation.map_inv, ht i j]
        by_cases hij : i = j
        · rw [hij, if_pos rfl]
          have hne : v j x.val ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
          set c := (v j x.val).untop hne
          have hc_eq : v j x.val = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
          rw [hc_eq, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
          rw [hc_eq, ← WithTop.coe_one, WithTop.coe_le_coe] at hval
          omega
        · rw [if_neg hij]; simp [neg_zero]; exact x.prop i
      exact ⟨⟨x.val * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (uniformizer_ne_zero ht j), mul_one])⟩

/-- Any nonzero non-unit element of $\bigcap_i R_{v_i}$ lies in some uniformizer prime ideal $(t_j)$. -/
lemma nonunit_in_some_uniformizer_ideal {n : ℕ} {v : Fin n → AddValuation F (WithTop ℤ)}
    {t : Fin n → F} (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
    (x : DVRIntersection n v) (hx_ne : x ≠ 0) (hx_nu : ¬IsUnit x) :
    ∃ j : Fin n, x ∈ Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)} := by
  by_contra h
  push_neg at h
  have hx_ne_F : x.val ≠ 0 := fun habs => hx_ne (Subtype.ext habs)
  have hval_zero : ∀ j, v j x.val = (0 : ℤ) := by
    intro j
    have hnotmem := h j
    rw [mem_uniformizer_ideal_iff ht j x] at hnotmem
    push_neg at hnotmem
    have hne : v j x.val ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
    set c := (v j x.val).untop hne
    have hc : v j x.val = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
    have hnn : 0 ≤ c := by
      have := x.prop j; rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at this; exact this
    have hlt : c < 1 := by
      rw [hc, ← WithTop.coe_one, WithTop.coe_lt_coe] at hnotmem; exact hnotmem
    rw [hc]; congr 1; omega
  exact hx_nu (isUnit_of_val_zero hx_ne_F hval_zero)
