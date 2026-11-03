/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators


namespace BooleanFourier

def IsDictator {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ i : Fin n, ∀ x, f x = x i

def IsUnanimous {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  f (fun _ => true) = true ∧ f (fun _ => false) = false

def prefersOver {m : ℕ} (ranking : Equiv.Perm (Fin m)) (a b : Fin m) : Bool :=
  decide (ranking a < ranking b)

def IsArrowViable {n : ℕ} (f : (Fin n → Bool) → Bool) (m : ℕ) : Prop :=
  ∀ (rankings : Fin n → Equiv.Perm (Fin m)),
    ∀ (a b c : Fin m),
      a ≠ b → b ≠ c → a ≠ c →
      f (fun i => prefersOver (rankings i) a b) = true →
      f (fun i => prefersOver (rankings i) b c) = true →
      f (fun i => prefersOver (rankings i) a c) = true

def IsOdd {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f (fun i => !(x i)) = !(f x)

lemma prefersOver_of_lt {m : ℕ} {σ : Equiv.Perm (Fin m)} {a b : Fin m}
    (h : σ a < σ b) : prefersOver σ a b = true := by
  simp [prefersOver, h]

lemma not_prefersOver_of_lt {m : ℕ} {σ : Equiv.Perm (Fin m)} {a b : Fin m}
    (h : σ b < σ a) : prefersOver σ a b = false := by
  simp [prefersOver]; omega

theorem exists_perm_placing_at_positions {m : ℕ} (hm : m ≥ 3) (a b c : Fin m)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ σ : Equiv.Perm (Fin m),
      σ a = ⟨0, by omega⟩ ∧ σ b = ⟨1, by omega⟩ ∧ σ c = ⟨2, by omega⟩ := by
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  let σ₁ := Equiv.swap a p0
  let b' := σ₁ b
  let σ₂ := Equiv.swap b' p1
  let c' := σ₂ (σ₁ c)
  let σ₃ := Equiv.swap c' p2
  have ha1 : σ₁ a = p0 := Equiv.swap_apply_left a p0
  have hb'_ne_p0 : b' ≠ p0 := by
    intro h; exact hab (σ₁.injective (by rw [ha1]; exact h.symm))
  have hp1_ne_p0 : p1 ≠ p0 := by simp [p0, p1, Fin.ext_iff]
  have hσ₂_p0 : σ₂ p0 = p0 := Equiv.swap_apply_of_ne_of_ne hb'_ne_p0.symm hp1_ne_p0.symm
  have hσ₂_b' : σ₂ b' = p1 := Equiv.swap_apply_left b' p1
  have hc'_ne_p0 : c' ≠ p0 := by
    intro h; exact hac (σ₁.injective (σ₂.injective (by rw [ha1, hσ₂_p0]; exact h.symm)))
  have hc'_ne_p1 : c' ≠ p1 := by
    intro h
    exact hbc (σ₁.injective (σ₂.injective
      (show σ₂ (σ₁ b) = σ₂ (σ₁ c) from by change σ₂ b' = c'; rw [hσ₂_b']; exact h.symm)))
  have hp2_ne_p0 : p2 ≠ p0 := by simp [p0, p2, Fin.ext_iff]
  have hp2_ne_p1 : p2 ≠ p1 := by simp [p1, p2, Fin.ext_iff]
  have hσ₃_p0 : σ₃ p0 = p0 := Equiv.swap_apply_of_ne_of_ne hc'_ne_p0.symm hp2_ne_p0.symm
  have hσ₃_p1 : σ₃ p1 = p1 := Equiv.swap_apply_of_ne_of_ne hc'_ne_p1.symm hp2_ne_p1.symm
  refine ⟨σ₃ * σ₂ * σ₁, ?_, ?_, ?_⟩
  · show σ₃ (σ₂ (σ₁ a)) = p0; rw [ha1, hσ₂_p0, hσ₃_p0]
  · show σ₃ (σ₂ (σ₁ b)) = p1; change σ₃ (σ₂ b') = p1; rw [hσ₂_b', hσ₃_p1]
  · show σ₃ (σ₂ (σ₁ c)) = p2; change σ₃ c' = p2; exact Equiv.swap_apply_left c' p2

private def flipCoord {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

private noncomputable def influence {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) / (2 ^ n : ℝ)

lemma exists_perm_for_valid_triple {m : ℕ} (hm : m ≥ 3) (a b c : Fin m)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (pab pbc pac : Bool) (hvalid : pab = pbc → pac = pab) :
    ∃ σ : Equiv.Perm (Fin m),
      prefersOver σ a b = pab ∧ prefersOver σ b c = pbc ∧ prefersOver σ a c = pac := by
  have hba := hab.symm; have hcb := hbc.symm; have hca := hac.symm
  match pab, pbc, pac, hvalid with
  | true, true, true, _ =>
    obtain ⟨σ, hσa, hσb, hσc⟩ := exists_perm_placing_at_positions hm a b c hab hbc hac
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, false, true, _ =>
    obtain ⟨σ, hσa, hσc, hσb⟩ := exists_perm_placing_at_positions hm a c b hac hcb hab
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, true, true, _ =>
    obtain ⟨σ, hσb, hσa, hσc⟩ := exists_perm_placing_at_positions hm b a c hba hac hbc
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, true, false, _ =>
    obtain ⟨σ, hσb, hσc, hσa⟩ := exists_perm_placing_at_positions hm b c a hbc hca hba
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
              prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, false, false, _ =>
    obtain ⟨σ, hσc, hσa, hσb⟩ := exists_perm_placing_at_positions hm c a b hca hab hcb
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, false, false, _ =>
    obtain ⟨σ, hσc, hσb, hσa⟩ := exists_perm_placing_at_positions hm c b a hcb hba hca
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
              not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, true, false, h => exact absurd (h rfl) Bool.noConfusion
  | false, false, true, h => exact absurd (h rfl) Bool.noConfusion

theorem arrow_viable_subcube {n m : ℕ} (hm : m ≥ 3)
    (f : (Fin n → Bool) → Bool) (hviable : IsArrowViable f m)
    (u v w : Fin n → Bool) (hfu : f u = true) (hfv : f v = true)
    (hw : ∀ k : Fin n, u k = v k → w k = u k) : f w = true := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hexists : ∀ k : Fin n, ∃ σ : Equiv.Perm (Fin m),
      prefersOver σ a b = u k ∧ prefersOver σ b c = v k ∧ prefersOver σ a c = w k :=
    fun k => exists_perm_for_valid_triple hm a b c hab hbc hac (u k) (v k) (w k) (hw k)
  classical
  let rankings : Fin n → Equiv.Perm (Fin m) := fun k => (hexists k).choose
  have hrankings : ∀ k, prefersOver (rankings k) a b = u k ∧
      prefersOver (rankings k) b c = v k ∧ prefersOver (rankings k) a c = w k :=
    fun k => (hexists k).choose_spec
  have h1 : f (fun k => prefersOver (rankings k) a b) = true := by
    have heq : (fun k => prefersOver (rankings k) a b) = u := funext fun k => (hrankings k).1
    rw [heq]; exact hfu
  have h2 : f (fun k => prefersOver (rankings k) b c) = true := by
    have heq : (fun k => prefersOver (rankings k) b c) = v := funext fun k => (hrankings k).2.1
    rw [heq]; exact hfv
  have h3 : (fun k => prefersOver (rankings k) a c) = w := funext fun k => (hrankings k).2.2
  rw [← h3]; exact hviable rankings a b c hab hbc hac h1 h2

private lemma exists_true_flip_witness {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hi : influence f i > 0) :
    ∃ x : Fin n → Bool, f x = true ∧ f (flipCoord x i) = false := by
  unfold influence at hi
  have hcard : 0 < (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card := by
    by_contra h
    have h' : (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card = 0 := by omega
    simp [h'] at hi
  rw [Finset.card_pos] at hcard
  obtain ⟨x, hx⟩ := hcard
  have hx' := (Finset.mem_filter.mp hx).2
  cases hfx : f x with
  | false =>
    cases hfx' : f (flipCoord x i) with
    | false => simp [hfx, hfx'] at hx'
    | true =>
      refine ⟨flipCoord x i, hfx', ?_⟩
      have heq : flipCoord (flipCoord x i) i = x := by
        funext k; by_cases hk : k = i
        · subst hk; simp [flipCoord, Bool.not_not]
        · simp [flipCoord, Function.update, hk]
      rw [heq, hfx]
  | true =>
    cases hfx' : f (flipCoord x i) with
    | false => exact ⟨x, hfx, hfx'⟩
    | true => simp [hfx, hfx'] at hx'

theorem arrow_viable_implies_unique_pivot {n m : ℕ} (hm : m ≥ 3)
    (f : (Fin n → Bool) → Bool) (hviable : IsArrowViable f m)
    (hodd : IsOdd f)
    (i j : Fin n) (hi : influence f i > 0) (hj : influence f j > 0) :
    i = j := by
  by_contra hne
  obtain ⟨x, hfx, hfxi⟩ := exists_true_flip_witness f i hi
  obtain ⟨y, hfy, hfyj⟩ := exists_true_flip_witness f j hj
  by_cases hxi_yi : x i ≠ y i
  ·
    have hcontra := arrow_viable_subcube hm f hviable x y (flipCoord x i) hfx hfy (by
      intro k hk
      have hki : k ≠ i := fun heq => by subst heq; exact hxi_yi hk
      simp [flipCoord, Function.update, hki])
    rw [hfxi] at hcontra; exact Bool.noConfusion hcontra
  ·
    have hxi_yi : x i = y i := not_ne_iff.mp hxi_yi
    by_cases hxj_yj : x j ≠ y j
    ·
      have hcontra := arrow_viable_subcube hm f hviable x y (flipCoord y j) hfx hfy (by
        intro k hk
        have hkj : k ≠ j := fun heq => by subst heq; exact hxj_yj hk
        simp [flipCoord, Function.update, hkj]; exact hk.symm)
      rw [hfyj] at hcontra; exact Bool.noConfusion hcontra
    ·
      have hxj_yj : x j = y j := not_ne_iff.mp hxj_yj

      let z : Fin n → Bool := fun k => !(flipCoord y j k)
      have hfz : f z = true := by
        have h := hodd (flipCoord y j)
        show f (fun k => !(flipCoord y j k)) = true
        rw [h, hfyj, Bool.not_false]

      have hxi_ne_zi : x i ≠ z i := by
        show x i ≠ !(flipCoord y j i)
        simp only [flipCoord, Function.update, dif_neg hne]
        rw [hxi_yi]; exact Bool.self_ne_not (y i)
      have hcontra := arrow_viable_subcube hm f hviable x z (flipCoord x i) hfx hfz (by
        intro k hk
        have hki : k ≠ i := fun heq => by subst heq; exact hxi_ne_zi hk
        simp [flipCoord, Function.update, hki])
      rw [hfxi] at hcontra; exact Bool.noConfusion hcontra

private lemma flipCoord_eq_of_ne {n : ℕ} (z : Fin n → Bool) (a : Fin n) (b : Bool)
    (h : ¬(z a = b)) : (flipCoord z a) a = b := by
  simp only [flipCoord, Function.update_self]
  cases hza : z a <;> cases hb : b
  · exact absurd rfl (hza ▸ hb ▸ h)
  · rfl
  · rfl
  · exact absurd rfl (hza ▸ hb ▸ h)

private lemma influence_zero_invariant {n : ℕ} (f : (Fin n → Bool) → Bool) (j : Fin n)
    (hj : influence f j = 0) : ∀ x : Fin n → Bool, f x = f (flipCoord x j) := by
  intro x
  unfold influence at hj
  have h2n : (2 : ℝ) ^ n > 0 := pow_pos (by norm_num : (2 : ℝ) > 0) n

  have hcard_nat : (Finset.univ.filter fun x => f x ≠ f (flipCoord x j)).card = 0 := by
    have : ((Finset.univ.filter fun x => f x ≠ f (flipCoord x j)).card : ℝ) = 0 :=
      (div_eq_zero_iff.mp hj).resolve_right (ne_of_gt h2n)
    exact_mod_cast this
  by_contra hne
  have hmem : x ∈ (Finset.univ.filter fun x => f x ≠ f (flipCoord x j)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  rw [Finset.card_eq_zero.mp hcard_nat] at hmem; simp at hmem

theorem arrow_impossibility
    {n m : ℕ} (hm : m ≥ 3)
    (f : (Fin n → Bool) → Bool)
    (hunanimous : IsUnanimous f)
    (hodd : IsOdd f)
    (hviable : IsArrowViable f m) :
    IsDictator f := by
  classical
  have htt := hunanimous.1
  have hff := hunanimous.2

  have hexists_inf : ∃ i : Fin n, influence f i > 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h

    have hzero : ∀ i : Fin n, influence f i = 0 := by
      intro i
      have hnn : (0 : ℝ) ≤ influence f i := by
        unfold influence
        exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
      exact le_antisymm (h i) hnn

    have hinv : ∀ i : Fin n, ∀ x : Fin n → Bool, f x = f (flipCoord x i) :=
      fun i => influence_zero_invariant f i (hzero i)

    suffices hconst : ∀ (x y : Fin n → Bool), f x = f y by
      have := hconst (fun _ => true) (fun _ => false)
      rw [htt, hff] at this; exact Bool.noConfusion this
    intro x y
    suffices hsuff : ∀ (S : Finset (Fin n)),
        ∀ (z : Fin n → Bool), (∀ k, k ∉ S → z k = y k) → f z = f y by
      exact hsuff Finset.univ x (fun k hk => absurd (Finset.mem_univ k) hk)
    intro S
    induction S using Finset.induction_on with
    | empty => intro z hz; congr 1; funext k; exact hz k (Finset.notMem_empty k)
    | insert a_elem a_set _ a_ih =>
      intro z hz
      by_cases hza : z a_elem = y a_elem
      · apply a_ih z; intro k hk
        by_cases hka : k = a_elem
        · rw [hka]; exact hza
        · exact hz k (by simp [Finset.mem_insert, hka, hk])
      · rw [hinv a_elem z]
        apply a_ih (flipCoord z a_elem); intro k hk
        by_cases hka : k = a_elem
        · rw [hka]; exact flipCoord_eq_of_ne z a_elem (y a_elem) hza
        · simp only [flipCoord, Function.update, dif_neg hka]
          exact hz k (by simp [Finset.mem_insert, hka, hk])

  obtain ⟨i₀, hi₀⟩ := hexists_inf

  have hunique : ∀ j : Fin n, j ≠ i₀ → influence f j = 0 := by
    intro j hj
    by_contra hjne
    have hjpos : influence f j > 0 := by
      have hnn : (0 : ℝ) ≤ influence f j := by
        unfold influence
        exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)

      exact lt_of_le_of_ne hnn (Ne.symm hjne)
    exact hj (arrow_viable_implies_unique_pivot hm f hviable hodd i₀ j hi₀ hjpos).symm

  have hinv_others : ∀ j : Fin n, j ≠ i₀ → ∀ x : Fin n → Bool, f x = f (flipCoord x j) :=
    fun j hj => influence_zero_invariant f j (hunique j hj)

  refine ⟨i₀, fun x => ?_⟩

  suffices hdep : f x = f (fun _ => x i₀) by
    rw [hdep]; cases hxi : x i₀ <;> simp [hxi, htt, hff]
  suffices hsuff : ∀ (S : Finset (Fin n)),
      (∀ k ∈ S, k ≠ i₀) →
      ∀ (z : Fin n → Bool), z i₀ = x i₀ → (∀ k, k ∉ S → z k = x i₀) →
      f z = f (fun _ => x i₀) by
    apply hsuff (Finset.univ.filter (fun k => k ≠ i₀))
    · intro k hk; exact (Finset.mem_filter.mp hk).2
    · exact rfl
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hk
      subst hk; rfl
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ z _ hz; congr 1; funext k; exact hz k (Finset.notMem_empty k)
  | insert a_elem a_set _ a_ih =>
    intro hne z hzi hz
    have hane : a_elem ≠ i₀ := hne a_elem (Finset.mem_insert_self a_elem a_set)
    have hne' : ∀ k ∈ a_set, k ≠ i₀ := fun k hk => hne k (Finset.mem_insert_of_mem hk)
    by_cases hza : z a_elem = x i₀
    · apply a_ih hne' z hzi; intro k hk
      by_cases hka : k = a_elem
      · rw [hka]; exact hza
      · exact hz k (by simp [Finset.mem_insert, hka, hk])
    · rw [hinv_others a_elem hane z]
      apply a_ih hne' (flipCoord z a_elem)
        (by simp only [flipCoord, Function.update, dif_neg (Ne.symm hane)]; exact hzi)
      intro k hk
      by_cases hka : k = a_elem
      · rw [hka]; exact flipCoord_eq_of_ne z a_elem (x i₀) hza
      · simp only [flipCoord, Function.update, dif_neg hka]
        exact hz k (by simp [Finset.mem_insert, hka, hk])

end BooleanFourier
