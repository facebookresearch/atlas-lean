/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
import Mathlib.Order.Filter.Basic

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

noncomputable def pairing (α x : B → ℝ) : ℝ :=
  ∑ s : B, α s * x s

def nonposRoots (Φpos : Set (B → ℝ)) (x : B → ℝ) : Set (B → ℝ) :=
  {α ∈ Φpos | pairing α x ≤ 0}

def nuFiniteAt (Φpos : Set (B → ℝ)) (x : B → ℝ) : Prop :=
  Set.Finite (nonposRoots Φpos x)

noncomputable def sigmaWord (M : CoxeterMatrix B) (ws : List B) (α : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => sigma M s v) α

noncomputable def dualSigmaWord (M : CoxeterMatrix B) (ws : List B) (x : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => dualSigma M s v) x

class RootSystemData (M : CoxeterMatrix B) where
  Φpos : Set (B → ℝ)
  roots_in_subspan_finite : ∀ (I : Finset B), I ≠ Finset.univ →
    Set.Finite {α ∈ Φpos | ∀ s : B, s ∉ I → α s = 0}
  pos_pairing_outside_span :
    ∀ (I : Finset B) (x : B → ℝ),
      x ∈ titsFaceDual M I →
      ∀ α ∈ Φpos, (∃ s : B, s ∉ I ∧ α s ≠ 0) → pairing α x > 0
  pairing_word_comm :
    ∀ (ws : List B) (α x : B → ℝ),
      pairing α (dualSigmaWord M ws x) = pairing (sigmaWord M ws.reverse α) x
  sigmaWord_injective :
    ∀ (ws : List B), Function.Injective (sigmaWord M ws)
  inversions_finite : ∀ (ws : List B),
    Set.Finite {α ∈ Φpos | ¬ (sigmaWord M ws α ∈ Φpos)}
  simple_inversion : ∀ s : B,
    {α ∈ Φpos | ¬ (sigmaWord M [s] α ∈ Φpos)} = {CoxeterGroup.e s}
  nonposRoots_finite_on_hyperplane :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) →
    ∀ (x : B → ℝ), (∑ s, v₀ s * x s = 1) →
    Set.Finite (nonposRoots Φpos x)

theorem sigma_involutive (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    CoxeterGroup.sigma M s (CoxeterGroup.sigma M s v) = v := by
  ext t
  simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply]
  by_cases hts : s = t
  · subst hts

    simp only [ite_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
               Finset.mem_univ]


    simp_rw [sub_mul]
    simp only [Finset.sum_sub_distrib]

    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
               CoxeterGroup.formVal_diag, mul_one]
    ring
  ·
    have hts' : t ≠ s := fun h => hts (h ▸ rfl)
    simp only [hts', ite_false, mul_zero, sub_zero]

theorem sigma_injective (M : CoxeterMatrix B) (s : B) :
    Function.Injective (CoxeterGroup.sigma M s) := by
  intro a b hab
  have := congr_arg (CoxeterGroup.sigma M s) hab
  rwa [sigma_involutive, sigma_involutive] at this

theorem sigmaWord_cons (M : CoxeterMatrix B) (s : B) (ws' : List B) (α : B → ℝ) :
    sigmaWord M (s :: ws') α = sigmaWord M ws' (CoxeterGroup.sigma M s α) := by
  simp [sigmaWord, List.foldl_cons]

theorem sigmaWord_injective_lemma (M : CoxeterMatrix B) (ws : List B) :
    Function.Injective (sigmaWord M ws) := by
  induction ws with
  | nil => exact Function.injective_id
  | cons s ws' ih =>
    intro a b h
    rw [sigmaWord_cons, sigmaWord_cons] at h
    exact sigma_injective M s (ih h)

theorem pairing_dualSigma_eq_sigma_pairing (M : CoxeterMatrix B) (s : B) (α x : B → ℝ) :
    pairing α (dualSigma M s x) = pairing (CoxeterGroup.sigma M s α) x := by
  simp only [pairing, dualSigma, CoxeterGroup.sigma, CoxeterGroup.bilinForm,
             CoxeterGroup.e, Pi.single_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_sub_distrib]

  congr 1


  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  ring_nf
  simp_rw [CoxeterGroup.formVal_symm M s]
  simp_rw [show ∀ t : B, α t * x s * formVal M t s * 2 = x s * 2 * (α t * formVal M t s) from
    fun t => by ring]
  rw [← Finset.mul_sum]
  ring

theorem dualSigmaWord_cons (M : CoxeterMatrix B) (s : B) (ws' : List B) (x : B → ℝ) :
    dualSigmaWord M (s :: ws') x = dualSigmaWord M ws' (dualSigma M s x) := by
  simp [dualSigmaWord, List.foldl_cons]

theorem pairing_word_comm_lemma (M : CoxeterMatrix B) (ws : List B) (α x : B → ℝ) :
    pairing α (dualSigmaWord M ws x) = pairing (sigmaWord M ws.reverse α) x := by
  induction ws generalizing α x with
  | nil => rfl
  | cons s ws' ih =>
    rw [dualSigmaWord_cons, ih α (dualSigma M s x), List.reverse_cons]
    simp only [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [pairing_dualSigma_eq_sigma_pairing]

noncomputable def standardΦpos (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {α | (∃ (ws : List B) (s : B), α = sigmaWord M ws (CoxeterGroup.e s)) ∧ (∀ t, 0 ≤ α t)}

/-- Translation between the two word-action conventions: $\sigma_w = \text{wordSigma}(w^R)$
where $w^R$ is the reversed word. -/
theorem sigmaWord_eq_wordSigma_reverse {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (ws : List B) (v : B → ℝ) :
    sigmaWord M ws v = CoxeterGroup.wordSigma M ws.reverse v := by
  induction ws generalizing v with
  | nil => simp [sigmaWord, CoxeterGroup.wordSigma]
  | cons r ws' ih =>
    simp only [sigmaWord, List.foldl_cons, List.reverse_cons]
    change sigmaWord M ws' (CoxeterGroup.sigma M r v) =
      CoxeterGroup.wordSigma M (ws'.reverse ++ [r]) v
    rw [ih (CoxeterGroup.sigma M r v)]
    rw [CoxeterGroup.wordSigma_append]
    simp [CoxeterGroup.wordSigma]

/-- A positive root $\alpha \neq e_s$ stays in $\Phi^+$ after applying $\sigma_s$.
The exception (the simple root $e_s$ itself) becomes $-e_s$, a negative root. -/
theorem sigma_preserves_pos {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (s : B) (α : B → ℝ)
    (hα : α ∈ standardΦpos M) (hne : α ≠ CoxeterGroup.e s) :
    CoxeterGroup.sigma M s α ∈ standardΦpos M := by
  obtain ⟨⟨ws, s₀, hα_eq⟩, hα_nn⟩ := hα
  constructor
  ·
    exact ⟨ws ++ [s], s₀, by rw [hα_eq]; simp [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]⟩
  ·
    set cs := M.toCoxeterSystem

    have hα_ws : α = CoxeterGroup.wordSigma M ws.reverse (CoxeterGroup.e s₀) := by
      rw [hα_eq, sigmaWord_eq_wordSigma_reverse]

    have h_sigma_ws : CoxeterGroup.sigma M s α =
        CoxeterGroup.wordSigma M (s :: ws.reverse) (CoxeterGroup.e s₀) := by
      rw [hα_ws]; rfl

    set w := cs.wordProd (s :: ws.reverse)
    obtain ⟨rw, hrw_red, hrw_prod⟩ := cs.exists_reduced_word w

    have h_wordsigma_eq : ∀ (v : B → ℝ),
        CoxeterGroup.wordSigma M (s :: ws.reverse) v =
        CoxeterGroup.wordSigma M rw v :=
      fun v => CoxeterGroup.wordSigma_eq_of_wordProd_eq M cs _ _ hrw_prod v

    by_cases hasc : cs.length (cs.wordProd rw * cs.simple s₀) > cs.length (cs.wordProd rw)
    ·
      have hpos := CoxeterGroup.pos_of_ascent M cs rw s₀ hrw_red hasc
      rw [h_sigma_ws]
      intro t
      have h := congr_fun (h_wordsigma_eq (CoxeterGroup.e s₀)) t
      rw [h]; exact hpos t
    ·
      push_neg at hasc
      have hdesc : cs.length (cs.wordProd rw * cs.simple s₀) < cs.length (cs.wordProd rw) := by
        have := cs.length_mul_simple (cs.wordProd rw) s₀; omega
      have hneg := CoxeterGroup.neg_of_descent M cs rw s₀ hrw_red hdesc


      have hα_zero : ∀ t, t ≠ s → α t = 0 := by
        intro t hts
        have hle : CoxeterGroup.wordSigma M (s :: ws.reverse) (CoxeterGroup.e s₀) t ≤ 0 := by
          rw [congr_fun (h_wordsigma_eq (CoxeterGroup.e s₀)) t]; exact hneg t
        rw [← h_sigma_ws] at hle
        have hsigma_t : CoxeterGroup.sigma M s α t = α t := by
          simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply]
          have hst : s ≠ t := fun h => hts h.symm
          have hts' : t ≠ s := fun h => hts (h ▸ rfl)
          simp only [hts', ite_false, mul_zero, sub_zero]
        rw [hsigma_t] at hle
        exact le_antisymm hle (hα_nn t)

      have hα_form : CoxeterGroup.bilinForm M α α = 1 := by
        rw [hα_ws, CoxeterGroup.wordSigma_preserves_form,
            CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]

      have hα_eq_smul : α = α s • CoxeterGroup.e s := by
        ext t
        simp only [Pi.smul_apply, smul_eq_mul, CoxeterGroup.e, Pi.single_apply]
        by_cases hts : t = s
        · subst hts; simp
        · rw [hα_zero t hts]; simp [hts]

      have hα_form2 : CoxeterGroup.bilinForm M α α = α s * α s := by
        conv_lhs => rw [hα_eq_smul]
        rw [CoxeterGroup.bilinForm_smul_left, CoxeterGroup.bilinForm_smul_right,
            CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]; ring

      have hαs : α s = 1 := by
        have hmul : α s * α s = 1 := by linarith [hα_form, hα_form2]
        have hnn := hα_nn s
        nlinarith [sq_nonneg (α s - 1)]

      exfalso; apply hne
      rw [hα_eq_smul, hαs, one_smul]

/-- Two abstract finiteness hypotheses that supply the standard $\Phi^+$ with a
`RootSystemData` structure: $(1)$ finiteness of roots supported on a proper subset,
and $(2)$ finiteness of nonposRoots on the radical hyperplane. -/
structure FiniteProperParabolicsHyp (M : CoxeterMatrix B) : Prop where
  finiteRoots_in_subspan_of_subset_finite :
    ∀ (I : Finset B), I ≠ Finset.univ →
      Set.Finite {α ∈ standardΦpos M | ∀ s : B, s ∉ I → α s = 0}
  hyperplane_nonposRoots_finite :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) →
    ∀ (x : B → ℝ), (∑ s, v₀ s * x s = 1) →
    Set.Finite (nonposRoots (standardΦpos M) x)

/-- Appending one letter: $\sigma_{w \cdot s}(\alpha) = \sigma_s(\sigma_w(\alpha))$. -/
theorem sigmaWord_append_singleton (M : CoxeterMatrix B) (ws : List B) (s : B) (α : B → ℝ) :
    sigmaWord M (ws ++ [s]) α = CoxeterGroup.sigma M s (sigmaWord M ws α) := by
  simp [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Inductive step for the finiteness of inversion sets: if the inversion set of $w$ is
finite, so is the inversion set of $w \cdot s$. -/
theorem inversions_append_finite (M : CoxeterMatrix B) (ws : List B) (s : B)
    (ih : Set.Finite {α ∈ standardΦpos M | sigmaWord M ws α ∉ standardΦpos M}) :
    Set.Finite {α ∈ standardΦpos M | sigmaWord M (ws ++ [s]) α ∉ standardΦpos M} := by


  have hsingle : Set.Finite {α ∈ standardΦpos M | sigmaWord M ws α = CoxeterGroup.e s} := by
    have : {α ∈ standardΦpos M | sigmaWord M ws α = CoxeterGroup.e s} ⊆
        sigmaWord M ws ⁻¹' {CoxeterGroup.e s} :=
      fun α ⟨_, h⟩ => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr h)
    exact Set.Finite.subset
      ((Set.finite_singleton _).preimage (Set.injOn_of_injective (sigmaWord_injective_lemma M ws)
        |>.mono (Set.subset_univ _))) this
  apply Set.Finite.subset (ih.union hsingle)
  intro α ⟨hα_pos, hα_not⟩
  rw [sigmaWord_append_singleton] at hα_not
  by_cases h : sigmaWord M ws α ∈ standardΦpos M
  ·
    right
    refine ⟨hα_pos, ?_⟩
    by_contra hne
    exact hα_not (sigma_preserves_pos M s _ h hne)
  ·
    left
    exact ⟨hα_pos, h⟩

/-- The simple root $e_s$ is positive but $\sigma_s(e_s) = -e_s$ is not in $\Phi^+$:
the unique inversion of the simple reflection $s$ is $e_s$. -/
theorem e_mem_inversion_singleton (M : CoxeterMatrix B) (s : B) :
    CoxeterGroup.e s ∈ standardΦpos M ∧
    sigmaWord M [s] (CoxeterGroup.e s) ∉ standardΦpos M := by
  constructor
  ·
    constructor
    · exact ⟨[], s, rfl⟩
    · intro t; simp [CoxeterGroup.e, Pi.single_apply]; split <;> norm_num
  ·
    simp only [sigmaWord, List.foldl_cons, List.foldl_nil]
    intro ⟨_, hnn⟩
    have h1 := hnn s
    have h2 := CoxeterGroup.sigma_e_self M s

    have : CoxeterGroup.sigma M s (CoxeterGroup.e s) s = -1 := by
      rw [h2]; simp [CoxeterGroup.e, Pi.single_apply]
    linarith

/-- Construction of `RootSystemData` from the standard positive roots, given the two
finiteness hypotheses encapsulated in `FiniteProperParabolicsHyp`. -/
noncomputable def rootSystemData_standard (M : CoxeterMatrix B)
    (hfpp : FiniteProperParabolicsHyp M) :
    RootSystemData M where
  Φpos := standardΦpos M
  roots_in_subspan_finite := fun I hI => hfpp.finiteRoots_in_subspan_of_subset_finite I hI
  pos_pairing_outside_span := by
    intro I x hx α hα hexists
    obtain ⟨_, hα_nn⟩ := hα
    obtain ⟨hx_zero, hx_pos⟩ := hx
    obtain ⟨s₀, hs₀_notI, hs₀_ne⟩ := hexists
    unfold pairing
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (hα_nn i)
      by_cases hi : i ∈ I
      · rw [hx_zero i hi]
      · exact le_of_lt (hx_pos i hi)
    · exact ⟨s₀, Finset.mem_univ s₀,
        mul_pos (lt_of_le_of_ne (hα_nn s₀) (Ne.symm hs₀_ne))
          (hx_pos s₀ hs₀_notI)⟩
  pairing_word_comm := fun ws α x => pairing_word_comm_lemma M ws α x
  sigmaWord_injective := fun ws => sigmaWord_injective_lemma M ws
  inversions_finite := by
    intro ws
    induction ws using List.reverseRecOn with
    | nil =>

      convert Set.finite_empty
      ext α; simp [standardΦpos, sigmaWord]
    | append_singleton ws' s ih =>
      exact inversions_append_finite M ws' s ih
  simple_inversion := by
    intro s
    ext α
    simp only [Set.mem_sep_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hα_pos, hα_not⟩

      simp only [sigmaWord, List.foldl_cons, List.foldl_nil] at hα_not
      by_contra hne
      exact hα_not (sigma_preserves_pos M s α hα_pos hne)
    · intro h; subst h
      exact e_mem_inversion_singleton M s
  nonposRoots_finite_on_hyperplane :=
    fun v₀ hv₀_pos hv₀_rad x hx =>
      hfpp.hyperplane_nonposRoots_finite v₀ hv₀_pos hv₀_rad x hx

variable (M : CoxeterMatrix B) [RootSystemData M]

/-- Every point of a proper face $F_I$ (with $I \neq \emptyset$, i.e. $I \neq$ all simple
roots) has nu-finiteness: only finitely many positive roots pair nonpositively. -/
theorem face_subset_nuFinite (I : Finset B) (hI : I ≠ Finset.univ)
    (x : B → ℝ) (hx : x ∈ titsFaceDual M I) :
    nuFiniteAt (RootSystemData.Φpos (M := M)) x := by
  unfold nuFiniteAt nonposRoots
  apply Set.Finite.subset (RootSystemData.roots_in_subspan_finite (M := M) I hI)
  intro α ⟨hαpos, hαpair⟩
  refine ⟨hαpos, ?_⟩
  intro s hs
  by_contra hne
  have hpos := RootSystemData.pos_pairing_outside_span I x hx α hαpos ⟨s, hs, hne⟩
  linarith

/-- The $W$-translate $w \cdot F_I$ of a proper Tits face is nu-finite at every point.
This bounds the nonposRoots set by inversions plus translated face-finiteness. -/
theorem wAction_face_nuFinite (ws : List B) (I : Finset B) (hI : I ≠ Finset.univ)
    (y : B → ℝ) (hy : y ∈ titsFaceDual M I) :
    nuFiniteAt (RootSystemData.Φpos (M := M))
      (dualSigmaWord M ws y) := by
  unfold nuFiniteAt nonposRoots
  set Φ := RootSystemData.Φpos (M := M)
  set wsRev := ws.reverse

  set A : Set (B → ℝ) := {α ∈ Φ | ¬ (sigmaWord M wsRev α ∈ Φ)}

  set B' : Set (B → ℝ) := {α ∈ Φ | sigmaWord M wsRev α ∈ Φ ∧
    pairing (sigmaWord M wsRev α) y ≤ 0}
  have hA_finite : A.Finite := RootSystemData.inversions_finite wsRev
  have hFI_finite : Set.Finite (nonposRoots Φ y) := face_subset_nuFinite M I hI y hy

  have hB'_finite : B'.Finite := by
    apply Set.Finite.subset (hFI_finite.preimage
      (RootSystemData.sigmaWord_injective (M := M) wsRev).injOn)
    intro α ⟨_, hact_in, hpair⟩
    exact ⟨hact_in, hpair⟩

  apply Set.Finite.subset (hA_finite.union hB'_finite)
  intro α ⟨hαpos, hαpair⟩

  rw [RootSystemData.pairing_word_comm ws α y] at hαpair
  by_cases hact : sigmaWord M wsRev α ∈ Φ
  · right; exact ⟨hαpos, hact, hαpair⟩
  · left; exact ⟨hαpos, hact⟩

/-- `dualSigmaWord` and `wordAction` are definitionally equal: both fold $\sigma^\vee_s$
left-to-right along the word. -/
theorem dualSigmaWord_eq_wordAction {M : CoxeterMatrix B} (ws : List B) (x : B → ℝ) :
    dualSigmaWord M ws x = wordAction M ws x := rfl

/-- The dual simple reflection fixes the origin: $\sigma^\vee_s(0) = 0$. -/
theorem dualSigma_zero (M : CoxeterMatrix B) (s : B) :
    dualSigma M s 0 = 0 := by
  ext t; simp [dualSigma]

/-- Any word fixes the origin: $w \cdot 0 = 0$. -/
theorem wordAction_zero (M : CoxeterMatrix B) (ws : List B) :
    wordAction M ws 0 = 0 := by
  induction ws with
  | nil => simp [wordAction]
  | cons s ws' ih =>
    rw [wordAction_cons, dualSigma_zero]
    exact ih

/-- Each point of the fundamental closure is either the origin or lies in some proper
face $F_I$ with $I$ the set of vanishing coordinates. -/
theorem closure_mem_zero_or_face (M : CoxeterMatrix B) (y : B → ℝ)
    (hy : y ∈ titsFundamentalClosure M) :
    y = 0 ∨ ∃ (I : Finset B), I ≠ Finset.univ ∧ y ∈ titsFaceDual M I := by
  by_cases h0 : y = 0
  · left; exact h0
  · right

    push Not at h0
    have hy_nn : ∀ s, y s ≥ 0 := hy

    have ⟨s₀, hs₀⟩ : ∃ s₀, y s₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact h0 (funext hall)

    let I : Finset B := Finset.univ.filter (fun s => y s = 0)
    use I
    constructor
    ·
      intro heq
      have : s₀ ∈ I := heq ▸ Finset.mem_univ s₀
      simp [I] at this
      exact hs₀ this
    ·
      constructor
      · intro s hs
        simp [I] at hs
        exact hs
      · intro s hs
        simp [I] at hs
        exact lt_of_le_of_ne (hy_nn s) (Ne.symm hs)

/-- Face decomposition of the Tits cone: every $x \in U$ is either zero or lies in
the $W$-translate of a proper Tits face $F_I$. -/
theorem titsCone_face_decomp (M : CoxeterMatrix B) (x : B → ℝ) (hx : x ∈ titsConeSet M) :
    x = 0 ∨ ∃ (I : Finset B) (ws : List B) (y : B → ℝ),
      I ≠ Finset.univ ∧ y ∈ titsFaceDual M I ∧
      x = dualSigmaWord M ws y := by

  obtain ⟨ws, y, hy_clos, hx_eq⟩ := fundamental_domain_existence M x hx

  rcases closure_mem_zero_or_face M y hy_clos with rfl | ⟨I, hI, hy_face⟩
  ·
    left
    rw [hx_eq, wordAction_zero]
  ·
    right
    exact ⟨I, ws, y, hI, hy_face, by rw [hx_eq, dualSigmaWord_eq_wordAction]⟩

/-- Evaluation at the standard basis vector $e_s$: $\langle e_s, x\rangle = x_s$. -/
lemma pairing_e (s : B) (x : B → ℝ) :
    pairing (CoxeterGroup.e s) x = x s := by
  simp only [pairing, CoxeterGroup.e, Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Singleton word: $\sigma_{[s]} = \sigma_s$. -/
lemma sigmaWord_singleton (s : B) (α : B → ℝ) :
    sigmaWord M [s] α = CoxeterGroup.sigma M s α := by
  simp [sigmaWord, List.foldl_cons, List.foldl_nil]

/-- Negation in the first argument: $\langle-\alpha, x\rangle = -\langle\alpha, x\rangle$. -/
lemma pairing_neg (α x : B → ℝ) :
    pairing (fun t => -(α t)) x = -(pairing α x) := by
  simp only [pairing, neg_mul, Finset.sum_neg_distrib]

/-- Sign-flip identity: $\langle e_s, \sigma^\vee_s y\rangle = -y_s$. -/
lemma pairing_e_dualSigma (s : B) (y : B → ℝ) :
    pairing (CoxeterGroup.e s) (dualSigma M s y) = -(y s) := by
  rw [pairing_dualSigma_eq_sigma_pairing]
  rw [CoxeterGroup.sigma_e_self]
  rw [pairing_neg, pairing_e]

/-- If $y_s < 0$ and $e_s \in \Phi^+$, then $e_s$ belongs to the set of positive roots
with nonpositive pairing at $y$. -/
lemma e_mem_nonposRoots_of_neg [RootSystemData M] (s : B) (y : B → ℝ) (hs : y s < 0)
    (he_mem : CoxeterGroup.e s ∈ RootSystemData.Φpos (M := M)) :
    CoxeterGroup.e s ∈ nonposRoots (RootSystemData.Φpos (M := M)) y :=
  ⟨he_mem, by rw [pairing_e]; exact le_of_lt hs⟩

/-- The simple root $e_s$ is not in the image of $\sigma_s$ on the nonposRoots of
$\sigma^\vee_s y$, used to obtain a strict cardinality drop in the induction. -/
lemma e_not_in_sigmaWord_image [RootSystemData M] (s : B) (y : B → ℝ) (hs : y s < 0) :
    CoxeterGroup.e s ∉ sigmaWord M [s] '' nonposRoots (RootSystemData.Φpos (M := M)) (dualSigma M s y) := by
  intro ⟨α, ⟨hαΦ, _⟩, hαeq⟩


  rw [sigmaWord_singleton] at hαeq
  have hα_eq : α = CoxeterGroup.sigma M s (CoxeterGroup.e s) := by
    have := congr_arg (CoxeterGroup.sigma M s) hαeq
    rwa [sigma_involutive] at this

  rw [hα_eq, CoxeterGroup.sigma_e_self] at hαΦ


  have h_inv := RootSystemData.simple_inversion (M := M) s
  have h_es : CoxeterGroup.e s ∈ ({CoxeterGroup.e s} : Set (B → ℝ)) := Set.mem_singleton _
  rw [← h_inv] at h_es
  exact h_es.2 (by rwa [sigmaWord_singleton, CoxeterGroup.sigma_e_self])

/-- Converse direction of the Tits cone characterisation: any $x \neq 0$ satisfying
nu-finiteness lies in $U$. The proof inducts on the cardinality of the nonposRoots set,
using a simple reflection at a negative coordinate to strictly shrink it. -/
lemma nuFinite_mem_titsCone (x : B → ℝ) (_hx : x ≠ 0)
    (hnu : nuFiniteAt (RootSystemData.Φpos (M := M)) x) :
    x ∈ titsConeSet M := by

  set Φ := RootSystemData.Φpos (M := M) with hΦ_def

  have he_mem : ∀ s : B, CoxeterGroup.e s ∈ Φ := by
    intro s
    have h := RootSystemData.simple_inversion (M := M) s
    have : CoxeterGroup.e s ∈ ({CoxeterGroup.e s} : Set (B → ℝ)) := Set.mem_singleton _
    rw [← h] at this; exact this.1

  suffices h_gen : ∀ (n : ℕ) (y : B → ℝ) (hfin : nuFiniteAt Φ y),
      hfin.toFinset.card ≤ n → y ∈ titsConeSet M by
    exact h_gen hnu.toFinset.card x hnu le_rfl
  intro n
  induction n with
  | zero =>
    intro y hfin hcard
    have hempty : hfin.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hpos : ∀ s, y s ≥ 0 := by
      intro s
      by_contra h_neg
      push_neg at h_neg
      have : CoxeterGroup.e s ∈ nonposRoots Φ y :=
        ⟨he_mem s, by rw [pairing_e]; exact le_of_lt h_neg⟩
      have := hfin.mem_toFinset.mpr this
      rw [hempty] at this
      exact Finset.notMem_empty _ this

    exact titsFundamentalClosure_subset_titsCone M hpos
  | succ n ih =>
    intro y hfin hcard
    by_cases h_all_nn : ∀ s, y s ≥ 0
    · exact titsFundamentalClosure_subset_titsCone M h_all_nn
    · push_neg at h_all_nn
      obtain ⟨s, hs_lt⟩ := h_all_nn

      suffices h_inner : dualSigma M s y ∈ titsConeSet M by


        obtain ⟨z, hz, ws, hws⟩ := h_inner
        refine ⟨z, hz, ws ++ [s], ?_⟩
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [← hws, dualSigma_involutive]


      have h_inj : ∀ α ∈ nonposRoots Φ (dualSigma M s y),
          sigmaWord M [s] α ∈ nonposRoots Φ y := by
        intro α ⟨hαΦ, hαpair⟩
        constructor
        ·
          by_contra h_not
          have h_inv := RootSystemData.simple_inversion (M := M) s
          have : α ∈ {α ∈ Φ | ¬ (sigmaWord M [s] α ∈ Φ)} := ⟨hαΦ, h_not⟩
          rw [h_inv] at this

          have hα_eq := Set.mem_singleton_iff.mp this

          rw [hα_eq] at hαpair
          have := pairing_e_dualSigma M s y
          linarith
        ·
          have hpw := RootSystemData.pairing_word_comm (M := M) [s] α y
          simp only [List.reverse_singleton] at hpw
          have h_dsw : dualSigmaWord M [s] y = dualSigma M s y := by
            simp [dualSigmaWord, List.foldl_cons, List.foldl_nil]
          rw [h_dsw] at hpw
          linarith

      have hfin' : nuFiniteAt Φ (dualSigma M s y) := by
        unfold nuFiniteAt
        exact (hfin.preimage
          (RootSystemData.sigmaWord_injective (M := M) [s]).injOn).subset
          (fun α hα => h_inj α hα)

      have he_in : CoxeterGroup.e s ∈ nonposRoots Φ y :=
        e_mem_nonposRoots_of_neg M s y hs_lt (he_mem s)
      have he_not_img : CoxeterGroup.e s ∉
          sigmaWord M [s] '' nonposRoots Φ (dualSigma M s y) :=
        e_not_in_sigmaWord_image M s y hs_lt
      have hcard_lt : hfin'.toFinset.card < hfin.toFinset.card := by
        have h_img_sub : hfin'.toFinset.image (sigmaWord M [s]) ⊆ hfin.toFinset := by
          intro β hβ
          rw [Finset.mem_image] at hβ
          obtain ⟨α, hα_mem, rfl⟩ := hβ
          rw [Set.Finite.mem_toFinset] at hα_mem ⊢
          exact h_inj α hα_mem
        have h_img_card : (hfin'.toFinset.image (sigmaWord M [s])).card =
            hfin'.toFinset.card := by
          rw [Finset.card_image_of_injective _
            (RootSystemData.sigmaWord_injective (M := M) [s])]
        have he_fin : CoxeterGroup.e s ∈ hfin.toFinset :=
          hfin.mem_toFinset.mpr he_in
        have he_not_fin : CoxeterGroup.e s ∉
            hfin'.toFinset.image (sigmaWord M [s]) := by
          intro h
          rw [Finset.mem_image] at h
          obtain ⟨α, hα_mem, hαeq⟩ := h
          exact he_not_img ⟨α, hfin'.mem_toFinset.mp hα_mem, hαeq⟩
        calc hfin'.toFinset.card
            = (hfin'.toFinset.image (sigmaWord M [s])).card := h_img_card.symm
          _ < hfin.toFinset.card := by
              apply Finset.card_lt_card
              exact Finset.ssubset_iff_of_subset h_img_sub |>.mpr
                ⟨CoxeterGroup.e s, he_fin, he_not_fin⟩

      exact ih (dualSigma M s y) hfin' (by omega)

/-- Main characterisation of the Tits cone: $U = \{0\} \cup \{x : \text{nu-finite at } x\}$.
A point lies in $U$ iff it is zero or only finitely many positive roots are nonpositive on it. -/
theorem titsCone_eq_zero_union_nuFinite :
    titsConeSet M =
      {x : B → ℝ | x = 0} ∪ {x : B → ℝ | nuFiniteAt (RootSystemData.Φpos (M := M)) x} := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  ·
    intro hx
    rcases titsCone_face_decomp M x hx with rfl | ⟨I, ws, y, hI, hy, rfl⟩
    · left; rfl
    · right; exact wAction_face_nuFinite M ws I hI y hy
  ·
    intro h
    rcases h with rfl | hnu
    ·
      apply titsFundamentalClosure_subset_titsCone
      simp only [titsFundamentalClosure, Set.mem_setOf_eq, Pi.zero_apply, le_refl,
        implies_true]
    ·
      by_cases hx : x = 0
      · subst hx
        apply titsFundamentalClosure_subset_titsCone
        simp only [titsFundamentalClosure, Set.mem_setOf_eq, Pi.zero_apply, le_refl,
          implies_true]
      · exact nuFinite_mem_titsCone M x hx hnu

end TitsCone
