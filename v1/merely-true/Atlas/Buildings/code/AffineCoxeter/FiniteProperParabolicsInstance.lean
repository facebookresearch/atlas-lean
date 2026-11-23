/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
import Atlas.Buildings.code.AffineCoxeter.LatticeFiniteness

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Every positive root $\alpha \in \Phi^+$ has unit length for the Coxeter form: $B(\alpha,\alpha) = 1$.
This follows from the fact that simple roots have unit length and the form is $W$-invariant. -/
lemma standardΦpos_form_eq_one (M : CoxeterMatrix B)
    (α : B → ℝ) (hα : α ∈ standardΦpos M) :
    CoxeterGroup.bilinForm M α α = 1 := by
  obtain ⟨⟨ws, s₀, hα_eq⟩, _⟩ := hα
  rw [hα_eq, sigmaWord_eq_wordSigma_reverse, CoxeterGroup.wordSigma_preserves_form,
      CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]

/-- Hypotheses isolating the two key properties of an affine, crystallographic Coxeter system used
in the proofs: (1) coercivity of the form $B$ on every proper parabolic subspace, and
(2) integrality of the coordinates of every positive root in the simple-root basis. -/
structure AffineCoxeterHyp (M : CoxeterMatrix B) : Prop where
  coercive_on_proper_subset :
    ∀ (I : Finset B), I ≠ Finset.univ →
      ∃ (c : ℝ), 0 < c ∧
        ∀ (v : B → ℝ), (∀ s, s ∉ I → v s = 0) →
          c * ∑ b : B, (v b) ^ 2 ≤ CoxeterGroup.bilinForm M v v
  roots_integer_coords :
    ∀ α ∈ standardΦpos M, ∀ b : B, ∃ n : ℤ, α b = ↑n

/-- Under the affine Coxeter hypothesis, the set of positive roots supported on any proper subset
$I \subsetneq B$ of simple reflections is **finite**. This is the "spherical-on-parabolics"
finiteness statement and is what makes proper parabolic subgroups finite. -/
theorem finiteRoots_in_subspan_of_AffineCoxeterHyp
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M) :
    ∀ (I : Finset B), I ≠ Finset.univ →
      Set.Finite {α ∈ standardΦpos M | ∀ s : B, s ∉ I → α s = 0} := by
  intro I hI
  set S := {α ∈ standardΦpos M | ∀ s : B, s ∉ I → α s = 0}

  obtain ⟨c, hc_pos, hcoerce⟩ := hyp.coercive_on_proper_subset I hI


  have hL2 : ∀ α ∈ S, ∑ b : B, (α b) ^ 2 ≤ 1 / c := by
    intro α ⟨hαΦ, hα_supp⟩
    have h1 := hcoerce α hα_supp
    have h2 := standardΦpos_form_eq_one M α hαΦ
    have hle : c * ∑ b : B, (α b) ^ 2 ≤ 1 := h2 ▸ h1
    have : c * (∑ b : B, (α b) ^ 2) / c ≤ 1 / c :=
      div_le_div_of_nonneg_right hle hc_pos.le
    rwa [mul_div_cancel_left₀ _ (ne_of_gt hc_pos)] at this

  have hcoord_sq : ∀ α ∈ S, ∀ b : B, (α b) ^ 2 ≤ 1 / c := by
    intro α hα b
    calc (α b) ^ 2
        ≤ ∑ b' : B, (α b') ^ 2 :=
          single_le_sum (fun i _ => sq_nonneg (α i)) (mem_univ b)
      _ ≤ 1 / c := hL2 α hα

  have hcoord : ∀ α ∈ S, ∀ b : B, α b ≤ Real.sqrt (1 / c) := by
    intro α ⟨hαΦ, hα_supp⟩ b
    have hnn : 0 ≤ α b := hαΦ.2 b
    rw [← Real.sqrt_sq hnn]
    exact Real.sqrt_le_sqrt (hcoord_sq _ ⟨hαΦ, hα_supp⟩ b)

  set bound := Real.sqrt (1 / c)
  set T : B → Set ℝ := fun _ =>
    {x : ℝ | (∃ n : ℤ, x = ↑n) ∧ 0 ≤ x ∧ x ≤ bound}
  have hT_finite : ∀ b : B, (T b).Finite := by
    intro b
    apply Set.Finite.subset
      ((Set.finite_Icc (0 : ℤ) ⌊bound⌋).image (Int.cast : ℤ → ℝ))
    intro x ⟨⟨n, hn⟩, hx0, hxM⟩
    exact ⟨n, ⟨by exact_mod_cast hn ▸ hx0, Int.le_floor.mpr (hn ▸ hxM)⟩, hn.symm⟩
  have hS_sub : S ⊆ Set.univ.pi T := by
    intro α ⟨hαΦ, hα_supp⟩ b _
    exact ⟨hyp.roots_integer_coords α hαΦ b, hαΦ.2 b, hcoord _ ⟨hαΦ, hα_supp⟩ b⟩
  exact (Set.Finite.pi hT_finite).subset hS_sub

/-- Shifting by a radical vector does not change the Coxeter form: $B(w - a v_0, w - a v_0) = B(w,w)$
when $v_0 \in \mathrm{rad}(B)$. -/
lemma bilinForm_radical_shift_eq
    (M : CoxeterMatrix B) (v₀ w : B → ℝ) (a : ℝ)
    (hrad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
    ∑ s, ∑ t, (w s - a * v₀ s) * CoxeterGroup.formVal M s t * (w t - a * v₀ t) =
    ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := by
  have expand : ∀ s t,
      (w s - a * v₀ s) * CoxeterGroup.formVal M s t * (w t - a * v₀ t)
      = w s * CoxeterGroup.formVal M s t * w t
      + (-a) * (v₀ s * CoxeterGroup.formVal M s t * w t)
      + (-a) * (w s * CoxeterGroup.formVal M s t * v₀ t)
      + (-a) ^ 2 * (v₀ s * CoxeterGroup.formVal M s t * v₀ t) := by intros; ring
  simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ s, ∑ t, v₀ s * CoxeterGroup.formVal M s t * w t = 0 := by
    trans ∑ t, (∑ s, v₀ s * CoxeterGroup.formVal M s t) * w t
    · rw [Finset.sum_comm]; congr 1; ext t; rw [Finset.sum_mul]
    · simp only [hrad, zero_mul, Finset.sum_const_zero]
  have h2 : ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * v₀ t = 0 := by
    trans ∑ s, w s * (∑ t, CoxeterGroup.formVal M s t * v₀ t)
    · congr 1; ext s; rw [Finset.mul_sum]; congr 1; ext t; ring
    · have hcol : ∀ s, ∑ t, CoxeterGroup.formVal M s t * v₀ t = 0 := by
        intro s
        have : ∑ t, CoxeterGroup.formVal M s t * v₀ t =
            ∑ t, v₀ t * CoxeterGroup.formVal M t s := by
          congr 1; ext t; rw [CoxeterGroup.formVal_symm M s t, mul_comm]
        rw [this]; exact hrad s
      simp only [hcol, mul_zero, Finset.sum_const_zero]
  have h3 : ∑ s, ∑ t, v₀ s * CoxeterGroup.formVal M s t * v₀ t = 0 := by
    trans ∑ t, (∑ s, v₀ s * CoxeterGroup.formVal M s t) * v₀ t
    · rw [Finset.sum_comm]; congr 1; ext t; rw [Finset.sum_mul]
    · simp only [hrad, zero_mul, Finset.sum_const_zero]
  rw [h1, h2, h3]; ring

/-- Pythagoras-style inequality: if $w \perp v_0$ then $\|w\|^2 \le \|w - a v_0\|^2$ for any $a$. -/
lemma norm_sq_le_of_perp_shift
    (v₀ w : B → ℝ) (a : ℝ) (hperp : ∑ s, v₀ s * w s = 0) :
    ∑ s, w s ^ 2 ≤ ∑ s, (w s - a * v₀ s) ^ 2 := by
  simp_rw [sub_eq_add_neg, add_pow_two]
  simp only [Finset.sum_add_distrib]
  have h1 : ∑ s, 2 * w s * (-(a * v₀ s)) = -2 * a * ∑ s, v₀ s * w s := by
    simp only [Finset.mul_sum]; congr 1; ext s; ring
  rw [h1, hperp, mul_zero]
  linarith [Finset.sum_nonneg (fun s (_ : s ∈ univ) => sq_nonneg (-(a * v₀ s)))]

/-- The Coxeter form $B$ is coercive on the hyperplane $v_0^{\perp}$: there exists $c > 0$ with
$c \|w\|^2 \le B(w,w)$ for all $w$ with $\langle v_0, w \rangle = 0$. This is the key spectral
estimate driving finiteness of nonpositive-roots sets. -/
theorem bilinForm_on_v0_perp_coercive
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M)
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
    ∃ c_min : ℝ, c_min > 0 ∧
      ∀ w : B → ℝ, (∑ s, v₀ s * w s = 0) →
        c_min * ∑ s, w s ^ 2 ≤ ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := by
  by_cases hB : IsEmpty B
  · exact ⟨1, one_pos, fun w _ => by simp [Finset.eq_empty_of_isEmpty]⟩
  rw [not_isEmpty_iff] at hB
  obtain ⟨s₀⟩ := hB
  have hI : Finset.univ.erase s₀ ≠ Finset.univ :=
    Finset.erase_ne_self.mpr (Finset.mem_univ s₀)
  obtain ⟨c, hc_pos, hc⟩ := hyp.coercive_on_proper_subset _ hI
  refine ⟨c, hc_pos, fun w hperp => ?_⟩
  set a := w s₀ / v₀ s₀ with ha_def
  have hv₀_ne : v₀ s₀ ≠ 0 := ne_of_gt (hv₀_pos s₀)
  have hu_s₀ : w s₀ - a * v₀ s₀ = 0 := by
    rw [ha_def, div_mul_cancel₀ _ hv₀_ne, sub_self]
  have hu_supp : ∀ s, s ∉ Finset.univ.erase s₀ → (fun b => w b - a * v₀ b) s = 0 := by
    intro s hs
    rw [Finset.mem_erase, not_and_or, Decidable.not_not] at hs
    rcases hs with hs | hs
    · rw [hs]; exact hu_s₀
    · exact absurd (Finset.mem_univ s) hs
  have hBu := hc _ hu_supp
  have hBuw : (∑ s, ∑ t, (fun b => w b - a * v₀ b) s *
      CoxeterGroup.formVal M s t * (fun b => w b - a * v₀ b) t) =
      ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := by
    simp only []
    exact bilinForm_radical_shift_eq M v₀ w a hv₀_radical
  have hu_norm : ∑ s, w s ^ 2 ≤ ∑ s, (fun b => w b - a * v₀ b) s ^ 2 := by
    simp only []
    exact norm_sq_le_of_perp_shift v₀ w a hperp
  calc c * ∑ s, w s ^ 2
      ≤ c * ∑ s, (fun b => w b - a * v₀ b) s ^ 2 :=
        mul_le_mul_of_nonneg_left hu_norm hc_pos.le
    _ ≤ ∑ s, ∑ t, (fun b => w b - a * v₀ b) s *
        CoxeterGroup.formVal M s t * (fun b => w b - a * v₀ b) t := hBu
    _ = ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := hBuw

/-- Cauchy–Schwarz with a bound: $|\langle a, b\rangle| \le \sqrt C \cdot \|b\|$ when $\|a\|^2 \le C$. -/
lemma abs_inner_le_sqrt_norms
    (a b : B → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∑ s, (a s) ^ 2 ≤ C) :
    |∑ s, a s * b s| ≤ Real.sqrt C * Real.sqrt (∑ s, (b s) ^ 2) := by
  have hle' : (∑ s, a s * b s) ^ 2 ≤ (Real.sqrt C * Real.sqrt (∑ s, (b s) ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg (b s)))]
    calc (∑ s, a s * b s) ^ 2
        ≤ (∑ s, (a s) ^ 2) * (∑ s, (b s) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
      _ ≤ C * ∑ s, (b s) ^ 2 :=
          mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg (fun s _ => sq_nonneg (b s)))
  rw [abs_le]
  exact abs_le_of_sq_le_sq' hle' (by positivity)

/-- Pythagoras decomposition: $\|c v_0 + w\|^2 = c^2 \|v_0\|^2 + \|w\|^2$ when $w \perp v_0$. -/
lemma sum_sq_orth_decomp
    (v₀ w : B → ℝ) (c : ℝ) (hperp : ∑ s, v₀ s * w s = 0) :
    ∑ s : B, (c * v₀ s + w s) ^ 2 = c ^ 2 * ∑ s, (v₀ s) ^ 2 + ∑ s, (w s) ^ 2 := by
  simp_rw [add_pow_two, mul_pow, Finset.sum_add_distrib]
  have h : ∑ s, 2 * (c * v₀ s) * w s = 2 * c * ∑ s, v₀ s * w s := by
    rw [Finset.mul_sum]; congr 1; ext s; ring
  rw [h, hperp, mul_zero, add_zero, ← Finset.mul_sum]

/-- Uniform coordinate bound: every root $\alpha \in \Phi^+$ with $\langle \alpha, x\rangle \le 0$
has all coordinates in $[0, C]$ for a constant $C$ depending only on $v_0$, $x$, and the coercivity
constant. -/
theorem nonposRoots_coord_bound
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M)
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hx_hyp : ∑ s, v₀ s * x s = 1)
    (hcoercive : ∃ c_min : ℝ, c_min > 0 ∧
      ∀ w : B → ℝ, (∑ s, v₀ s * w s = 0) →
        c_min * ∑ s, w s ^ 2 ≤ ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t) :
    ∃ C : ℝ, ∀ α ∈ nonposRoots (standardΦpos M) x, ∀ s : B, α s ≤ C ∧ 0 ≤ α s := by
  by_cases hB : IsEmpty B
  · exact ⟨0, fun α hα => hB.elim⟩
  rw [not_isEmpty_iff] at hB; obtain ⟨s₀⟩ := hB
  haveI : Nonempty B := ⟨s₀⟩
  obtain ⟨c_min, hc_pos, hcoerc⟩ := hcoercive

  set norm_v₀_sq := ∑ s, (v₀ s) ^ 2
  set norm_x_sq := ∑ s, (x s) ^ 2
  have hv₀_sq_pos : 0 < norm_v₀_sq :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hv₀_pos i)) Finset.univ_nonempty

  set bound := (1 / c_min) * (norm_x_sq * norm_v₀_sq + 1)
  refine ⟨Real.sqrt bound, fun α hα s => ?_⟩
  obtain ⟨hαΦ, hαx⟩ := hα
  constructor
  ·

    set c_α := (∑ t, α t * v₀ t) / norm_v₀_sq
    set w := fun t => α t - c_α * v₀ t

    have hw_perp : ∑ t, v₀ t * w t = 0 := by
      show ∑ t, v₀ t * (α t - c_α * v₀ t) = 0
      have hstep : ∀ t, v₀ t * (α t - c_α * v₀ t) =
        v₀ t * α t - c_α * (v₀ t) ^ 2 := by intro t; ring
      simp_rw [hstep]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hcancel : c_α * norm_v₀_sq = ∑ t, α t * v₀ t :=
        div_mul_cancel₀ _ (ne_of_gt hv₀_sq_pos)
      rw [hcancel]
      have : ∑ x : B, v₀ x * α x = ∑ t : B, α t * v₀ t := by
        congr 1; ext t; ring
      linarith

    have hBw_eq : ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t = 1 := by
      have hshift := bilinForm_radical_shift_eq M v₀ α c_α hv₀_radical
      have hform : bilinForm M α α = 1 := standardΦpos_form_eq_one M α hαΦ

      unfold bilinForm at hform

      change ∑ s, ∑ t, (α s - c_α * v₀ s) * CoxeterGroup.formVal M s t * (α t - c_α * v₀ t) = 1
      linarith

    have hw_coerc := hcoerc w hw_perp
    have hw_sq_le : ∑ t, (w t) ^ 2 ≤ 1 / c_min := by
      rw [le_div_iff₀ hc_pos]
      have := hBw_eq ▸ hw_coerc
      linarith [mul_comm c_min (∑ t, (w t) ^ 2)]

    have hpairing_decomp : ∑ t, α t * x t = c_α * (∑ t, v₀ t * x t) + ∑ t, w t * x t := by
      have : ∀ t, α t * x t = c_α * (v₀ t * x t) + w t * x t := by
        intro t; simp only [w]; ring
      simp_rw [this, Finset.sum_add_distrib, Finset.mul_sum]
    have hαx' : ∑ t, α t * x t ≤ 0 := by exact hαx
    have hc_le_neg_wx : c_α ≤ -(∑ t, w t * x t) := by
      rw [hx_hyp] at hpairing_decomp; linarith
    have hc_α_le : c_α ≤ Real.sqrt (1 / c_min) * Real.sqrt norm_x_sq := calc
      c_α ≤ -(∑ t, w t * x t) := hc_le_neg_wx
      _ ≤ |∑ t, w t * x t| := neg_le_abs _
      _ ≤ Real.sqrt (1 / c_min) * Real.sqrt norm_x_sq :=
          abs_inner_le_sqrt_norms w x (by positivity) hw_sq_le

    have hc_α_nn : 0 ≤ c_α := by
      apply div_nonneg _ hv₀_sq_pos.le
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (hαΦ.2 t) (hv₀_pos t).le)

    have hc_sq_le : c_α ^ 2 ≤ (1 / c_min) * norm_x_sq := by
      calc c_α ^ 2 ≤ (Real.sqrt (1 / c_min) * Real.sqrt norm_x_sq) ^ 2 :=
            sq_le_sq' (by linarith) hc_α_le
        _ = (1 / c_min) * norm_x_sq := by
            rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / c_min),
                Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg (x s)))]

    have hα_rewrite : ∀ t, α t = c_α * v₀ t + w t := by intro t; simp [w]
    have hα_sq_eq : ∑ t, (α t) ^ 2 = c_α ^ 2 * norm_v₀_sq + ∑ t, (w t) ^ 2 := by
      conv_lhs => arg 2; ext t; rw [hα_rewrite t]
      exact sum_sq_orth_decomp v₀ w c_α hw_perp
    have hα_sq_le : ∑ t, (α t) ^ 2 ≤ bound := by
      rw [hα_sq_eq]
      have h1 : c_α ^ 2 * norm_v₀_sq ≤ (1 / c_min) * norm_x_sq * norm_v₀_sq :=
        mul_le_mul_of_nonneg_right hc_sq_le hv₀_sq_pos.le
      have h2 : ∑ t, (w t) ^ 2 ≤ 1 / c_min := hw_sq_le
      calc c_α ^ 2 * norm_v₀_sq + ∑ t, (w t) ^ 2
          ≤ 1 / c_min * norm_x_sq * norm_v₀_sq + 1 / c_min := by linarith
        _ = (1 / c_min) * (norm_x_sq * norm_v₀_sq + 1) := by ring

    calc α s ≤ Real.sqrt ((α s) ^ 2) := by rw [Real.sqrt_sq (hαΦ.2 s)]
      _ ≤ Real.sqrt (∑ t, (α t) ^ 2) :=
          Real.sqrt_le_sqrt (single_le_sum (fun i _ => sq_nonneg (α i)) (mem_univ s))
      _ ≤ Real.sqrt bound := Real.sqrt_le_sqrt hα_sq_le
  · exact hαΦ.2 s

/-- Combining the coordinate bound with integrality: for $x$ on the affine hyperplane, the set of
positive roots with $\langle \alpha, x\rangle \le 0$ is **finite**. -/
theorem hyperplane_nonposRoots_finite_axiom
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M)
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ)
    (hx_hyp : ∑ s, v₀ s * x s = 1) :
    Set.Finite (nonposRoots (standardΦpos M) x) := by

  have hcoerc := bilinForm_on_v0_perp_coercive M hyp v₀ hv₀_pos hv₀_radical

  obtain ⟨C, hC⟩ := nonposRoots_coord_bound M hyp v₀ hv₀_pos hv₀_radical x hx_hyp hcoerc

  set S := nonposRoots (standardΦpos M) x
  set T : B → Set ℝ := fun _ =>
    {r : ℝ | (∃ n : ℤ, r = ↑n) ∧ 0 ≤ r ∧ r ≤ C}
  have hT_finite : ∀ b : B, (T b).Finite := by
    intro b
    apply Set.Finite.subset
      ((Set.finite_Icc (0 : ℤ) ⌊C⌋).image (Int.cast : ℤ → ℝ))
    intro r ⟨⟨n, hn⟩, hr0, hrC⟩
    exact ⟨n, ⟨by exact_mod_cast hn ▸ hr0, Int.le_floor.mpr (hn ▸ hrC)⟩, hn.symm⟩
  have hS_sub : S ⊆ Set.univ.pi T := by
    intro α hα b _
    have hαΦ := hα.1
    have hbd := hC α hα
    exact ⟨hyp.roots_integer_coords α hαΦ b, (hbd b).2, (hbd b).1⟩
  exact (Set.Finite.pi hT_finite).subset hS_sub

/-- Packaging: from `AffineCoxeterHyp` we obtain the two finiteness axioms needed by the rest of
the development (subspan finiteness and hyperplane finiteness of nonposRoots). -/
def finiteProperParabolicsHyp_of_affineCoxeterHyp
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M) :
    FiniteProperParabolicsHyp M where
  finiteRoots_in_subspan_of_subset_finite :=
    finiteRoots_in_subspan_of_AffineCoxeterHyp M hyp
  hyperplane_nonposRoots_finite := by
    intro v₀ hv₀_pos hv₀_radical x hx_hyp
    exact hyperplane_nonposRoots_finite_axiom M hyp v₀ hv₀_pos hv₀_radical x hx_hyp

end TitsCone
