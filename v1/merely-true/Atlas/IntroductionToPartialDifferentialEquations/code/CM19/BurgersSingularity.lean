/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers

set_option maxHeartbeats 1600000

open Finset MeasureTheory Set

noncomputable section

namespace TransportBurgers

/-- Predicate that a pair of curves $g_0, g_1 : \mathbb{R} \to \mathbb{R}$
forms a Burger's characteristic: $g_0'(s) = 1$ and $g_1'(s) = u(g_0(s), g_1(s))$. -/
def IsBurgersCharacteristic (u : ℝ → ℝ → ℝ) (g0 g1 : ℝ → ℝ) : Prop :=
  (∀ s, deriv g0 s = 1) ∧ (∀ s, deriv g1 s = u (g0 s) (g1 s))

/-- Bundled (paired) version of a Burger's characteristic curve
$\gamma : \mathbb{R} \to \mathbb{R} \times \mathbb{R}$: the time component
has derivative $1$ and the space component has derivative $u(\gamma_t, \gamma_x)$. -/
structure IsCharacteristicCurve (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : Prop where
  time_param : ∀ s, HasDerivAt (fun s => (γ s).1) 1 s
  spatial_eq : ∀ s, HasDerivAt (fun s => (γ s).2) (u (γ s).1 (γ s).2) s

/-- If $g_0' \equiv 1$ then $g_0$ has zero acceleration: $g_0''(s) = 0$ for
all $s$. (Time-component analogue of straight-line characteristics.) -/
theorem burgers_char_zero_accel_time
    (g0 : ℝ → ℝ)
    (hg0 : ∀ s, deriv g0 s = 1) :
    ∀ s, (deriv (deriv g0) s : ℝ) = 0 := by
  intro s
  have : deriv g0 = fun _ => (1 : ℝ) := funext hg0
  rw [this]
  exact deriv_const s 1

/-- Spatial-component analogue: if $u$ is constant along the characteristic
$(g_0, g_1)$ then $g_1$ has zero acceleration, $g_1''(s) = 0$ for all $s$. -/
theorem burgers_char_zero_accel_space
    (u : ℝ → ℝ → ℝ) (g0 g1 : ℝ → ℝ)
    (hchar : IsBurgersCharacteristic u g0 g1)
    (hconst : ∀ s, deriv (fun s => u (g0 s) (g1 s)) s = 0)
    (hg1_diff : Differentiable ℝ g1) :
    ∀ s, (deriv (deriv g1) s : ℝ) = 0 := by
  intro s
  have hderiv_eq : deriv g1 = fun s => u (g0 s) (g1 s) := by
    ext s'
    have h1 : HasDerivAt g1 (u (g0 s') (g1 s')) s' := by
      rw [← hchar.2 s']
      exact (hg1_diff s').hasDerivAt
    exact h1.deriv
  rw [hderiv_eq]
  exact hconst s

/-- Uniqueness for the linear ODE $w'(s) = -w(s) \cdot h(s)$ with $w(0) = 0$
on the right half-line: any differentiable solution with continuous coefficient
$h$ must vanish identically on $[0, \infty)$. Proved via Grönwall. -/
lemma ode_unique_zero_pos (w h : ℝ → ℝ)
    (hw_diff : Differentiable ℝ w) (hw0 : w 0 = 0) (hh_cont : Continuous h)
    (hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h s₀) s₀)
    (s : ℝ) (hs : 0 ≤ s) : w s = 0 := by
  have hh_bdd : ∃ K : ℝ, ∀ t ∈ Icc 0 s, ‖h t‖ ≤ K := by
    have := (isCompact_Icc (a := 0) (b := s)).bddAbove_image hh_cont.norm.continuousOn
    obtain ⟨K, hK⟩ := this; exact ⟨K, fun t ht => hK ⟨t, ht, rfl⟩⟩
  obtain ⟨K, hK⟩ := hh_bdd
  have hws : ‖w s‖ ≤ gronwallBound 0 K 0 (s - 0) := by
    apply norm_le_gronwallBound_of_norm_deriv_right_le
        (hw_diff.continuous.continuousOn (s := Icc 0 s))
    · intro x _; exact (hw_eq x).hasDerivWithinAt
    · simp [hw0]
    · intro x hx
      calc ‖-w x * h x‖ = ‖w x‖ * ‖h x‖ := by
            rw [show -w x * h x = -(w x * h x) from by ring, norm_neg, norm_mul]
        _ ≤ ‖w x‖ * K :=
            mul_le_mul_of_nonneg_left (hK x (Ico_subset_Icc_self hx)) (norm_nonneg _)
        _ = K * ‖w x‖ + 0 := by ring
    · exact ⟨hs, le_refl s⟩
  simp [gronwallBound] at hws; exact hws

/-- Two-sided uniqueness: any differentiable solution of $w'(s) = -w(s) h(s)$
with $w(0) = 0$ and continuous $h$ vanishes on all of $\mathbb{R}$. -/
lemma ode_unique_zero (w h : ℝ → ℝ)
    (hw_diff : Differentiable ℝ w) (hw0 : w 0 = 0) (hh_cont : Continuous h)
    (hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h s₀) s₀)
    (s : ℝ) : w s = 0 := by
  by_cases hs : 0 ≤ s
  · exact ode_unique_zero_pos w h hw_diff hw0 hh_cont hw_eq s hs
  · push Not at hs
    have key : w (-(-s)) = 0 :=
      ode_unique_zero_pos (fun t => w (-t)) (fun t => -h (-t))
        (hw_diff.comp differentiable_neg) (by simp [hw0])
        ((hh_cont.comp continuous_neg).neg)
        (fun t => by
          have h1 := (hw_eq (-t)).comp t (hasDerivAt_neg t)
          simp at h1; convert h1 using 1; ring)
        (-s) (by linarith)
    simpa using key

/-- **Proposition 2.0.2 (Burger solutions are constant along characteristics).**
Let $u$ be a $C^1$ solution of Burger's equation with initial data $u(0, \cdot) = f$.
Then along the straight characteristic emanating from $(0, p)$, the solution is
constant: $u(s, p + f(p) \cdot s) = f(p)$ for all $s \in \mathbb{R}$. -/
theorem burgers_constant_along_straight_char
    (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : SolvesBurgers u)
    (hu_C1 : ContDiff ℝ 1 (Function.uncurry u))
    (hdata : ∀ x, u 0 x = f x)
    (p s : ℝ) :
    u s (p + f p * s) = f p := by
  set c := f p
  set U := Function.uncurry u
  set w : ℝ → ℝ := fun s₀ => u s₀ (p + c * s₀) - c
  set h_func : ℝ → ℝ := fun s₀ => deriv (fun x' => u s₀ x') (p + c * s₀)
  have hU_diff : Differentiable ℝ U := hu_C1.differentiable one_ne_zero

  have hw_diff : Differentiable ℝ w := by
    apply Differentiable.sub _ (differentiable_const c)
    intro s₀
    exact hU_diff.differentiableAt.comp s₀
      (differentiableAt_id.prodMk
        ((differentiableAt_const p).add ((differentiableAt_const c).mul differentiableAt_id)))

  have hw0 : w 0 = 0 := by simp [w, hdata p, c]

  have hh_cont : Continuous h_func := by
    have hfderiv_cont : Continuous (fderiv ℝ U) := hu_C1.continuous_fderiv one_ne_zero
    have hline_cont : Continuous (fun s₀ => (s₀, p + c * s₀)) :=
      continuous_id.prodMk (continuous_const.add (continuous_const.mul continuous_id))
    have hcomp_cont : Continuous (fun s₀ => fderiv ℝ U (s₀, p + c * s₀)) :=
      hfderiv_cont.comp hline_cont
    have heval : Continuous (fun (L : ℝ × ℝ →L[ℝ] ℝ) => L (0, 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous
    suffices heq : h_func = fun s₀ => fderiv ℝ U (s₀, p + c * s₀) (0, 1) from
      heq ▸ heval.comp hcomp_cont
    ext s₀
    simp only [h_func]
    symm
    have hcomp : HasFDerivAt (fun x' => U (s₀, x'))
        ((fderiv ℝ U (s₀, p + c * s₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) (p + c * s₀) :=
      HasFDerivAt.comp (p + c * s₀) (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
        (hasFDerivAt_prodMk_right s₀ (p + c * s₀) :
          HasFDerivAt (fun x' => (s₀, x')) (ContinuousLinearMap.inr ℝ ℝ ℝ) (p + c * s₀))
    have hd := hcomp.hasDerivAt
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hd
    exact hd.deriv.symm

  have hw_eq : ∀ s₀, HasDerivAt w (-w s₀ * h_func s₀) s₀ := by
    intro s₀
    have hφ : HasDerivAt (fun s => (s, p + c * s)) ((1 : ℝ), c) s₀ :=
      (hasDerivAt_id s₀).prodMk (by simpa using (hasDerivAt_id s₀).const_mul c |>.const_add p)
    have hchain := (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt.comp_hasDerivAt s₀ hφ
    have hval : fderiv ℝ U (s₀, p + c * s₀) ((1:ℝ), c) =
        deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀ := by
      have h_t : fderiv ℝ U (s₀, p + c * s₀) (1, 0) = deriv (fun t' => u t' (p + c * s₀)) s₀ := by
        have hc := HasFDerivAt.comp s₀ (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
          (hasFDerivAt_prodMk_left s₀ (p + c * s₀) :
            HasFDerivAt (fun t' => (t', p + c * s₀)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s₀)
        exact hc.hasDerivAt.deriv.symm
      have h_x : fderiv ℝ U (s₀, p + c * s₀) (0, 1) = h_func s₀ := by
        have hc := HasFDerivAt.comp (p + c * s₀) (hU_diff.differentiableAt (x := (s₀, p + c * s₀))).hasFDerivAt
          (hasFDerivAt_prodMk_right s₀ (p + c * s₀) :
            HasFDerivAt (fun x' => (s₀, x')) (ContinuousLinearMap.inr ℝ ℝ ℝ) (p + c * s₀))
        exact hc.hasDerivAt.deriv.symm
      have hd : ((1:ℝ), (c:ℝ)) = (1:ℝ) • ((1:ℝ), (0:ℝ)) + c • ((0:ℝ), (1:ℝ)) := by simp
      rw [hd, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h_t, h_x, one_mul]
    have hg_hasderiv : HasDerivAt (fun s => u s (p + c * s))
        (deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀) s₀ := by
      convert hchain using 1; exact hval.symm
    have hw_hasderiv := hg_hasderiv.sub_const c
    have hburg := hu s₀ (p + c * s₀)
    have heq_val : deriv (fun t' => u t' (p + c * s₀)) s₀ + c * h_func s₀ = -w s₀ * h_func s₀ := by
      have : deriv (fun t' => u t' (p + c * s₀)) s₀ =
          -(u s₀ (p + c * s₀) * h_func s₀) := by linarith
      rw [this]; simp [w, h_func]; ring
    rwa [heq_val] at hw_hasderiv

  have hresult := ode_unique_zero w h_func hw_diff hw0 hh_cont hw_eq s
  simp [w] at hresult
  linarith

/-- **Theorem 3.1 ("Solving" Burger's equation).** Reformulation of
`burgers_constant_along_straight_char`: if $(t, x)$ lies on the characteristic
through $(0, p)$, i.e. $x = p + f(p) \cdot t$, then $u(t, x) = f(p)$. -/
theorem burgers_implicit_solution
    (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : SolvesBurgers u)
    (hu_C1 : ContDiff ℝ 1 (Function.uncurry u))
    (hdata : ∀ x, u 0 x = f x)
    (t x p : ℝ) (hp : x = p + f p * t) :
    u t x = f p := by
  rw [hp]
  exact burgers_constant_along_straight_char u f hu hu_C1 hdata p t

/-- If $f$ is differentiable and $f'(x_0) < 0$, then there exists some
$x_1 > x_0$ with $f(x_1) < f(x_0)$. (A strict decrease just to the right of
$x_0$.) -/
theorem exists_gt_of_deriv_neg
    (f : ℝ → ℝ)
    (hf_diff : Differentiable ℝ f)
    (x₀ : ℝ) (hf'_neg : deriv f x₀ < 0) :
    ∃ x₁ > x₀, f x₁ < f x₀ := by

  have hda := (hf_diff x₀).hasDerivAt
  have hslope := hda.tendsto_slope_zero_right

  have hev : ∀ᶠ h in nhdsWithin (0:ℝ) (Ioi 0), h⁻¹ • (f (x₀ + h) - f x₀) < 0 :=
    hslope.eventually (gt_mem_nhds (by linarith : (0:ℝ) > deriv f x₀))

  have hev_pos : ∀ᶠ h in nhdsWithin (0:ℝ) (Ioi 0), (0:ℝ) < h :=
    eventually_nhdsWithin_of_forall (fun x hx => hx)

  obtain ⟨h, hh_slope, hh_pos⟩ := (hev.and hev_pos).exists
  refine ⟨x₀ + h, by linarith, ?_⟩

  have hinv_pos : (0:ℝ) < h⁻¹ := inv_pos.mpr hh_pos
  have : f (x₀ + h) - f x₀ < 0 := by
    by_contra h_ge
    push Not at h_ge
    have : (0:ℝ) ≤ h⁻¹ • (f (x₀ + h) - f x₀) :=
      smul_nonneg (le_of_lt hinv_pos) h_ge
    linarith
  linarith

/-- If $f'(x_0) < 0$ for some $x_0$, then two characteristics for Burger's
equation collide at some positive time: there exist distinct $p_0, p_1$ and
$t > 0$ with $p_0 + f(p_0) t = p_1 + f(p_1) t$. -/
theorem singularity_forward_chars_cross
    (f : ℝ → ℝ)
    (hf_diff : Differentiable ℝ f)
    (x₀ : ℝ) (hf'_neg : deriv f x₀ < 0) :
    ∃ (p₀ p₁ : ℝ) (t : ℝ), p₀ ≠ p₁ ∧ 0 < t ∧
      p₀ + f p₀ * t = p₁ + f p₁ * t := by
  obtain ⟨x₁, hx₁_gt, hf_lt⟩ := exists_gt_of_deriv_neg f hf_diff x₀ hf'_neg

  refine ⟨x₀, x₁, (x₁ - x₀) / (f x₀ - f x₁), ne_of_lt hx₁_gt, ?_, ?_⟩
  ·
    exact div_pos (by linarith) (by linarith)
  ·
    have hne : f x₀ - f x₁ ≠ 0 := by linarith
    field_simp
    ring

/-- The forward-time contradiction underlying the singularity theorem: if the
initial data has $f'(x_0) < 0$, then there is a point $(t, x)$ with $t > 0$ where
the constant-along-characteristics property forces $u(t, x) = f(p_0) = f(p_1)$
for distinct $p_0, p_1$ with $f(p_0) \ne f(p_1)$, a contradiction. -/
theorem singularity_forward_contradiction
    (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hdata : ∀ x, u 0 x = f x)
    (hconst_char : ∀ p s, u s (p + f p * s) = u 0 p)
    (hf_diff : Differentiable ℝ f)
    (x₀ : ℝ) (hf'_neg : deriv f x₀ < 0) :
    ∃ (p₀ p₁ : ℝ) (t : ℝ) (x : ℝ),
      p₀ ≠ p₁ ∧ 0 < t ∧ f p₀ ≠ f p₁ ∧
      u t x = f p₀ ∧ u t x = f p₁ := by
  obtain ⟨p₀, p₁, t, hp_ne, ht_pos, hcross⟩ :=
    singularity_forward_chars_cross f hf_diff x₀ hf'_neg
  refine ⟨p₀, p₁, t, p₀ + f p₀ * t, hp_ne, ht_pos, ?_, ?_, ?_⟩
  ·
    intro heq
    apply hp_ne
    have : p₀ + f p₀ * t = p₁ + f p₁ * t := hcross
    rw [heq] at this
    linarith
  · rw [hconst_char p₀ t, hdata p₀]
  · rw [hcross, hconst_char p₁ t, hdata p₁]


/-- The characteristic inverse $p_0(t, x)$ satisfies the linear transport
equation $\partial_t p_0 + f(p_0) \partial_x p_0 = 0$. Derived by implicit
differentiation of the relation $x = p_0(t, x) + f(p_0(t, x)) t$. -/
theorem transport_equation_from_ift
    (f : ℝ → ℝ)
    (hf_C1 : ContDiff ℝ 1 f)
    (hf'_nonneg : ∀ x, 0 ≤ deriv f x)
    (p₀ : ℝ → ℝ → ℝ)
    (hp₀_rel : ∀ t x, x = p₀ t x + f (p₀ t x) * t)
    (hp₀_C1 : ContDiff ℝ 1 (Function.uncurry p₀)) :
    ∀ t x, deriv (fun t' => p₀ t' x) t +
        f (p₀ t x) * deriv (fun x' => p₀ t x') x = 0 := by
  intro t x
  set P := Function.uncurry p₀
  have hP_diff : Differentiable ℝ P := hp₀_C1.differentiable (by norm_num)
  have hf_diff : Differentiable ℝ f := hf_C1.differentiable (by norm_num)

  have hp₀_t_diff : Differentiable ℝ (fun t' => p₀ t' x) := by
    intro t'
    have : (fun t' => p₀ t' x) = P ∘ (fun t' => (t', x)) := by ext; simp [P, Function.uncurry]
    rw [this]
    exact hP_diff.differentiableAt.comp t' (differentiableAt_id.prodMk (differentiableAt_const _))
  have hp₀_x_diff : Differentiable ℝ (fun x' => p₀ t x') := by
    intro x'
    have : (fun x' => p₀ t x') = P ∘ (fun x' => (t, x')) := by ext; simp [P, Function.uncurry]
    rw [this]
    exact hP_diff.differentiableAt.comp x' ((differentiableAt_const _).prodMk differentiableAt_id)
  have hfp₀_t_diff : Differentiable ℝ (fun t' => f (p₀ t' x)) := hf_diff.comp hp₀_t_diff
  have hfp₀_x_diff : Differentiable ℝ (fun x' => f (p₀ t x')) := hf_diff.comp hp₀_x_diff


  have h_Phi_t : deriv (fun t' => p₀ t' x + f (p₀ t' x) * t') t = 0 := by
    have : (fun t' => p₀ t' x + f (p₀ t' x) * t') = fun _ => x := by
      ext t'; linarith [hp₀_rel t' x]
    rw [this, deriv_const]

  have h_Phi_x : deriv (fun x' => p₀ t x' + f (p₀ t x') * t) x = 1 := by
    have : (fun x' => p₀ t x' + f (p₀ t x') * t) = id := by
      ext x'; simp [id]; linarith [hp₀_rel t x']
    rw [this, deriv_id']

  have h_expand_t : deriv (fun t' => p₀ t' x + f (p₀ t' x) * t') t =
      deriv (fun t' => p₀ t' x) t +
      (deriv (fun t' => f (p₀ t' x)) t * t + f (p₀ t x)) := by
    have h1 : HasDerivAt (fun t' => p₀ t' x) (deriv (fun t' => p₀ t' x) t) t :=
      (hp₀_t_diff t).hasDerivAt
    have h2 : HasDerivAt (fun t' => f (p₀ t' x)) (deriv (fun t' => f (p₀ t' x)) t) t :=
      (hfp₀_t_diff t).hasDerivAt
    have h3 : HasDerivAt (fun t' => f (p₀ t' x) * t')
        (deriv (fun t' => f (p₀ t' x)) t * t + f (p₀ t x) * 1) t :=
      h2.mul (hasDerivAt_id t)
    simp only [mul_one] at h3
    exact (h1.add h3).deriv

  have h_chain_t : deriv (fun t' => f (p₀ t' x)) t =
      deriv f (p₀ t x) * deriv (fun t' => p₀ t' x) t :=
    ((hf_diff (p₀ t x)).hasDerivAt.comp t (hp₀_t_diff t).hasDerivAt).deriv

  have h_expand_x : deriv (fun x' => p₀ t x' + f (p₀ t x') * t) x =
      deriv (fun x' => p₀ t x') x + deriv (fun x' => f (p₀ t x')) x * t :=
    ((hp₀_x_diff x).hasDerivAt.add ((hfp₀_x_diff x).hasDerivAt.mul_const t)).deriv

  have h_chain_x : deriv (fun x' => f (p₀ t x')) x =
      deriv f (p₀ t x) * deriv (fun x' => p₀ t x') x :=
    ((hf_diff (p₀ t x)).hasDerivAt.comp x (hp₀_x_diff x).hasDerivAt).deriv


  set A := deriv (fun t' => p₀ t' x) t
  set B := deriv (fun x' => p₀ t x') x
  set c := f (p₀ t x)
  set d := deriv f (p₀ t x)

  have eq1 : A + d * A * t + c = 0 := by
    have := h_Phi_t; rw [h_expand_t, h_chain_t] at this; linarith

  have eq2 : B + d * B * t = 1 := by
    have := h_Phi_x; rw [h_expand_x, h_chain_x] at this; linarith

  have h_nonzero : 1 + d * t ≠ 0 := by
    intro h
    have hB : B * (1 + d * t) = 1 := by linarith [eq2]
    rw [h, mul_zero] at hB; exact zero_ne_one hB

  have h_factor : (A + c * B) * (1 + d * t) = 0 := by
    have : (A + c * B) * (1 + d * t) = A + d * A * t + c * (B + d * B * t) := by ring
    rw [this, eq2]; linarith

  exact (mul_eq_zero.mp h_factor).resolve_right h_nonzero



open scoped Classical


end TransportBurgers
