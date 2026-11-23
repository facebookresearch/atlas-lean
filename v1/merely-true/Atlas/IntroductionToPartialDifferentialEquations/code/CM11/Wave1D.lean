/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Real Set MeasureTheory intervalIntegral

noncomputable section

namespace WaveEquation1D

/-- D'Alembert's formula for the $1+1$ dimensional wave equation:
$u(t,x) = \frac{1}{2}(f(x+t) + f(x-t)) + \frac{1}{2}\int_{x-t}^{x+t} g(z)\,dz$. -/
def dAlembertSolution (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (f (x + t) + f (x - t)) / 2 + (∫ y in (x - t)..(x + t), g y) / 2


/-- If $g_0 \in C^1(\mathbb{R})$, then its antiderivative $z \mapsto \int_0^z g_0(y)\,dy$
is in $C^2(\mathbb{R})$. -/
lemma contDiff_antideriv (g₀ : ℝ → ℝ) (hg₀ : ContDiff ℝ 1 g₀) :
    ContDiff ℝ 2 (fun z => ∫ y in (0 : ℝ)..z, g₀ y) := by
  have hg_cont : Continuous g₀ := hg₀.continuous
  have key : ContDiff ℝ (1 + 1) (fun z => ∫ y in (0 : ℝ)..z, g₀ y) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (hg_cont.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
    · intro h; simp at h
    · have hderiv : deriv (fun z => ∫ y in (0 : ℝ)..z, g₀ y) = g₀ := by
        ext z; exact (hg_cont.integral_hasStrictDerivAt 0 z).hasDerivAt.deriv
      rw [hderiv]; exact hg₀
  exact_mod_cast key


/-- Chain rule helper: if $h$ is differentiable at $a + b$, then the map $s \mapsto h(a + s)$
has derivative $h'(a + b)$ at $b$. -/
lemma hasDerivAt_comp_add_right' {h : ℝ → ℝ} {a b : ℝ}
    (hd : DifferentiableAt ℝ h (a + b)) :
    HasDerivAt (fun s => h (a + s)) (deriv h (a + b)) b := by
  have h1 : HasDerivAt (fun s => a + s) 1 b := by
    simpa using (hasDerivAt_id b).const_add a
  exact (hd.hasDerivAt.comp b h1).congr_deriv (by ring)

/-- Chain rule helper: if $h$ is differentiable at $a - b$, then the map $s \mapsto h(a - s)$
has derivative $-h'(a - b)$ at $b$. -/
lemma hasDerivAt_comp_sub_right' {h : ℝ → ℝ} {a b : ℝ}
    (hd : DifferentiableAt ℝ h (a - b)) :
    HasDerivAt (fun s => h (a - s)) (-deriv h (a - b)) b := by
  have h1 : HasDerivAt (fun s => a - s) (-1) b := by
    have := (hasDerivAt_id b).const_sub a
    simp at this; exact this
  have h2 := hd.hasDerivAt.comp b h1
  convert h2 using 1; ring

/-- Chain rule helper: if $h$ is differentiable at $b + a$, then $s \mapsto h(s + a)$
has derivative $h'(b + a)$ at $b$. -/
lemma hasDerivAt_comp_add_left' {h : ℝ → ℝ} {a b : ℝ}
    (hd : DifferentiableAt ℝ h (b + a)) :
    HasDerivAt (fun s => h (s + a)) (deriv h (b + a)) b := by
  have h1 : HasDerivAt (fun s => s + a) 1 b := by
    simpa using (hasDerivAt_id b).add_const a
  exact (hd.hasDerivAt.comp b h1).congr_deriv (by ring)

/-- Chain rule helper: if $h$ is differentiable at $b - a$, then $s \mapsto h(s - a)$
has derivative $h'(b - a)$ at $b$. -/
lemma hasDerivAt_comp_sub_left' {h : ℝ → ℝ} {a b : ℝ}
    (hd : DifferentiableAt ℝ h (b - a)) :
    HasDerivAt (fun s => h (s - a)) (deriv h (b - a)) b := by
  have h1 : HasDerivAt (fun s => s - a) 1 b := by
    simpa using (hasDerivAt_id b).sub_const a
  exact (hd.hasDerivAt.comp b h1).congr_deriv (by ring)

/-- Regularity for d'Alembert's solution: if $f \in C^2(\mathbb{R})$ and $g \in C^1(\mathbb{R})$,
then $(t, x) \mapsto u(t, x)$ defined by d'Alembert's formula is in $C^2(\mathbb{R}^2)$. -/
theorem dAlembert_regularity_proof (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => dAlembertSolution f g p.1 p.2) := by

  set G := fun z => ∫ y in (0 : ℝ)..z, g y
  have hG : ContDiff ℝ 2 G := contDiff_antideriv g hg
  have hg_cont : Continuous g := hg.continuous
  have hG_deriv : ∀ z, HasDerivAt G (g z) z := by
    intro z; exact (hg_cont.integral_hasStrictDerivAt 0 z).hasDerivAt

  set Fp : ℝ → ℝ := fun z => f z / 2 + G z / 2
  set Fm : ℝ → ℝ := fun z => f z / 2 - G z / 2
  have hFp : ContDiff ℝ 2 Fp := (hf.div_const 2).add (hG.div_const 2)
  have hFm : ContDiff ℝ 2 Fm := (hf.div_const 2).sub (hG.div_const 2)

  have integral_eq : ∀ a b : ℝ, ∫ z in a..b, g z = G b - G a := by
    intro a b
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => hG_deriv z) (hg_cont.intervalIntegrable _ _)

  have h_eq : (fun p : ℝ × ℝ => dAlembertSolution f g p.1 p.2) =
      fun p : ℝ × ℝ => Fp (p.2 + p.1) + Fm (p.2 - p.1) := by
    ext ⟨t, x⟩
    simp only [dAlembertSolution, Fp, Fm, integral_eq]
    ring
  rw [h_eq]
  exact (hFp.comp (contDiff_snd.add contDiff_fst)).add
    (hFm.comp (contDiff_snd.sub contDiff_fst))

/-- D'Alembert's solution is jointly $C^2$ in $(t, x)$ when $f \in C^2(\mathbb{R})$
and $g \in C^1(\mathbb{R})$. -/
theorem dAlembert_regularity (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => dAlembertSolution f g p.1 p.2) :=
  dAlembert_regularity_proof f g hf hg

/-- Any function of the form $u(t, x) = F(x + t) + G(x - t)$ with $F, G \in C^2(\mathbb{R})$
satisfies the wave equation $\partial_t^2 u = \partial_x^2 u$. -/
lemma general_solution_satisfies_wave_eq (F G : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (t x : ℝ) :
    deriv (fun t' => deriv (fun t'' => F (x + t'') + G (x - t'')) t') t =
    deriv (fun x' => deriv (fun x'' => F (x'' + t) + G (x'' - t)) x') x := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hFd' : Differentiable ℝ (deriv F) := hF.differentiable_deriv_two
  have hGd' : Differentiable ℝ (deriv G) := hG.differentiable_deriv_two
  have hdt : ∀ t', HasDerivAt (fun t'' => F (x + t'') + G (x - t''))
      (deriv F (x + t') - deriv G (x - t')) t' := by
    intro t'
    convert (hasDerivAt_comp_add_right' (hFd.differentiableAt (x := x + t'))).add
      (hasDerivAt_comp_sub_right' (hGd.differentiableAt (x := x - t'))) using 1
  have hdt_eq : (fun t' => deriv (fun t'' => F (x + t'') + G (x - t'')) t') =
      fun t' => deriv F (x + t') - deriv G (x - t') := by
    ext t'; exact (hdt t').deriv
  have hdtt : HasDerivAt (fun t' => deriv F (x + t') - deriv G (x - t'))
      (deriv (deriv F) (x + t) + deriv (deriv G) (x - t)) t := by
    convert (hasDerivAt_comp_add_right' (hFd'.differentiableAt (x := x + t))).sub
      (hasDerivAt_comp_sub_right' (hGd'.differentiableAt (x := x - t))) using 1; ring
  have hdx : ∀ x', HasDerivAt (fun x'' => F (x'' + t) + G (x'' - t))
      (deriv F (x' + t) + deriv G (x' - t)) x' := by
    intro x'
    exact (hasDerivAt_comp_add_left' (hFd.differentiableAt (x := x' + t))).add
      (hasDerivAt_comp_sub_left' (hGd.differentiableAt (x := x' - t)))
  have hdx_eq : (fun x' => deriv (fun x'' => F (x'' + t) + G (x'' - t)) x') =
      fun x' => deriv F (x' + t) + deriv G (x' - t) := by
    ext x'; exact (hdx x').deriv
  have hdxx : HasDerivAt (fun x' => deriv F (x' + t) + deriv G (x' - t))
      (deriv (deriv F) (x + t) + deriv (deriv G) (x - t)) x :=
    (hasDerivAt_comp_add_left' (hFd'.differentiableAt (x := x + t))).add
     (hasDerivAt_comp_sub_left' (hGd'.differentiableAt (x := x - t)))
  rw [hdt_eq, hdtt.deriv, hdx_eq, hdxx.deriv]

set_option maxHeartbeats 2000000 in

/-- Uniqueness for the wave equation with zero initial data: if $w \in C^2(\mathbb{R}^2)$
satisfies $\partial_t^2 w = \partial_x^2 w$, $w(0, x) = 0$, and $\partial_t w(0, x) = 0$ for all
$x$, then $w \equiv 0$. -/
theorem zero_wave_is_zero (w : ℝ → ℝ → ℝ)
    (h_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => w p.1 p.2))
    (h_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => w t'' x) t') t =
                      deriv (fun x' => deriv (fun x'' => w t x'') x') x)
    (h_pos : ∀ x, w 0 x = 0)
    (h_vel : ∀ x, deriv (fun t => w t x) 0 = 0) :
    ∀ t x, w t x = 0 := by
  set W := fun p : ℝ × ℝ => w p.1 p.2
  have hdW : Differentiable ℝ W := h_reg.differentiable two_ne_zero
  have hdDW : Differentiable ℝ (fderiv ℝ W) :=
    (h_reg.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero

  have wave_fderiv : ∀ p : ℝ × ℝ, (fderiv ℝ (fderiv ℝ W) p (1, 0)) (1, 0) =
                                     (fderiv ℝ (fderiv ℝ W) p (0, 1)) (0, 1) := by
    intro ⟨t, x⟩
    have lhs : (fderiv ℝ (fderiv ℝ W) (t, x) (1, 0)) (1, 0) =
        deriv (fun t' => deriv (fun t'' => w t'' x) t') t := by
      set γ := fun s : ℝ => ((s : ℝ), (x : ℝ))
      have hγ' : ∀ s, HasDerivAt γ (1, 0) s :=
        fun s => (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
      have hd1 : ∀ s, HasDerivAt (W ∘ γ) (fderiv ℝ W (γ s) (1, 0)) s := fun s =>
        (hdW.differentiableAt (x := γ s)).hasFDerivAt.comp_hasDerivAt s (hγ' s)
      have hdW_γ :=
        (hdDW.differentiableAt (x := γ t)).hasFDerivAt.comp_hasDerivAt t (hγ' t)
      have heval :=
        (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt t hdW_γ
      have hfun : (fun t' => deriv (fun t'' => w t'' x) t') =
          (fun s => fderiv ℝ W (γ s) (1, 0)) :=
        funext fun s => (hd1 s).deriv
      rw [hfun]; exact heval.deriv.symm
    have rhs : (fderiv ℝ (fderiv ℝ W) (t, x) (0, 1)) (0, 1) =
        deriv (fun x' => deriv (fun x'' => w t x'') x') x := by
      set γ := fun s : ℝ => ((t : ℝ), s)
      have hγ' : ∀ s, HasDerivAt γ (0, 1) s :=
        fun s => (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
      have hd1 : ∀ s, HasDerivAt (W ∘ γ) (fderiv ℝ W (γ s) (0, 1)) s := fun s =>
        (hdW.differentiableAt (x := γ s)).hasFDerivAt.comp_hasDerivAt s (hγ' s)
      have hdW_γ :=
        (hdDW.differentiableAt (x := γ x)).hasFDerivAt.comp_hasDerivAt x (hγ' x)
      have heval :=
        (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt x hdW_γ
      have hfun : (fun x' => deriv (fun x'' => w t x'') x') =
          (fun s => fderiv ℝ W (γ s) (0, 1)) :=
        funext fun s => (hd1 s).deriv
      rw [hfun]; exact heval.deriv.symm
    rw [lhs, rhs]; exact h_wave t x

  have schwarz : ∀ p : ℝ × ℝ, (fderiv ℝ (fderiv ℝ W) p (1, 0)) (0, 1) =
      (fderiv ℝ (fderiv ℝ W) p (0, 1)) (1, 0) :=
    fun p => (ContDiffAt.isSymmSndFDerivAt (h_reg.contDiffAt (x := p)) (by simp)).eq (1, 0) (0, 1)
  have vanish_11 : ∀ p, (fderiv ℝ (fderiv ℝ W) p (1, -1)) (1, 1) = 0 := by
    intro p
    rw [show ((1:ℝ), (-1:ℝ)) = ((1:ℝ), (0:ℝ)) - ((0:ℝ), (1:ℝ)) from by ext <;> simp,
        show ((1:ℝ), (1:ℝ)) = ((1:ℝ), (0:ℝ)) + ((0:ℝ), (1:ℝ)) from by ext <;> simp]
    simp only [map_sub, map_add, ContinuousLinearMap.sub_apply]
    linarith [wave_fderiv p, schwarz p]
  have vanish_1m1 : ∀ p, (fderiv ℝ (fderiv ℝ W) p (1, 1)) (1, -1) = 0 := by
    intro p
    rw [show ((1:ℝ), (1:ℝ)) = ((1:ℝ), (0:ℝ)) + ((0:ℝ), (1:ℝ)) from by ext <;> simp,
        show ((1:ℝ), (-1:ℝ)) = ((1:ℝ), (0:ℝ)) - ((0:ℝ), (1:ℝ)) from by ext <;> simp]
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply]
    linarith [wave_fderiv p, schwarz p]

  have chain_fderiv : ∀ (p v u : ℝ × ℝ),
      fderiv ℝ (fun q => fderiv ℝ W q v) p u = (fderiv ℝ (fderiv ℝ W) p u) v := by
    intro p v u
    have hkey : fderiv ℝ (fun q => fderiv ℝ W q v) p =
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ W) p)) :=
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt (x := fderiv ℝ W p)).comp p
        hdDW.differentiableAt.hasFDerivAt |>.fderiv
    rw [hkey]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have vanish_11' : ∀ p, fderiv ℝ (fun q => fderiv ℝ W q (1, 1)) p (1, -1) = 0 := by
    intro p; rw [chain_fderiv]; exact vanish_11 p
  have vanish_1m1' : ∀ p, fderiv ℝ (fun q => fderiv ℝ W q (1, -1)) p (1, 1) = 0 := by
    intro p; rw [chain_fderiv]; exact vanish_1m1 p

  have init_zero : ∀ a, fderiv ℝ W (0, a) = 0 := by
    intro a
    have ht : fderiv ℝ W (0, a) (1, 0) = 0 := by
      rw [← ((hdW.differentiableAt (x := ((0:ℝ), a))).hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_id _).prodMk (hasDerivAt_const _ a))).deriv]
      exact h_vel a
    have hx : fderiv ℝ W (0, a) (0, 1) = 0 := by
      rw [← ((hdW.differentiableAt (x := ((0:ℝ), a))).hasFDerivAt.comp_hasDerivAt a
        ((hasDerivAt_const _ (0:ℝ)).prodMk (hasDerivAt_id _))).deriv]
      have : W ∘ Prod.mk (0 : ℝ) = fun _ => (0 : ℝ) := by ext x'; simp [W, h_pos]
      rw [this]; exact deriv_const a 0
    apply ContinuousLinearMap.ext; intro ⟨v₁, v₂⟩
    simp only [ContinuousLinearMap.zero_apply]
    rw [show (v₁, v₂) = v₁ • ((1:ℝ), (0:ℝ)) + v₂ • ((0:ℝ), (1:ℝ)) from by ext <;> simp,
        map_add, map_smul, map_smul, ht, hx, smul_zero, smul_zero, add_zero]

  have hR11 : Differentiable ℝ (fun q => fderiv ℝ W q (1, 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(1:ℝ))).differentiable.comp hdDW
  have hR1m1 : Differentiable ℝ (fun q => fderiv ℝ W q (1, -1)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(-1:ℝ))).differentiable.comp hdDW
  have prop_11 : ∀ t x, fderiv ℝ W (t, x) (1, 1) = 0 := by
    intro t x; set a := x + t; set γ := fun s : ℝ => (s, a - s)
    have hγ' : ∀ s, HasDerivAt γ (1, -1) s := fun s =>
      (hasDerivAt_id s).prodMk (by simpa using (hasDerivAt_const s a).sub (hasDerivAt_id s))
    have hRγ_zero : ∀ s, HasDerivAt (fun s => fderiv ℝ W (γ s) (1, 1)) 0 s := by
      intro s; convert hR11.differentiableAt.hasFDerivAt.comp_hasDerivAt s (hγ' s) using 1
      exact (vanish_11' (γ s)).symm
    have hRγ_diff : Differentiable ℝ (fun s => fderiv ℝ W (γ s) (1, 1)) :=
      hR11.comp (fun s => (hγ' s).differentiableAt)
    have := is_const_of_deriv_eq_zero hRγ_diff (fun s => (hRγ_zero s).deriv) t 0
    simp [γ, a, show x + t - t = x from by ring] at this
    rw [this]; simp [init_zero]
  have prop_1m1 : ∀ t x, fderiv ℝ W (t, x) (1, -1) = 0 := by
    intro t x; set b := x - t; set γ := fun s : ℝ => (s, b + s)
    have hγ' : ∀ s, HasDerivAt γ (1, 1) s := fun s =>
      (hasDerivAt_id s).prodMk (by simpa using (hasDerivAt_const s b).add (hasDerivAt_id s))
    have hRγ_zero : ∀ s, HasDerivAt (fun s => fderiv ℝ W (γ s) (1, -1)) 0 s := by
      intro s; convert hR1m1.differentiableAt.hasFDerivAt.comp_hasDerivAt s (hγ' s) using 1
      exact (vanish_1m1' (γ s)).symm
    have hRγ_diff : Differentiable ℝ (fun s => fderiv ℝ W (γ s) (1, -1)) :=
      hR1m1.comp (fun s => (hγ' s).differentiableAt)
    have := is_const_of_deriv_eq_zero hRγ_diff (fun s => (hRγ_zero s).deriv) t 0
    simp [γ, b, show x - t + t = x from by ring] at this
    rw [this]; simp [init_zero]

  have fderiv_zero : ∀ p, fderiv ℝ W p = 0 := by
    intro ⟨t, x⟩; apply ContinuousLinearMap.ext; intro ⟨v₁, v₂⟩
    simp only [ContinuousLinearMap.zero_apply]
    rw [show (v₁, v₂) = ((v₁ + v₂) / 2) • ((1:ℝ), (1:ℝ)) +
        ((v₁ - v₂) / 2) • ((1:ℝ), (-1:ℝ)) from by ext <;> simp <;> ring,
        map_add, map_smul, map_smul, prop_11 t x, prop_1m1 t x,
        smul_zero, smul_zero, add_zero]

  intro t x
  have := is_const_of_fderiv_eq_zero hdW fderiv_zero (t, x) (0, 0)
  simp [W, h_pos] at this; exact this

/-- The difference of two solutions to the wave equation is itself a solution: if $u_1, u_2$
both satisfy $\partial_t^2 u = \partial_x^2 u$, then so does $u_1 - u_2$. -/
theorem wave_eq_of_sub (u₁ u₂ : ℝ → ℝ → ℝ)
    (h₁_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₁ p.1 p.2))
    (h₂_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₂ p.1 p.2))
    (h₁_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₁ t'' x) t') t =
                       deriv (fun x' => deriv (fun x'' => u₁ t x'') x') x)
    (h₂_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₂ t'' x) t') t =
                       deriv (fun x' => deriv (fun x'' => u₂ t x'') x') x) :
    ∀ t x, deriv (fun t' => deriv (fun t'' => (u₁ t'' x - u₂ t'' x)) t') t =
            deriv (fun x' => deriv (fun x'' => (u₁ t x'' - u₂ t x'')) x') x := by
  intro t x

  have hc₁t : ∀ x, ContDiff ℝ 2 (fun t => u₁ t x) :=
    fun x => h₁_reg.comp (contDiff_prodMk_left x)
  have hc₂t : ∀ x, ContDiff ℝ 2 (fun t => u₂ t x) :=
    fun x => h₂_reg.comp (contDiff_prodMk_left x)
  have hc₁x : ∀ t, ContDiff ℝ 2 (fun x => u₁ t x) :=
    fun t => h₁_reg.comp (contDiff_prodMk_right t)
  have hc₂x : ∀ t, ContDiff ℝ 2 (fun x => u₂ t x) :=
    fun t => h₂_reg.comp (contDiff_prodMk_right t)

  have hd₁t : ∀ x, Differentiable ℝ (fun t => u₁ t x) :=
    fun x => (hc₁t x).differentiable two_ne_zero
  have hd₂t : ∀ x, Differentiable ℝ (fun t => u₂ t x) :=
    fun x => (hc₂t x).differentiable two_ne_zero
  have hd₁x : ∀ t, Differentiable ℝ (fun x => u₁ t x) :=
    fun t => (hc₁x t).differentiable two_ne_zero
  have hd₂x : ∀ t, Differentiable ℝ (fun x => u₂ t x) :=
    fun t => (hc₂x t).differentiable two_ne_zero

  have hdd₁t : ∀ x, Differentiable ℝ (fun t => deriv (fun t' => u₁ t' x) t) := by
    intro x
    have := (hc₁t x).differentiable_iteratedDeriv 1 (by norm_cast)
    rwa [iteratedDeriv_one] at this
  have hdd₂t : ∀ x, Differentiable ℝ (fun t => deriv (fun t' => u₂ t' x) t) := by
    intro x
    have := (hc₂t x).differentiable_iteratedDeriv 1 (by norm_cast)
    rwa [iteratedDeriv_one] at this
  have hdd₁x : ∀ t, Differentiable ℝ (fun x => deriv (fun x' => u₁ t x') x) := by
    intro t
    have := (hc₁x t).differentiable_iteratedDeriv 1 (by norm_cast)
    rwa [iteratedDeriv_one] at this
  have hdd₂x : ∀ t, Differentiable ℝ (fun x => deriv (fun x' => u₂ t x') x) := by
    intro t
    have := (hc₂x t).differentiable_iteratedDeriv 1 (by norm_cast)
    rwa [iteratedDeriv_one] at this

  have inner_t : ∀ t', deriv (fun t'' => u₁ t'' x - u₂ t'' x) t' =
      deriv (fun t'' => u₁ t'' x) t' - deriv (fun t'' => u₂ t'' x) t' := by
    intro t'
    exact deriv_sub (hd₁t x).differentiableAt (hd₂t x).differentiableAt

  have lhs_eq : deriv (fun t' => deriv (fun t'' => u₁ t'' x - u₂ t'' x) t') t =
      deriv (fun t' => deriv (fun t'' => u₁ t'' x) t' - deriv (fun t'' => u₂ t'' x) t') t := by
    congr 1; ext t'; exact inner_t t'
  rw [lhs_eq]

  have outer_t : deriv (fun t' => deriv (fun t'' => u₁ t'' x) t' -
      deriv (fun t'' => u₂ t'' x) t') t =
      deriv (fun t' => deriv (fun t'' => u₁ t'' x) t') t -
      deriv (fun t' => deriv (fun t'' => u₂ t'' x) t') t :=
    deriv_sub (hdd₁t x).differentiableAt (hdd₂t x).differentiableAt
  rw [outer_t]

  have inner_x : ∀ x', deriv (fun x'' => u₁ t x'' - u₂ t x'') x' =
      deriv (fun x'' => u₁ t x'') x' - deriv (fun x'' => u₂ t x'') x' := by
    intro x'
    exact deriv_sub (hd₁x t).differentiableAt (hd₂x t).differentiableAt
  have rhs_eq : deriv (fun x' => deriv (fun x'' => u₁ t x'' - u₂ t x'') x') x =
      deriv (fun x' => deriv (fun x'' => u₁ t x'') x' -
      deriv (fun x'' => u₂ t x'') x') x := by
    congr 1; ext x'; exact inner_x x'
  rw [rhs_eq]
  have outer_x : deriv (fun x' => deriv (fun x'' => u₁ t x'') x' -
      deriv (fun x'' => u₂ t x'') x') x =
      deriv (fun x' => deriv (fun x'' => u₁ t x'') x') x -
      deriv (fun x' => deriv (fun x'' => u₂ t x'') x') x :=
    deriv_sub (hdd₁x t).differentiableAt (hdd₂x t).differentiableAt
  rw [outer_x]

  rw [h₁_wave t x, h₂_wave t x]

/-- If two $C^2$ functions $u_1, u_2$ have equal initial $t$-derivatives at $t = 0$, then
the $t$-derivative of their difference vanishes at $t = 0$. -/
lemma deriv_sub_zero (u₁ u₂ : ℝ → ℝ → ℝ)
    (h₁_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₁ p.1 p.2))
    (h₂_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₂ p.1 p.2))
    (h_vel : ∀ x, deriv (fun t => u₁ t x) 0 = deriv (fun t => u₂ t x) 0) :
    ∀ x, deriv (fun t => u₁ t x - u₂ t x) 0 = 0 := by
  intro x
  have hd₁ : DifferentiableAt ℝ (fun t => u₁ t x) 0 :=
    ((h₁_reg.differentiable two_ne_zero).comp
      (Differentiable.prodMk differentiable_id (differentiable_const x))).differentiableAt
  have hd₂ : DifferentiableAt ℝ (fun t => u₂ t x) 0 :=
    ((h₂_reg.differentiable two_ne_zero).comp
      (Differentiable.prodMk differentiable_id (differentiable_const x))).differentiableAt
  have : (fun t => u₁ t x - u₂ t x) = (fun t => u₁ t x) - (fun t => u₂ t x) := by
    ext; simp [Pi.sub_apply]
  rw [this, deriv_sub hd₁ hd₂, h_vel x, sub_self]

/-- Uniqueness for the wave equation: two $C^2$ solutions of the 1D wave equation that share
the same initial position $u(0, x)$ and the same initial velocity $\partial_t u(0, x)$ must
agree everywhere. -/
theorem wave_uniqueness (u₁ u₂ : ℝ → ℝ → ℝ)
    (h₁_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₁ p.1 p.2))
    (h₁_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₁ t'' x) t') t =
                       deriv (fun x' => deriv (fun x'' => u₁ t x'') x') x)
    (h₂_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₂ p.1 p.2))
    (h₂_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₂ t'' x) t') t =
                       deriv (fun x' => deriv (fun x'' => u₂ t x'') x') x)
    (h_pos : ∀ x, u₁ 0 x = u₂ 0 x)
    (h_vel : ∀ x, deriv (fun t => u₁ t x) 0 = deriv (fun t => u₂ t x) 0) :
    ∀ t x, u₁ t x = u₂ t x := by
  intro t x
  have h := zero_wave_is_zero (fun t x => u₁ t x - u₂ t x)
    (h₁_reg.sub h₂_reg)
    (wave_eq_of_sub u₁ u₂ h₁_reg h₂_reg h₁_wave h₂_wave)
    (fun x => by simp [h_pos x])
    (deriv_sub_zero u₁ u₂ h₁_reg h₂_reg h_vel)
    t x
  linarith

/-- Null decomposition for the wave equation: every $C^2$ solution $u$ of the 1D wave equation
can be written as $u(t, x) = F(x + t) + G(x - t)$ for some differentiable $F, G : \mathbb{R} \to
\mathbb{R}$ (travelling waves). -/
theorem wave_null_decomposition (u : ℝ → ℝ → ℝ)
    (hu_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
    (hu_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u t'' x) t') t =
                      deriv (fun x' => deriv (fun x'' => u t x'') x') x) :
    ∃ F G : ℝ → ℝ, (∀ t x, u t x = F (x + t) + G (x - t)) ∧
      Differentiable ℝ F ∧ Differentiable ℝ G := by
  set U := fun p : ℝ × ℝ => u p.1 p.2
  set f₀ : ℝ → ℝ := fun x => u 0 x
  set g₀ : ℝ → ℝ := fun x => deriv (fun t => u t x) 0

  have hf₀_C2 : ContDiff ℝ 2 f₀ :=
    show ContDiff ℝ 2 (U ∘ (Prod.mk 0)) from hu_reg.comp (contDiff_prodMk_right 0)

  have hg₀_C1 : ContDiff ℝ 1 g₀ := by
    have hU_diff : Differentiable ℝ U := hu_reg.differentiable (by norm_num)
    have key : g₀ = fun x => fderiv ℝ U (0, x) (1, 0) := funext fun x =>
      (((hU_diff (0, x)).hasFDerivAt.comp (0 : ℝ)
        ((hasFDerivAt_id 0).prodMk (hasFDerivAt_const x 0))).hasDerivAt
        |> fun h => (by convert h using 1 : HasDerivAt (fun t => u t x) _ 0)).deriv
    rw [key]
    exact ((hu_reg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).comp
      (contDiff_prodMk_right 0)).clm_apply contDiff_const
  have hg₀_cont : Continuous g₀ := hg₀_C1.continuous

  set G_int : ℝ → ℝ := fun z => ∫ y in (0 : ℝ)..z, g₀ y
  have hG_int_C2 : ContDiff ℝ 2 G_int := contDiff_antideriv g₀ hg₀_C1
  have hG_int_deriv : ∀ z, HasDerivAt G_int (g₀ z) z :=
    fun z => (hg₀_cont.integral_hasStrictDerivAt 0 z).hasDerivAt
  set F : ℝ → ℝ := fun z => f₀ z / 2 + G_int z / 2
  set G_fun : ℝ → ℝ := fun z => f₀ z / 2 - G_int z / 2
  have hF_C2 : ContDiff ℝ 2 F := (hf₀_C2.div_const 2).add (hG_int_C2.div_const 2)
  have hG_C2 : ContDiff ℝ 2 G_fun := (hf₀_C2.div_const 2).sub (hG_int_C2.div_const 2)
  have hFd : Differentiable ℝ F := hF_C2.differentiable (by norm_num)
  have hGd : Differentiable ℝ G_fun := hG_C2.differentiable (by norm_num)
  refine ⟨F, G_fun, ?_, hFd, hGd⟩

  set v : ℝ → ℝ → ℝ := fun t x => F (x + t) + G_fun (x - t)
  have hv_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => v p.1 p.2) :=
    (hF_C2.comp (contDiff_snd.add contDiff_fst)).add (hG_C2.comp (contDiff_snd.sub contDiff_fst))
  have hv_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => v t'' x) t') t =
      deriv (fun x' => deriv (fun x'' => v t x'') x') x :=
    general_solution_satisfies_wave_eq F G_fun hF_C2 hG_C2

  have h_pos : ∀ x, u 0 x = v 0 x := by
    intro x; show f₀ x = F (x + 0) + G_fun (x - 0)
    simp only [add_zero, sub_zero]
    show f₀ x = f₀ x / 2 + G_int x / 2 + (f₀ x / 2 - G_int x / 2); ring

  have h_vel : ∀ x, deriv (fun t => u t x) 0 = deriv (fun t => v t x) 0 := by
    intro x
    have hF_at : HasDerivAt (fun t => F (x + t)) (deriv F x) 0 := by
      have := hasDerivAt_comp_add_right' (hFd.differentiableAt (x := x + 0))
      simp only [add_zero] at this; exact this
    have hG_at : HasDerivAt (fun t => G_fun (x - t)) (-deriv G_fun x) 0 := by
      have := hasDerivAt_comp_sub_right' (hGd.differentiableAt (x := x - 0))
      simp only [sub_zero] at this; exact this
    have hv_deriv : HasDerivAt (fun t => v t x) (deriv F x - deriv G_fun x) 0 := by
      show HasDerivAt (fun t => F (x + t) + G_fun (x - t)) _ 0
      convert hF_at.add hG_at using 1
    rw [hv_deriv.deriv]

    have hf₀d : Differentiable ℝ f₀ := hf₀_C2.differentiable (by norm_num)
    have hF_hd : HasDerivAt F (deriv f₀ x / 2 + g₀ x / 2) x :=
      ((hf₀d x).hasDerivAt.div_const 2).add ((hG_int_deriv x).div_const 2)
    have hG_hd : HasDerivAt G_fun (deriv f₀ x / 2 - g₀ x / 2) x :=
      ((hf₀d x).hasDerivAt.div_const 2).sub ((hG_int_deriv x).div_const 2)
    rw [hF_hd.deriv, hG_hd.deriv]; ring

  exact wave_uniqueness u v hu_reg hu_wave hv_reg hv_wave h_pos h_vel

/-- In a null decomposition $u(t, x) = F(x + t) + G(x - t)$ matching initial data $f$ and $g$,
the right-moving wave $F$ satisfies $F'(x) = (f'(x) + g(x))/2$. -/
theorem hasDerivAt_F_of_null_decomp (f g F G : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (_hg : ContDiff ℝ 1 g)
    (hFd : Differentiable ℝ F)
    (hFG_init_pos : ∀ x, F x + G x = f x)
    (hFG_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0) :
    ∀ x, HasDerivAt F ((deriv f x + g x) / 2) x := by
  intro x
  have hGd : Differentiable ℝ G := by
    have : G = fun y => f y - F y := funext (fun y => by linarith [hFG_init_pos y])
    rw [this]; exact (hf.differentiable (by norm_num)).sub hFd

  have hFxt : HasDerivAt (fun t => F (x + t)) (deriv F x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add x
    convert (show HasDerivAt F (deriv F x) (x + 0) by
      rw [add_zero]; exact (hFd x).hasDerivAt).comp 0 h1 using 1; ring

  have hGxt : HasDerivAt (fun t => G (x - t)) (-deriv G x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x - t) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub x
    convert (show HasDerivAt G (deriv G x) (x - 0) by
      rw [sub_zero]; exact (hGd x).hasDerivAt).comp 0 h1 using 1; ring

  have hcomb : HasDerivAt (fun t => F (x + t) + G (x - t)) (deriv F x + -deriv G x) 0 :=
    hFxt.add hGxt

  have hvel : deriv F x - deriv G x = g x := by
    have := hcomb.unique (hFG_init_vel x); linarith

  have hpos : deriv F x + deriv G x = deriv f x := by
    have hf_eq : f = F + G := funext (fun y => by simp [Pi.add_apply]; linarith [hFG_init_pos y])
    have h : HasDerivAt f (deriv F x + deriv G x) x := by
      rw [hf_eq]; exact (hFd x).hasDerivAt.add (hGd x).hasDerivAt
    exact (h.deriv).symm

  have : deriv F x = (deriv f x + g x) / 2 := by linarith
  rw [← this]; exact (hFd x).hasDerivAt

/-- Any null decomposition $F(x + t) + G(x - t)$ that matches the initial position $f$ and
initial velocity $g$ must coincide with d'Alembert's solution. -/
theorem null_decomposition_determines_dalembert (f g : ℝ → ℝ) (F G : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hFd : Differentiable ℝ F)
    (hFG_init_pos : ∀ x, F x + G x = f x)
    (hFG_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0) :
    ∀ t x, F (x + t) + G (x - t) = dAlembertSolution f g t x := by
  have hF_hasderiv := hasDerivAt_F_of_null_decomp f g F G hf hg hFd hFG_init_pos hFG_init_vel
  intro t x
  have hG : ∀ y, G y = f y - F y := fun y => by linarith [hFG_init_pos y]
  rw [hG (x - t)]
  suffices h : F (x + t) - F (x - t) =
      (f (x + t) - f (x - t)) / 2 + (∫ y in (x - t)..(x + t), g y) / 2 by
    simp only [dAlembertSolution]; linarith
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg_cont : Continuous g := hg.continuous

  have ftc_F : ∫ y in (x - t)..(x + t), (fun y => (deriv f y + g y) / 2) y =
      F (x + t) - F (x - t) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF_hasderiv y)
      ((((hf.continuous_deriv (by norm_num)).add hg_cont).div_const _).intervalIntegrable _ _)

  have ftc_f : ∫ y in (x - t)..(x + t), deriv f y = f (x + t) - f (x - t) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => (hf_diff y).hasDerivAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  rw [← ftc_F]
  have hint_df : IntervalIntegrable (deriv f) volume (x - t) (x + t) :=
    (hf.continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hint_g : IntervalIntegrable g volume (x - t) (x + t) :=
    hg_cont.intervalIntegrable _ _

  have h_split : ∫ y in (x - t)..(x + t), (deriv f y + g y) / 2 =
      (∫ y in (x - t)..(x + t), deriv f y) / 2 +
      (∫ y in (x - t)..(x + t), g y) / 2 := by
    have : (fun y => (deriv f y + g y) / 2) =
        fun y => (1/2 : ℝ) * deriv f y + (1/2 : ℝ) * g y := by ext y; ring
    rw [this, intervalIntegral.integral_add (hint_df.const_mul _) (hint_g.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [h_split, ftc_f]

/-- Theorem 4.1 (d'Alembert's formula, uniqueness part). The unique $C^2$ solution $u$ of the
1D wave equation $-\partial_t^2 u + \partial_x^2 u = 0$ with initial data $u(0, x) = f(x)$ and
$\partial_t u(0, x) = g(x)$ is given by d'Alembert's formula. -/
theorem dAlembert_uniqueness (f g : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hu_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
    (hu_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u t'' x) t') t =
                      deriv (fun x' => deriv (fun x'' => u t x'') x') x)
    (hu_init_pos : ∀ x, u 0 x = f x)
    (hu_init_vel : ∀ x, HasDerivAt (fun t => u t x) (g x) 0) :
    ∀ t x, u t x = dAlembertSolution f g t x := by
  obtain ⟨F, G, hFG, hFd, _hGd⟩ := wave_null_decomposition u hu_reg hu_wave
  have h_init_pos : ∀ x, F x + G x = f x := by
    intro x
    have h := hFG 0 x
    simp [add_zero, sub_zero] at h
    linarith [hu_init_pos x]
  have h_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0 := by
    intro x
    have heq : (fun t => u t x) = (fun t => F (x + t) + G (x - t)) := by
      ext t; linarith [hFG t x]
    exact heq ▸ hu_init_vel x
  have h_dalembert := null_decomposition_determines_dalembert f g F G hf hg hFd h_init_pos h_init_vel
  intro t x
  rw [hFG t x]
  exact h_dalembert t x

/-- The odd extension of a function $f : [0, \infty) \to \mathbb{R}$ to all of $\mathbb{R}$:
$\tilde{f}(y) = f(y)$ for $y \ge 0$, and $\tilde{f}(y) = -f(-y)$ for $y < 0$. -/
def oddExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => if 0 ≤ y then f y else -(f (-y))

/-- If $f(0) = 0$, then the odd extension of $f$ is an odd function:
$\tilde{f}(-y) = -\tilde{f}(y)$. -/
theorem oddExtension_neg (f : ℝ → ℝ) (hf0 : f 0 = 0) (y : ℝ) :
    oddExtension f (-y) = -(oddExtension f y) := by
  simp only [oddExtension]
  by_cases hy : 0 < y
  · have h1 : ¬(0 ≤ -y) := by linarith
    have h2 : 0 ≤ y := le_of_lt hy
    simp [h1, h2, neg_neg]
  · by_cases hy0 : y = 0
    · subst hy0; simp [hf0]
    · have hy_neg : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
      have h1 : 0 ≤ -y := by linarith
      have h2 : ¬(0 ≤ y) := by linarith
      simp [h1, h2, neg_neg]

/-- The d'Alembert formula for the half-line wave equation with Dirichlet boundary condition
$u(t, 0) = 0$, obtained by applying d'Alembert's formula to the odd extensions of $f$ and $g$. -/
def dAlembertHalfLine (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  dAlembertSolution (oddExtension f) (oddExtension g) t x

/-- The integral of a continuous odd function over a symmetric interval vanishes:
$\int_{-t}^{t} h(y)\,dy = 0$ when $h(-y) = -h(y)$. -/
theorem integral_odd_symmetric {h : ℝ → ℝ} (hodd : ∀ y, h (-y) = -(h y))
    (hcont : Continuous h) (t : ℝ) :
    ∫ y in (-t)..t, h y = 0 := by
  have hint1 : IntervalIntegrable h MeasureTheory.volume (-t) 0 :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable h MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals hint1 hint2]
  suffices hsuff : ∫ y in (-t)..(0 : ℝ), h y = -(∫ y in (0 : ℝ)..t, h y) by linarith

  have key : ∫ y in (-t)..(0 : ℝ), h y = ∫ y in (0 : ℝ)..t, h (-y) := by
    rw [integral_comp_neg]
    simp
  rw [key]
  simp_rw [hodd]
  exact integral_neg

/-- If $g : \mathbb{R} \to \mathbb{R}$ is continuous with $g(0) = 0$, then its odd extension
is continuous. -/
theorem oddExtension_continuous (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg0 : g 0 = 0) : Continuous (oddExtension g) := by
  unfold oddExtension
  apply continuous_if_le continuous_const continuous_id
  · exact hg_cont.continuousOn
  · apply ContinuousOn.neg
    exact (hg_cont.comp continuous_neg).continuousOn
  · intro x hx
    simp at hx
    rw [← hx, hg0, neg_zero, hg0, neg_zero]

/-- If $g$ is continuous on $[0, \infty)$ with $g(0) = 0$, then its odd extension is
continuous on all of $\mathbb{R}$. -/
theorem oddExtension_continuous_of_continuousOn (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Ici 0))
    (hg0 : g 0 = 0) : Continuous (oddExtension g) := by
  unfold oddExtension
  apply continuous_if_le continuous_const continuous_id
  · exact hg_cont
  · apply ContinuousOn.neg
    exact hg_cont.comp continuous_neg.continuousOn (fun x hx => by
      simp only [Set.mem_Ici] at *; exact neg_nonneg.mpr hx)
  · intro x hx
    simp at hx
    rw [← hx, hg0, neg_zero, hg0, neg_zero]

/-- Derivative of the odd extension (from $C^1$ on $[0, \infty)$): for $g \in C^1([0, \infty))$
with $g(0) = 0$, the odd extension is differentiable everywhere, with derivative
$g'(\lvert x \rvert)$ at $x$. -/
lemma oddExtension_hasDerivAt_of_contDiffOn (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 1 g (Set.Ici 0)) (hg0 : g 0 = 0) (x : ℝ) :
    HasDerivAt (oddExtension g) (derivWithin g (Set.Ici 0) |x|) x := by
  have hg_diff : DifferentiableOn ℝ g (Set.Ici 0) := hg.differentiableOn (by norm_num)
  by_cases hxp : 0 < x
  · rw [abs_of_pos hxp]
    have hIci_nhds : Set.Ici (0:ℝ) ∈ nhds x :=
      mem_nhds_iff.mpr ⟨Set.Ioi 0, Set.Ioi_subset_Ici_self, isOpen_Ioi, hxp⟩
    rw [derivWithin_of_mem_nhds hIci_nhds]
    exact (hg_diff.differentiableAt hIci_nhds).hasDerivAt.congr_of_eventuallyEq
      (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds hxp,
          fun y hy => by simp [oddExtension, le_of_lt (Set.mem_Ioi.mp hy)]⟩)
  · by_cases hxn : x < 0
    · rw [abs_of_neg hxn]
      have hIci_nhds_mx : Set.Ici (0:ℝ) ∈ nhds (-x) :=
        mem_nhds_iff.mpr ⟨Set.Ioi 0, Set.Ioi_subset_Ici_self, isOpen_Ioi, neg_pos.mpr hxn⟩
      rw [derivWithin_of_mem_nhds hIci_nhds_mx]
      have h_eq : oddExtension g =ᶠ[nhds x] (fun y => -(g (-y))) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, isOpen_Iio.mem_nhds hxn,
            fun y hy => by simp only [oddExtension, not_le.mpr (Set.mem_Iio.mp hy), ite_false]⟩
      have h_deriv : HasDerivAt (fun y => -(g (-y))) (deriv g (-x)) x := by
        convert ((hg_diff.differentiableAt hIci_nhds_mx).hasDerivAt.comp x (hasDerivAt_neg x)).neg
          using 1
        ring
      exact h_deriv.congr_of_eventuallyEq h_eq
    · have hx0 : x = 0 := by linarith
      subst hx0; simp only [abs_zero]
      have h0_mem : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
      have hg_dwa : HasDerivWithinAt g (derivWithin g (Set.Ici 0) 0) (Set.Ici 0) 0 :=
        (hg_diff 0 h0_mem).hasDerivWithinAt
      have hoe_right : HasDerivWithinAt (oddExtension g) (derivWithin g (Set.Ici 0) 0)
          (Set.Ici 0) 0 :=
        hg_dwa.congr (fun y hy => by simp [oddExtension, Set.mem_Ici.mp hy])
          (by simp [oddExtension])
      have hoe_eq_neg_on_Iic : ∀ y ∈ Set.Iic (0:ℝ), oddExtension g y = -(g (-y)) := by
        intro y hy; simp only [oddExtension]
        by_cases h : 0 ≤ y
        · have hy0 : y = 0 := le_antisymm (Set.mem_Iic.mp hy) h
          subst hy0; simp [hg0]
        · simp [h]
      have hneg_maps : Set.MapsTo Neg.neg (Set.Iic (0:ℝ)) (Set.Ici (0:ℝ)) := by
        intro y hy; simp only [Set.mem_Ici, Set.mem_Iic] at *; linarith
      have hcomp : HasDerivWithinAt (g ∘ Neg.neg) (derivWithin g (Set.Ici 0) 0 * (-1))
          (Set.Iic 0) 0 :=
        (show HasDerivWithinAt g (derivWithin g (Set.Ici 0) 0) (Set.Ici 0) (Neg.neg (0:ℝ)) by
          simp only [neg_zero]; exact hg_dwa).comp 0
          (hasDerivAt_neg (0:ℝ)).hasDerivWithinAt hneg_maps
      have hng_dwa : HasDerivWithinAt (fun y => -(g (-y))) (derivWithin g (Set.Ici 0) 0)
          (Set.Iic 0) 0 := by
        convert hcomp.neg using 1; ring
      have hoe_left : HasDerivWithinAt (oddExtension g) (derivWithin g (Set.Ici 0) 0)
          (Set.Iic 0) 0 :=
        hng_dwa.congr hoe_eq_neg_on_Iic (by simp [oddExtension, hg0])
      have hunion := hoe_left.union hoe_right
      rw [Set.Iic_union_Ici] at hunion
      exact hunion.hasDerivAt Filter.univ_mem

/-- If $g \in C^1([0, \infty))$ with $g(0) = 0$, then the odd extension of $g$ is in
$C^1(\mathbb{R})$. -/
theorem oddExtension_contDiff_one_of_contDiffOn (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 1 g (Set.Ici 0)) (hg0 : g 0 = 0) :
    ContDiff ℝ 1 (oddExtension g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (oddExtension_hasDerivAt_of_contDiffOn g hg hg0 x).differentiableAt, ?_⟩
  have h_deriv_eq : deriv (oddExtension g) = fun x => derivWithin g (Set.Ici 0) |x| := by
    ext x; exact (oddExtension_hasDerivAt_of_contDiffOn g hg hg0 x).deriv
  rw [h_deriv_eq]
  exact (hg.continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl).comp_continuous
    continuous_abs (fun x => Set.mem_Ici.mpr (abs_nonneg x))

/-- Derivative of an even extension: for $h \in C^1([0, \infty))$ with $h'(0) = 0$, the
function $y \mapsto h(\lvert y \rvert)$ is differentiable everywhere with derivative given by
the odd extension of $h'$. -/
lemma evenExtension_hasDerivAt_of_contDiffOn (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Set.Ici 0))
    (hh'0 : derivWithin h (Set.Ici 0) 0 = 0) (x : ℝ) :
    HasDerivAt (fun y => h |y|) (oddExtension (derivWithin h (Set.Ici 0)) x) x := by
  have hh_diff : DifferentiableOn ℝ h (Set.Ici 0) := hh.differentiableOn (by norm_num)
  by_cases hxp : 0 < x
  · have h_eq : (fun y => h |y|) =ᶠ[nhds x] h :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 0, IsOpen.mem_nhds isOpen_Ioi hxp, fun y hy => by
          simp [abs_of_pos (Set.mem_Ioi.mp hy)]⟩
    rw [show oddExtension (derivWithin h (Set.Ici 0)) x = derivWithin h (Set.Ici 0) x from
      by simp [oddExtension, le_of_lt hxp]]
    have hIci_nhds : Set.Ici (0:ℝ) ∈ nhds x :=
      mem_nhds_iff.mpr ⟨Set.Ioi 0, Set.Ioi_subset_Ici_self, isOpen_Ioi, hxp⟩
    exact ((hh_diff x (Set.mem_Ici.mpr (le_of_lt hxp))).hasDerivWithinAt.hasDerivAt
      hIci_nhds).congr_of_eventuallyEq h_eq
  · by_cases hxn : x < 0
    · have h_eq : (fun y => h |y|) =ᶠ[nhds x] (fun y => h (-y)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, IsOpen.mem_nhds isOpen_Iio hxn, fun y hy => by
            simp [abs_of_neg (Set.mem_Iio.mp hy)]⟩
      rw [show oddExtension (derivWithin h (Set.Ici 0)) x =
          -(derivWithin h (Set.Ici 0) (-x)) from
        by simp only [oddExtension, show ¬(0 ≤ x) from by linarith, ite_false]]
      have hmx_pos : 0 < -x := by linarith
      have hIci_nhds_mx : Set.Ici (0:ℝ) ∈ nhds (-x) :=
        mem_nhds_iff.mpr ⟨Set.Ioi 0, Set.Ioi_subset_Ici_self, isOpen_Ioi, hmx_pos⟩
      have hda_mx := (hh_diff (-x) (Set.mem_Ici.mpr (le_of_lt hmx_pos))).hasDerivWithinAt.hasDerivAt
        hIci_nhds_mx
      exact (show HasDerivAt (fun y => h (-y)) (-(derivWithin h (Set.Ici 0) (-x))) x from by
        convert hda_mx.comp x (hasDerivAt_neg x) using 1; ring).congr_of_eventuallyEq h_eq
    · have hx0 : x = 0 := by linarith
      subst hx0
      rw [show oddExtension (derivWithin h (Set.Ici 0)) 0 = 0 from
        by simp [oddExtension, hh'0]]
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      simp only [zero_add, smul_zero, sub_zero, abs_zero]
      have h0_mem : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
      have hda : HasDerivWithinAt h 0 (Set.Ici 0) 0 := by
        have := (hh_diff 0 h0_mem).hasDerivWithinAt; rwa [hh'0] at this
      rw [← nhdsGE_sup_nhdsLE (0 : ℝ), Asymptotics.isLittleO_sup]
      constructor
      · have hda_o := hda.isLittleO
        simp only [sub_zero] at hda_o
        exact hda_o.congr'
          (eventually_nhdsWithin_of_forall (fun y (hy : y ∈ Set.Ici 0) => by
            simp [abs_of_nonneg (Set.mem_Ici.mp hy)])) Filter.EventuallyEq.rfl
      · have hneg_maps : Set.MapsTo Neg.neg (Set.Iic (0:ℝ)) (Set.Ici (0:ℝ)) := by
          intro y hy; simp only [Set.mem_Ici, Set.mem_Iic] at *; linarith
        have hda_neg : HasDerivWithinAt (fun y => h (-y)) 0 (Set.Iic 0) 0 := by
          convert (show HasDerivWithinAt h 0 (Set.Ici 0) (Neg.neg (0:ℝ)) from by
            simp only [neg_zero]; exact hda).comp 0
            (hasDerivAt_neg (0:ℝ)).hasDerivWithinAt hneg_maps using 1; ring
        have hda_neg_o := hda_neg.isLittleO
        simp only [sub_zero, neg_zero] at hda_neg_o
        exact hda_neg_o.congr'
          (eventually_nhdsWithin_of_forall (fun y (hy : y ∈ Set.Iic 0) => by
            simp [abs_of_nonpos (Set.mem_Iic.mp hy)])) Filter.EventuallyEq.rfl

/-- If $f \in C^2([0, \infty))$ with $f(0) = 0$ and $f''(0) = 0$, then the odd extension of $f$
is in $C^2(\mathbb{R})$. The compatibility condition $f''(0) = 0$ is necessary for smoothness
across the origin. -/
theorem oddExtension_contDiff_two_of_contDiffOn (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hf0 : f 0 = 0)
    (hf''0 : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0) :
    ContDiff ℝ 2 (oddExtension f) := by
  have hf1 : ContDiffOn ℝ 1 f (Set.Ici 0) := hf.of_le (by norm_num)
  have hda := oddExtension_hasDerivAt_of_contDiffOn f hf1 hf0

  have hf'_C1 : ContDiffOn ℝ 1 (derivWithin f (Set.Ici 0)) (Set.Ici 0) :=
    hf.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)

  have hf''0' : derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0) 0 = 0 := by
    have : iteratedDerivWithin 2 f (Set.Ici 0) 0 =
      derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0) 0 := by
      simp [iteratedDerivWithin_succ]
    linarith


  have hevda := evenExtension_hasDerivAt_of_contDiffOn
    (derivWithin f (Set.Ici 0)) hf'_C1 hf''0'

  have key : ContDiff ℝ (1 + 1) (oddExtension f) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hda x).differentiableAt, fun h => by simp at h, ?_⟩
    have h_deriv_eq : deriv (oddExtension f) = fun x => derivWithin f (Set.Ici 0) |x| := by
      ext x; exact (hda x).deriv
    rw [h_deriv_eq]

    have key2 : ContDiff ℝ (0 + 1) (fun x => derivWithin f (Set.Ici 0) |x|) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun x => (hevda x).differentiableAt, fun h => by simp at h, ?_⟩
      have h_deriv_eq2 : deriv (fun x => derivWithin f (Set.Ici 0) |x|) =
          oddExtension (derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0)) := by
        ext x; exact (hevda x).deriv
      rw [h_deriv_eq2]

      exact contDiff_zero.mpr (oddExtension_continuous_of_continuousOn
        (derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0))
        (hf'_C1.continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl) hf''0')
    exact_mod_cast key2
  exact_mod_cast key

/-- Derivative of the odd extension (from $C^1$ on all of $\mathbb{R}$): if $g \in
C^1(\mathbb{R})$ and $g(0) = 0$, then the odd extension is differentiable everywhere with
derivative $g'(\lvert x \rvert)$ at $x$. -/
lemma oddExtension_hasDerivAt (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0) (x : ℝ) :
    HasDerivAt (oddExtension g) (deriv g |x|) x := by
  have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  by_cases hxp : 0 < x
  · have h_eq : oddExtension g =ᶠ[nhds x] g :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 0, IsOpen.mem_nhds isOpen_Ioi hxp, fun y hy =>
          by simp [oddExtension, le_of_lt (Set.mem_Ioi.mp hy)]⟩
    rw [abs_of_pos hxp]
    exact ((hg_diff x).hasDerivAt).congr_of_eventuallyEq h_eq
  · by_cases hxn : x < 0
    · have h_eq : oddExtension g =ᶠ[nhds x] (fun y => -(g (-y))) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, IsOpen.mem_nhds isOpen_Iio hxn, fun y hy => by
            simp only [oddExtension, not_le.mpr (Set.mem_Iio.mp hy), ite_false]⟩
      rw [abs_of_neg hxn]
      have h1 : HasDerivAt (fun y => -y) (-1 : ℝ) x := hasDerivAt_neg x
      have h2 : HasDerivAt g (deriv g (-x)) (-x) := (hg_diff (-x)).hasDerivAt
      have h4 : HasDerivAt (fun y => -(g (-y))) (deriv g (-x)) x := by
        have h3 := (h2.comp x h1).neg; convert h3 using 1; ring
      exact h4.congr_of_eventuallyEq h_eq
    ·
      have hx0 : x = 0 := by linarith
      subst hx0; simp only [abs_zero]
      have hg_at : HasDerivAt g (deriv g 0) 0 := (hg_diff 0).hasDerivAt
      have hng : HasDerivAt (fun y => -(g (-y))) (deriv g 0) 0 := by
        have h1 : HasDerivAt (fun y => -y) (-1 : ℝ) (0 : ℝ) := hasDerivAt_neg 0
        have h2 : HasDerivAt g (deriv g 0) (-(0 : ℝ)) := by rw [neg_zero]; exact hg_at
        have h3 := (h2.comp 0 h1).neg; convert h3 using 1; ring
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      have h0 : oddExtension g 0 = g 0 := by simp [oddExtension]
      simp only [zero_add, h0, hg0, sub_zero]
      rw [← nhdsGE_sup_nhdsLE (0 : ℝ), Asymptotics.isLittleO_sup]
      rw [hasDerivAt_iff_isLittleO_nhds_zero] at hg_at hng
      simp only [zero_add, hg0, sub_zero] at hg_at
      simp only [zero_add, neg_zero, hg0, neg_zero, sub_zero] at hng
      exact ⟨
        (hg_at.mono nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall (fun h (hh : h ∈ Set.Ici 0) => by
            show g h - h • deriv g 0 = oddExtension g h - h • deriv g 0
            congr 1; simp [oddExtension, Set.mem_Ici.mp hh]))
          Filter.EventuallyEq.rfl,
        (hng.mono nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall (fun h (hh : h ∈ Set.Iic 0) => by
            show -g (-h) - h • deriv g 0 = oddExtension g h - h • deriv g 0
            congr 1; simp only [oddExtension]
            split_ifs with h0
            · have : h = 0 := le_antisymm (Set.mem_Iic.mp hh) h0; subst this; simp [hg0]
            · rfl))
          Filter.EventuallyEq.rfl⟩

/-- If $g \in C^1(\mathbb{R})$ with $g(0) = 0$, then the odd extension of $g$ is in
$C^1(\mathbb{R})$. -/
theorem oddExtension_contDiff_one (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hg0 : g 0 = 0) :
    ContDiff ℝ 1 (oddExtension g) := by
  have hda := oddExtension_hasDerivAt g hg hg0
  have key : ContDiff ℝ (0 + 1) (oddExtension g) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hda x).differentiableAt, fun h => by simp at h, ?_⟩
    have h_deriv_eq : deriv (oddExtension g) = fun x => deriv g |x| := by
      ext x; exact (hda x).deriv
    rw [h_deriv_eq]
    exact contDiff_zero.mpr ((hg.continuous_deriv (by norm_num)).comp continuous_abs)
  exact_mod_cast key

/-- Derivative of an even extension (from $C^1$ on all of $\mathbb{R}$): if $h \in
C^1(\mathbb{R})$ and $h'(0) = 0$, then $y \mapsto h(\lvert y \rvert)$ is differentiable
everywhere with derivative the odd extension of $h'$. -/
lemma evenExtension_deriv_hasDerivAt (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hh'0 : deriv h 0 = 0) (x : ℝ) :
    HasDerivAt (fun y => h |y|) (oddExtension (deriv h) x) x := by
  have hh_diff : Differentiable ℝ h := hh.differentiable (by norm_num)
  by_cases hxp : 0 < x
  · have h_eq : (fun y => h |y|) =ᶠ[nhds x] h :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 0, IsOpen.mem_nhds isOpen_Ioi hxp, fun y hy => by
          simp [abs_of_pos (Set.mem_Ioi.mp hy)]⟩
    have : oddExtension (deriv h) x = deriv h x := by
      simp [oddExtension, le_of_lt hxp]
    rw [this]
    exact (hh_diff x).hasDerivAt.congr_of_eventuallyEq h_eq
  · by_cases hxn : x < 0
    · have h_eq : (fun y => h |y|) =ᶠ[nhds x] (fun y => h (-y)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, IsOpen.mem_nhds isOpen_Iio hxn, fun y hy => by
            simp [abs_of_neg (Set.mem_Iio.mp hy)]⟩
      have : oddExtension (deriv h) x = -(deriv h (-x)) := by
        simp only [oddExtension, show ¬(0 ≤ x) from by linarith, ite_false]
      rw [this]
      have hd : HasDerivAt (fun y => h (-y)) (-(deriv h (-x))) x := by
        convert (hh_diff (-x)).hasDerivAt.comp x (hasDerivAt_neg x) using 1; ring
      exact hd.congr_of_eventuallyEq h_eq
    · have hx0 : x = 0 := by linarith
      subst hx0
      have : oddExtension (deriv h) 0 = 0 := by simp [oddExtension, hh'0]
      rw [this]
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      simp only [zero_add, smul_zero, sub_zero, abs_zero]
      have hda : HasDerivAt h 0 0 := by
        have := (hh_diff 0).hasDerivAt; rwa [hh'0] at this
      have hda_o := hda.isLittleO
      simp only [smul_zero, sub_zero] at hda_o
      rw [← nhdsGE_sup_nhdsLE (0 : ℝ), Asymptotics.isLittleO_sup]
      constructor
      · exact (hda_o.mono nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall (fun y (hy : y ∈ Set.Ici 0) => by
            simp [abs_of_nonneg (Set.mem_Ici.mp hy)])) Filter.EventuallyEq.rfl
      · have hda_neg : HasDerivAt (fun y => h (-y)) 0 0 := by
          have : HasDerivAt h 0 (-(0 : ℝ)) := by rw [neg_zero]; exact hda
          convert this.comp 0 (hasDerivAt_neg 0) using 1; ring
        have hda_neg_o := hda_neg.isLittleO
        simp only [smul_zero, sub_zero, neg_zero] at hda_neg_o
        exact (hda_neg_o.mono nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall (fun y (hy : y ∈ Set.Iic 0) => by
            simp [abs_of_nonpos (Set.mem_Iic.mp hy)])) Filter.EventuallyEq.rfl

/-- If $f \in C^2(\mathbb{R})$ with $f(0) = 0$ and $f''(0) = 0$, then the odd extension of $f$
is in $C^2(\mathbb{R})$. -/
theorem oddExtension_contDiff_two (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hf''0 : deriv (deriv f) 0 = 0) :
    ContDiff ℝ 2 (oddExtension f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hda := oddExtension_hasDerivAt f hf1 hf0
  have hf' : ContDiff ℝ 1 (deriv f) := by
    have : ContDiff ℝ ((1 : ℕ∞) + 1) f := by exact_mod_cast hf
    exact this.deriv'
  have hf'_cont : Continuous (deriv (deriv f)) := hf'.continuous_deriv (by norm_num)
  have hevda := evenExtension_deriv_hasDerivAt (deriv f) hf' hf''0
  have key : ContDiff ℝ (1 + 1) (oddExtension f) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hda x).differentiableAt, fun h => by simp at h, ?_⟩
    have h_deriv_eq : deriv (oddExtension f) = fun x => deriv f |x| := by
      ext x; exact (hda x).deriv
    rw [h_deriv_eq]
    have key2 : ContDiff ℝ (0 + 1) (fun x => deriv f |x|) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun x => (hevda x).differentiableAt, fun h => by simp at h, ?_⟩
      have h_deriv_eq2 : deriv (fun x => deriv f |x|) =
          oddExtension (deriv (deriv f)) := by
        ext x; exact (hevda x).deriv
      rw [h_deriv_eq2]
      exact contDiff_zero.mpr (oddExtension_continuous _ hf'_cont hf''0)
    exact_mod_cast key2
  exact_mod_cast key

/-- Half-line d'Alembert formula in the case $0 \le t \le x$ (Corollary 4.0.1, first branch):
$u(t, x) = \frac{1}{2}(f(x + t) + f(x - t)) + \frac{1}{2}\int_{x-t}^{x+t} g(z)\,dz$. -/
theorem dAlembert_halfline_formula_txle (f g : ℝ → ℝ)
    (_hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (_hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) (htx : t ≤ x) :
    dAlembertHalfLine f g t x =
      (f (x + t) + f (x - t)) / 2 + (∫ z in (x - t)..(x + t), g z) / 2 := by
  simp only [dAlembertHalfLine, dAlembertSolution]
  have hxt_pos : 0 ≤ x + t := by linarith
  have hxmt_pos : 0 ≤ x - t := by linarith
  have hf1 : oddExtension f (x + t) = f (x + t) := by simp [oddExtension, hxt_pos]
  have hf2 : oddExtension f (x - t) = f (x - t) := by simp [oddExtension, hxmt_pos]
  have hg_cont : ContinuousOn g (Set.Ici 0) := hg.continuousOn
  have _hg_odd_ext_cont : Continuous (oddExtension g) :=
    oddExtension_continuous_of_continuousOn g hg_cont hg0
  have key_integral : ∫ y in (x - t)..(x + t), oddExtension g y = ∫ z in (x - t)..(x + t), g z := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [Set.uIcc_of_le (show x - t ≤ x + t from by linarith)] at hy
    simp [oddExtension, show 0 ≤ y from by linarith [hy.1]]
  rw [hf1, hf2, key_integral]

/-- Half-line d'Alembert formula in the case $0 \le x \le t$ (Corollary 4.0.1, second branch):
$u(t, x) = \frac{1}{2}(f(x + t) - f(t - x)) + \frac{1}{2}\int_{t - x}^{x + t} g(z)\,dz$. -/
theorem dAlembert_halfline_formula_xtle (f g : ℝ → ℝ)
    (_hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) (hxt : x ≤ t) :
    dAlembertHalfLine f g t x =
      (f (x + t) - f (t - x)) / 2 + (∫ z in (t - x)..(x + t), g z) / 2 := by
  simp only [dAlembertHalfLine, dAlembertSolution]
  have hxt_pos : 0 ≤ x + t := by linarith
  have hf1 : oddExtension f (x + t) = f (x + t) := by simp [oddExtension, hxt_pos]
  have hf2 : oddExtension f (x - t) = -(f (t - x)) := by
    by_cases heq : x = t
    · subst heq; simp [oddExtension, hf0]
    · have hlt : x < t := lt_of_le_of_ne hxt heq
      simp only [oddExtension, show ¬(0 ≤ x - t) from by linarith, ite_false]
      ring_nf
  have hg_cont : ContinuousOn g (Set.Ici 0) := hg.continuousOn
  have hg_odd_ext_cont : Continuous (oddExtension g) :=
    oddExtension_continuous_of_continuousOn g hg_cont hg0
  have key_integral : ∫ y in (x - t)..(x + t), oddExtension g y = ∫ z in (t - x)..(x + t), g z := by
    have hint1 : IntervalIntegrable (oddExtension g) volume (x - t) (t - x) :=
      hg_odd_ext_cont.intervalIntegrable _ _
    have hint2 : IntervalIntegrable (oddExtension g) volume (t - x) (x + t) :=
      hg_odd_ext_cont.intervalIntegrable _ _
    have h_split := (integral_add_adjacent_intervals hint1 hint2).symm
    have h_sym : ∫ y in (x - t)..(t - x), oddExtension g y = 0 := by
      have heq : x - t = -(t - x) := by ring
      rw [heq]
      exact integral_odd_symmetric (oddExtension_neg g hg0) (oddExtension_continuous_of_continuousOn g hg_cont hg0) (t - x)

    have h_pos_int : ∫ y in (t - x)..(x + t), oddExtension g y = ∫ y in (t - x)..(x + t), g y := by
      apply intervalIntegral.integral_congr
      intro y hy
      simp only [Set.uIcc_of_le (show t - x ≤ x + t from by linarith)] at hy
      simp [oddExtension, show 0 ≤ y from by linarith [hy.1]]
    linarith [h_split, h_sym, h_pos_int]
  rw [hf1, hf2, key_integral]
  ring

/-- Regularity for the half-line d'Alembert solution: under the standard assumptions plus the
compatibility condition $f''(0) = 0$, the half-line d'Alembert solution is in $C^2$ on
$[0, \infty) \times [0, \infty)$. -/
theorem dAlembert_halfline_regularity_proof (f g : ℝ → ℝ)
    (_hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (_hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (_hf0 : f 0 = 0) (_hg0 : g 0 = 0)
    (hcompat : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => dAlembertHalfLine f g p.1 p.2)
      (Set.Ici 0 ×ˢ Set.Ici 0) := by


  have hf_odd_C2 : ContDiff ℝ 2 (oddExtension f) :=
    oddExtension_contDiff_two_of_contDiffOn f _hf _hf0 hcompat

  have hg_odd_C1 : ContDiff ℝ 1 (oddExtension g) :=
    oddExtension_contDiff_one_of_contDiffOn g _hg _hg0

  have h_full : ContDiff ℝ 2 (fun p : ℝ × ℝ => dAlembertSolution (oddExtension f) (oddExtension g) p.1 p.2) :=
    dAlembert_regularity (oddExtension f) (oddExtension g) hf_odd_C2 hg_odd_C1

  exact h_full.contDiffOn

/-- The half-line d'Alembert solution is jointly $C^2$ on $[0, \infty) \times [0, \infty)$
when $f \in C^2$, $g \in C^1$, $f(0) = g(0) = 0$, and $f''(0) = 0$. -/
theorem dAlembert_halfline_regularity (f g : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hcompat : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => dAlembertHalfLine f g p.1 p.2)
      (Set.Ici 0 ×ˢ Set.Ici 0) :=
  dAlembert_halfline_regularity_proof f g hf hg hf0 hg0 hcompat

/-- The derivative of an even function at the origin vanishes: if $g(-x) = g(x)$ for all $x$,
then $g'(0) = 0$. -/
lemma deriv_zero_of_even (g : ℝ → ℝ) (heven : ∀ x, g (-x) = g x) :
    deriv g 0 = 0 := by
  have h1 : deriv g 0 = deriv (fun x => g (-x)) 0 := by
    congr 1; ext x; exact (heven x).symm
  rw [deriv_comp_neg] at h1
  simp at h1
  linarith

/-- The derivative of an odd function is even: if $h(-x) = -h(x)$ for all $x$, then
$h'(-x) = h'(x)$. -/
lemma deriv_even_of_odd (h : ℝ → ℝ) (hodd : ∀ x, h (-x) = -h x) (x : ℝ) :
    deriv h (-x) = deriv h x := by
  have h1 : (fun y => h (-y)) = fun y => -h y := by ext y; exact hodd y
  have h2 : deriv (fun y => h (-y)) x = -deriv h (-x) := deriv_comp_neg h x
  rw [h1] at h2
  rw [show (fun y => -h y) = -h from by ext; simp] at h2
  rw [deriv.neg] at h2
  linarith

/-- For a solution $u$ of the half-line wave problem with boundary condition $u(t, 0) = 0$,
the second spatial derivative of the odd extension (in $x$) vanishes at $x = 0$, for every
fixed $t \ge 0$. -/
lemma odd_extension_second_spatial_deriv_zero (u : ℝ → ℝ → ℝ)
    (_hu_reg : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ici 0 ×ˢ Set.Ici 0))
    (_hu_wave : ∀ t x, 0 ≤ t → 0 ≤ x →
      deriv (fun t' => deriv (fun t'' => u t'' x) t') t =
      deriv (fun x' => deriv (fun x'' => u t x'') x') x)
    (_hu_boundary : ∀ t, u t 0 = 0) (t : ℝ) (_ht : 0 ≤ t) :
    deriv (fun x' => deriv (fun x'' => if 0 ≤ x'' then u t x'' else -u t (-x'')) x') 0 = 0 := by

  set h := fun x'' => if 0 ≤ x'' then u t x'' else -u t (-x'')

  have h_odd : ∀ x, h (-x) = -h x := by
    intro x
    simp only [h]
    by_cases hx : 0 ≤ x
    · by_cases hx0 : x = 0
      · subst hx0; simp [_hu_boundary t]
      · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have : ¬(0 ≤ -x) := by linarith
        simp [hx, this]
    · have hx_neg : x < 0 := not_le.mp hx
      have hle : 0 ≤ -x := by linarith
      simp [hx, hle]

  have dh_even : ∀ x, deriv h (-x) = deriv h x := deriv_even_of_odd h h_odd

  exact deriv_zero_of_even (deriv h) dh_even









end WaveEquation1D
