/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Order

open Complex Filter

open scoped Topology

noncomputable section

/-- A complex function $f : \mathbb{C} \to \mathbb{C}$ is *holomorphic at* $z_0$
if it is complex-differentiable at $z_0$. -/
def HolomorphicAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  DifferentiableAt ℂ f z₀

/-- A complex function $f$ is *holomorphic on* an open set $\Omega \subseteq \mathbb{C}$
if it is complex-differentiable at every point of $\Omega$. -/
def HolomorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  DifferentiableOn ℂ f Ω

/-- A complex function is *entire* if it is holomorphic on all of $\mathbb{C}$. -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f


open Bornology Set in
/-- **Liouville's theorem.**  A bounded entire function on $\mathbb{C}$
is constant. -/
theorem liouville_theorem {f : ℂ → ℂ} (hf : IsEntire f) (hb : IsBounded (range f)) :
    ∃ c : ℂ, f = Function.const ℂ c :=
  hf.exists_eq_const_of_bounded hb

open Filter

open scoped Topology

/-- $f$ has a *zero of order* $k$ at $z_0$ if $k > 0$ and locally
$f(z) = (z - z_0)^k g(z)$ for some analytic $g$ with $g(z_0) \neq 0$. -/
def HasZeroOfOrder (k : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  0 < k ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ k * g z

/-- $f$ has a *pole of order* $k$ at $z_0$ iff $1/f$ has a zero of order $k$ at $z_0$. -/
def HasPoleOfOrder (k : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasZeroOfOrder k f⁻¹ z₀

/-- $f$ has a *simple zero* at $z_0$ if it has a zero of order $1$ there. -/
def HasSimpleZero (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasZeroOfOrder 1 f z₀

/-- $f$ has a *simple pole* at $z_0$ if it has a pole of order $1$ there. -/
def HasSimplePole (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasPoleOfOrder 1 f z₀

/-- Compatibility: $f$ has a zero of order $k > 0$ at $z_0$ iff its Mathlib
meromorphic order at $z_0$ equals $k$ (as a positive integer). -/
theorem hasZeroOfOrder_iff_meromorphicOrderAt {k : ℕ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) :
    HasZeroOfOrder k f z₀ ↔ 0 < k ∧ meromorphicOrderAt f z₀ = (k : ℤ) := by
  constructor
  · rintro ⟨hk, g, hg_an, hg_ne, hg_eq⟩
    refine ⟨hk, (meromorphicOrderAt_eq_int_iff hf).mpr ?_⟩
    exact ⟨g, hg_an, hg_ne, by
      filter_upwards [hg_eq] with z hz
      simp only [smul_eq_mul, zpow_natCast, hz]⟩
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
    exact ⟨g, hg_an, hg_ne, by
      filter_upwards [hg_eq] with z hz
      simp only [smul_eq_mul, zpow_natCast] at hz
      exact hz⟩

/-- Compatibility: $f$ has a pole of order $k > 0$ at $z_0$ iff its Mathlib
meromorphic order at $z_0$ equals $-k$. -/
theorem hasPoleOfOrder_iff_meromorphicOrderAt {k : ℕ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) :
    HasPoleOfOrder k f z₀ ↔ 0 < k ∧ meromorphicOrderAt f z₀ = (-↑k : ℤ) := by
  unfold HasPoleOfOrder
  rw [hasZeroOfOrder_iff_meromorphicOrderAt hf.inv]
  constructor
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    have h := meromorphicOrderAt_inv (f := f) (x := z₀)
    rw [hord] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    have h := meromorphicOrderAt_inv (f := f) (x := z₀)
    rw [hord] at h
    push_cast [neg_neg] at h
    exact h

/-- A function $f$ is *meromorphic on* an open set $\Omega$ if it is
meromorphic at every point of $\Omega$. -/
def IsMeromorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  MeromorphicOn f Ω

/-- `IsMeromorphicOn` unfolds to Mathlib's `MeromorphicOn`. -/
theorem isMeromorphicOn_iff {f : ℂ → ℂ} {Ω : Set ℂ} :
    IsMeromorphicOn f Ω ↔ MeromorphicOn f Ω :=
  Iff.rfl

/-- The *order* of $f$ at $z_0$, in $\mathbb{Z} \cup \{+\infty\}$: positive for
zeros, negative for poles, $+\infty$ if $f$ vanishes identically near $z_0$. -/
def ord (z₀ : ℂ) (f : ℂ → ℂ) : WithTop ℤ :=
  meromorphicOrderAt f z₀

end

open Set

/-- A *smooth curve* in $\mathbb{C}$: a continuously differentiable map
$\gamma : [a, b] \to \mathbb{C}$ on a real interval $[a, b]$. -/
structure SmoothCurve where
  a : ℝ
  b : ℝ
  hab : a ≤ b
  toFun : ℝ → ℂ
  contDiffOn : ContDiffOn ℝ 1 toFun (Icc a b)

namespace SmoothCurve

/-- Coerce a `SmoothCurve` to its underlying function $[a, b] \to \mathbb{C}$. -/
instance : CoeFun SmoothCurve (fun _ => ℝ → ℂ) := ⟨SmoothCurve.toFun⟩

/-- The image $\gamma([a, b]) \subseteq \mathbb{C}$ of a smooth curve. -/
def image (γ : SmoothCurve) : Set ℂ := γ.toFun '' Icc γ.a γ.b

/-- A smooth curve is continuous on its parameter interval $[a, b]$. -/
theorem continuousOn (γ : SmoothCurve) : ContinuousOn γ.toFun (Icc γ.a γ.b) :=
  γ.contDiffOn.continuousOn

end SmoothCurve

namespace SmoothCurve

open MeasureTheory

/-- The *contour integral* of $f$ along a smooth curve $\gamma$:
$\int_\gamma f \, dz = \int_a^b f(\gamma(t)) \gamma'(t) \, dt$. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (γ : SmoothCurve) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

/-- Definitional unfolding of the contour integral along a smooth curve. -/
theorem contourIntegral_def (f : ℂ → ℂ) (γ : SmoothCurve) :
    γ.contourIntegral f = ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t :=
  rfl

end SmoothCurve

/-- A *piecewise smooth curve* in $\mathbb{C}$: finitely many smooth pieces
$\gamma_0, \dots, \gamma_{n-1}$ glued end-to-end, with matching parameter
endpoints and continuous join. -/
structure PiecewiseSmoothCurve where
  n : ℕ
  hn : 0 < n
  pieces : Fin n → SmoothCurve
  endpoints_match : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    (pieces ⟨i.val + 1, hi⟩).a = (pieces i).b
  continuous_join : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    (pieces i).toFun (pieces i).b =
    (pieces ⟨i.val + 1, hi⟩).toFun (pieces ⟨i.val + 1, hi⟩).a

namespace PiecewiseSmoothCurve

/-- The starting parameter of a piecewise smooth curve (the $a$ of its first piece). -/
def a (γ : PiecewiseSmoothCurve) : ℝ := (γ.pieces ⟨0, γ.hn⟩).a

/-- The ending parameter of a piecewise smooth curve (the $b$ of its last piece). -/
def b (γ : PiecewiseSmoothCurve) : ℝ :=
  (γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).b

/-- The underlying function $\gamma : \mathbb{R} \to \mathbb{C}$ of a piecewise
smooth curve, defined piece-by-piece on the union of the parameter intervals
and $0$ outside. -/
noncomputable def toFun (γ : PiecewiseSmoothCurve) : ℝ → ℂ :=
  fun t =>
    if h : ∃ i : Fin γ.n, t ∈ Icc (γ.pieces i).a (γ.pieces i).b then
      (γ.pieces h.choose).toFun t
    else
      0

/-- A piecewise smooth curve is *simple* if $\gamma$ is injective on the
open parameter interval $(a, b)$. -/
def IsSimple (γ : PiecewiseSmoothCurve) : Prop :=
  InjOn γ.toFun (Ioo γ.a γ.b)

/-- A piecewise smooth curve is *closed* if its endpoints coincide:
$\gamma(a) = \gamma(b)$. -/
def IsClosed (γ : PiecewiseSmoothCurve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- The image of a piecewise smooth curve in $\mathbb{C}$: the union of the
images of its individual smooth pieces. -/
def image (γ : PiecewiseSmoothCurve) : Set ℂ :=
  ⋃ i : Fin γ.n, (γ.pieces i).toFun '' Icc (γ.pieces i).a (γ.pieces i).b



/-- The *contour integral* of $f$ along a piecewise smooth curve $\gamma$:
the sum of the contour integrals over each smooth piece. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (γ : PiecewiseSmoothCurve) : ℂ :=
  ∑ i : Fin γ.n, (γ.pieces i).contourIntegral f

/-- Definitional unfolding of the contour integral along a piecewise smooth curve. -/
theorem contourIntegral_def (f : ℂ → ℂ) (γ : PiecewiseSmoothCurve) :
    γ.contourIntegral f = ∑ i : Fin γ.n, (γ.pieces i).contourIntegral f :=
  rfl

end PiecewiseSmoothCurve

/-- View a smooth curve as a (degenerate) piecewise smooth curve with a single piece. -/
def SmoothCurve.toPiecewiseSmoothCurve (γ : SmoothCurve) : PiecewiseSmoothCurve where
  n := 1
  hn := Nat.one_pos
  pieces := fun _ => γ
  endpoints_match := fun _ hi => absurd hi (by omega)
  continuous_join := fun _ hi => absurd hi (by omega)

namespace SmoothCurve

open MeasureTheory

/-- Fundamental theorem of calculus for contour integrals along a smooth curve:
if $F$ is complex-differentiable along $\gamma$ and the chain-rule integrand is
integrable, then $\int_\gamma F' \, dz = F(\gamma(b)) - F(\gamma(a))$. -/
theorem contourIntegral_eq_sub_of_deriv
    (F : ℂ → ℂ) (γ : SmoothCurve)
    (hF : ∀ t ∈ Set.uIcc γ.a γ.b, DifferentiableAt ℂ F (γ.toFun t))
    (hγ : ∀ t ∈ Set.uIcc γ.a γ.b, DifferentiableAt ℝ γ.toFun t)
    (hint : IntervalIntegrable
      (fun t => deriv F (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    γ.contourIntegral (deriv F) = F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
  unfold contourIntegral
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hF t ht).hasDerivAt.comp t (hγ t ht).hasDerivAt) hint

end SmoothCurve

namespace PiecewiseSmoothCurve

open MeasureTheory Finset

/-- Telescoping sum lemma: if $G^b_i = G^a_{i+1}$ for consecutive indices, then
$\sum_{i} (G^b_i - G^a_i) = G^b_{n-1} - G^a_0$. -/
lemma telescoping_sum (n : ℕ) (hn : 0 < n)
    (G_b G_a : Fin n → ℂ)
    (hconnect : ∀ (i : Fin n) (hi : i.val + 1 < n),
      G_b i = G_a ⟨i.val + 1, hi⟩) :
    ∑ i : Fin n, (G_b i - G_a i) =
    G_b ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩ - G_a ⟨0, hn⟩ := by
  let g : ℕ → ℂ := fun j =>
    if hj : j < n then G_a ⟨j, hj⟩ else G_b ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩
  have hterms : ∀ i : Fin n, G_b i - G_a i = g (i.val + 1) - g i.val := by
    intro ⟨i, hi⟩
    simp only [g, hi, dite_true]
    by_cases h : i + 1 < n
    · simp only [h, dite_true]
      rw [← hconnect ⟨i, hi⟩ h]
    · simp only [h, dite_false]
      have hieq : i = n - 1 := by omega
      subst hieq
      rfl
  conv_lhs =>
    arg 2
    ext i
    rw [hterms i]
  rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j), Finset.sum_range_sub g]
  simp only [g, hn, dite_true, Nat.lt_irrefl, dite_false]

/-- **Theorem 14.13.**  Fundamental theorem of calculus for contour integrals
along piecewise smooth curves: $\int_\gamma F' \, dz = F(\gamma(b)) - F(\gamma(a))$. -/
theorem theorem_14_13
    (F : ℂ → ℂ) (γ : PiecewiseSmoothCurve)
    (hF : ∀ i : Fin γ.n, ∀ t ∈ Set.uIcc (γ.pieces i).a (γ.pieces i).b,
      DifferentiableAt ℂ F ((γ.pieces i).toFun t))
    (hγ : ∀ i : Fin γ.n, ∀ t ∈ Set.uIcc (γ.pieces i).a (γ.pieces i).b,
      DifferentiableAt ℝ (γ.pieces i).toFun t)
    (hint : ∀ i : Fin γ.n, IntervalIntegrable
      (fun t => deriv F ((γ.pieces i).toFun t) * deriv (γ.pieces i).toFun t)
      volume (γ.pieces i).a (γ.pieces i).b) :
    γ.contourIntegral (deriv F) =
      F ((γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).toFun
          (γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).b) -
      F ((γ.pieces ⟨0, γ.hn⟩).toFun (γ.pieces ⟨0, γ.hn⟩).a) := by
  unfold contourIntegral

  simp_rw [fun i => SmoothCurve.contourIntegral_eq_sub_of_deriv F (γ.pieces i)
    (hF i) (hγ i) (hint i)]

  exact telescoping_sum γ.n γ.hn _ _ (fun i hi => congrArg F (γ.continuous_join i hi))

end PiecewiseSmoothCurve


open Metric in
/-- **Theorem 14.14 (Cauchy's theorem, circle case).**  If $f$ is holomorphic on
the closed disk $\overline{B(c, R)}$, then its integral around the circle of
radius $R$ centred at $c$ vanishes. -/
theorem theorem_14_14_circle {R : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 ≤ R) (hf : DifferentiableOn ℂ f (closedBall c R)) :
    (∮ z in C(c, R), f z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty hf.continuousOn
    (fun _z ⟨hz, _⟩ => hf.differentiableAt (closedBall_mem_nhds_of_mem hz))

namespace Residue

open Complex Filter

open scoped Topology Classical

/-- The *residue* $\mathrm{Res}_{z_0}(f)$ of a meromorphic function $f$ at
$z_0$, computed via the formula
$\frac{1}{(k-1)!} \lim_{z \to z_0} \frac{d^{k-1}}{dz^{k-1}}\bigl[(z - z_0)^k f(z)\bigr]$
for the meromorphic order $k$, and $0$ if $f$ is not meromorphic at $z_0$. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  if h : MeromorphicAt f z₀ then
    if h.choose = 0 then 0
    else iteratedDeriv (h.choose - 1) (fun z => (z - z₀) ^ h.choose • f z) z₀ /
      ((h.choose - 1).factorial : ℂ)
  else 0

/-- The residue is zero when $f$ is not meromorphic at $z_0$. -/
@[simp]
theorem residue_of_not_meromorphicAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ¬MeromorphicAt f z₀) : residue f z₀ = 0 :=
  dif_neg hf

/-- The residue at a regular (analytic) point vanishes. -/
theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) : residue f z₀ = 0 := by
  unfold residue
  have hm : MeromorphicAt f z₀ := hf.meromorphicAt
  rw [dif_pos hm]
  split_ifs with hn
  · rfl
  · suffices h0 : iteratedDeriv (hm.choose - 1)
        (fun z => (z - z₀) ^ hm.choose • f z) z₀ = 0 by
      rw [h0, zero_div]
    have smul_eq : (fun z => (z - z₀) ^ hm.choose • f z) =
        (fun z => (z - z₀) ^ hm.choose * f z) := by
      ext z; simp [smul_eq_mul]
    rw [smul_eq]
    set n := hm.choose
    have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
    have hg : AnalyticAt ℂ (fun z => (z - z₀) ^ n * f z) z₀ := by
      rw [← smul_eq]; exact hm.choose_spec
    have hord : (n : ℕ∞) ≤ analyticOrderAt (fun z => (z - z₀) ^ n * f z) z₀ := by
      rw [show (fun z => (z - z₀) ^ n * f z) = ((fun z => z - z₀) ^ n * f) from by
        ext; simp [Pi.pow_apply, Pi.mul_apply]]
      rw [analyticOrderAt_mul
        (AnalyticAt.pow (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀) n) hf]
      rw [analyticOrderAt_pow (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀)]
      have h1 : (1 : ℕ∞) ≤ analyticOrderAt (fun z => z - z₀) z₀ := by
        rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl]
        rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀)]
        intro i hi; interval_cases i; simp [iteratedDeriv_zero]
      calc (n : ℕ∞) = n • 1 + 0 := by simp
        _ ≤ n • analyticOrderAt (fun z => z - z₀) z₀ + analyticOrderAt f z₀ := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left h1 (Nat.zero_le n)
          · exact zero_le _
    exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp hord)
      (n - 1) (by omega)

end Residue

export Residue (residue)




/-- If $f$ is meromorphic and $g$ is holomorphic on $\Omega$, then the
logarithmic-derivative product $g \cdot f'/f$ is meromorphic on $\Omega$. -/
theorem isMeromorphicOn_g_f'_over_f
    (f g : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (hf_mero : IsMeromorphicOn f Ω)
    (hg_holo : HolomorphicOn g Ω) :
    IsMeromorphicOn (fun z => g z * (deriv f z / f z)) Ω := by
  intro z hz
  have hf_z : MeromorphicAt f z := hf_mero z hz
  have hg_mero : MeromorphicAt g z :=
    (hg_holo.analyticAt (hΩ.mem_nhds hz)).meromorphicAt
  have key : MeromorphicAt (g • (deriv f • f⁻¹)) z :=
    hg_mero.smul (hf_z.deriv.smul hf_z.inv)
  refine key.congr (Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_)
  filter_upwards with w
  simp [smul_eq_mul, div_eq_mul_inv]

/-- At a point $z \in \Omega$ where $f$ is analytic and nonvanishing and $g$ is
holomorphic, the product $g \cdot f'/f$ is analytic at $z$. -/
theorem analyticAt_g_f'_over_f
    (f g : ℂ → ℂ) (z : ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω)
    (hg_holo : HolomorphicOn g Ω)
    (hz : z ∈ Ω)
    (hf_an : AnalyticAt ℂ f z) (hf_nz : f z ≠ 0) :
    AnalyticAt ℂ (fun z => g z * (deriv f z / f z)) z := by
  have hg_an : AnalyticAt ℂ g z := hg_holo.analyticAt (hΩ.mem_nhds hz)
  exact hg_an.fun_mul (hf_an.deriv.fun_div hf_an hf_nz)

