/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped ZeroAtInfty
open MeasureTheory Filter Topology

noncomputable section

namespace SobolevEmbedding

/-- A (strong) Sobolev space `H^m` on `ℝ^n`: smooth functions `u : ℝ^n → ℂ` of class
`C^m` such that each iterated Fréchet derivative `D^j u` (for `j ≤ m`) is square
integrable with respect to Lebesgue measure. -/
structure SobolevSpace (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  contDiff_toFun : ContDiff ℝ (m : ℕ∞) toFun
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpace n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpace.toFun⟩

/-- `H^m ⊂ H^{m'}` whenever `m' ≤ m`: lower the Sobolev order of an element by
restricting the derivative-integrability hypothesis. -/
def SobolevSpace.toLowerOrder {n : ℕ} {m m' : ℕ} (hle : m' ≤ m)
    (u : SobolevSpace n m) : SobolevSpace n m' where
  toFun := u.toFun
  contDiff_toFun := u.contDiff_toFun.of_le (Nat.cast_le.mpr hle)
  iteratedFDeriv_memLp j hj := u.iteratedFDeriv_memLp j (le_trans hj hle)


set_option synthInstance.maxHeartbeats 80000 in
/-- For `u ∈ H^m` and a coordinate direction `j`, the partial derivative
`∂_j u` has all iterated derivatives up to order `m-1` in `L^2`. This is the
key technical lemma used to define `SobolevSpace.partialDeriv`. -/
theorem partialDeriv_iteratedFDeriv_memLp {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) (i : ℕ) (hi : i ≤ m - 1) :
    MemLp (fun x => iteratedFDeriv ℝ i
      (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by

  have hmem := u.iteratedFDeriv_memLp (i + 1) (by omega)

  have hcd_fderiv : ContDiff ℝ (↑i : ℕ∞) (fderiv ℝ u.toFun) := by
    apply u.contDiff_toFun.fderiv_right
    norm_cast; omega

  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ i
        (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x‖ ≤
      ‖EuclideanSpace.single j (1 : ℝ)‖ *
        ‖iteratedFDeriv ℝ (i + 1) u.toFun x‖ := by
    intro x
    have h1 := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ u.toFun) (c := EuclideanSpace.single j (1 : ℝ)) (x := x)
      hcd_fderiv.contDiffAt (N := (↑i : ℕ∞)) (le_refl _)
    rw [norm_iteratedFDeriv_fderiv] at h1
    exact h1

  exact hmem.of_le_mul
    ((hcd_fderiv.clm_apply contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Partial derivative `∂_j u` as an element of `H^{m-1}`, given `u ∈ H^m`. -/
def SobolevSpace.partialDeriv {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) : SobolevSpace n (m - 1) where
  toFun := fun x => fderiv ℝ u.toFun x (EuclideanSpace.single j 1)
  contDiff_toFun := by
    have hle : ((↑(m - 1) : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((↑m : ℕ∞) : WithTop ℕ∞) := by
      norm_cast; exact (Nat.sub_add_cancel hm).le
    exact (ContDiff.fderiv_right u.contDiff_toFun hle).clm_apply contDiff_const
  iteratedFDeriv_memLp i hi := partialDeriv_iteratedFDeriv_memLp hm u j i hi


set_option synthInstance.maxHeartbeats 80000 in

/-- Iterate the partial derivative in direction `j` exactly `k` times, mapping
`H^m` into `H^{m-k}`. -/
def SobolevSpace.iteratedPartialDeriv {n : ℕ} {m : ℕ}
    (j : Fin n) : (k : ℕ) → (hk : k ≤ m) → SobolevSpace n m → SobolevSpace n (m - k)
  | 0, _, u => u.toLowerOrder (by omega)
  | k + 1, hk, u =>
    let v := SobolevSpace.iteratedPartialDeriv j k (by omega) u
    (v.partialDeriv (by omega) j).toLowerOrder (by omega)




























/-- Each iterated derivative of a Schwartz function vanishes at infinity (in the
cocompact filter). -/
theorem schwartz_iteratedFDeriv_tendsto_zero {n : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (j : ℕ) :
    Tendsto (fun x => iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC_pos, hC⟩ := φ.decay 1 j
  rw [Filter.hasBasis_cocompact.eventually_iff]
  refine ⟨Metric.closedBall 0 (C / ε), isCompact_closedBall 0 _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hx
  push_neg at hx
  simp only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  have hx_pos : 0 < ‖x‖ := by linarith [div_nonneg (le_of_lt hC_pos) (le_of_lt hε)]
  have h := hC x; simp only [pow_one] at h
  calc ‖iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖
      ≤ C / ‖x‖ := by rwa [le_div_iff₀ hx_pos, mul_comm]
    _ < C / (C / ε) := div_lt_div_of_pos_left hC_pos (by positivity) hx
    _ = ε := by field_simp


/-- General principle: if `F_i → g` uniformly and each `F_i` vanishes at infinity
(cocompactly), then so does `g`. -/
theorem tendsto_zero_of_tendstoUniformly_of_vanish'
    {α : Type*} [TopologicalSpace α]
    {E : Type*} [SeminormedAddCommGroup E]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → α → E} {g : α → E}
    (hunif : TendstoUniformly F g l)
    (hvanish : ∀ᶠ i in l, Tendsto (F i) (cocompact α) (𝓝 0)) :
    Tendsto g (cocompact α) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  rw [Metric.tendstoUniformly_iff] at hunif
  obtain ⟨i, hi_unif, hi_vanish⟩ := (hunif (ε / 2) hε2).and hvanish |>.exists
  rw [Metric.tendsto_nhds] at hi_vanish
  apply (hi_vanish (ε / 2) hε2).mono
  intro x hx
  calc dist (g x) 0
      ≤ dist (g x) (F i x) + dist (F i x) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hi_unif x) hx
    _ = ε := by ring








/-- Weak Sobolev space: a function whose iterated derivatives up to order `m`
are in `L^2`, but without an a priori smoothness assumption on the function
itself. Used as the input type for the Sobolev embedding. -/
structure SobolevSpaceWeak (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a weak Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpaceWeak n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpaceWeak.toFun⟩

/-- The (strong) Sobolev space embeds into the weak Sobolev space by forgetting
the a priori smoothness. -/
def SobolevSpace.toWeak {n m : ℕ} (u : SobolevSpace n m) : SobolevSpaceWeak n m where
  toFun := u.toFun
  iteratedFDeriv_memLp := u.iteratedFDeriv_memLp




/-- The smooth Sobolev space `H^∞ = ⋂_m H^m`: a function `u` that lies in every
`H^m` with a consistent underlying function. -/
structure SobolevInfty (n : ℕ) where
  mem_sobolev : ∀ m : ℕ, SobolevSpace n m
  consistent : ∀ m₁ m₂ : ℕ, (mem_sobolev m₁).toFun = (mem_sobolev m₂).toFun


end SobolevEmbedding

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

/-- Order `|α| = α₁ + ⋯ + α_n` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- The finite set of all multi-indices `α : Fin n → ℕ` with `|α| ≤ m`. -/
def multiIndicesBall (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (m + 1))).filter
    (fun α => multiIndexOrder α ≤ m)

/-- Membership criterion for `multiIndicesBall`: `α ∈ multiIndicesBall n m` iff
the total order `|α|` is at most `m`. -/
theorem mem_multiIndicesBall_iff {n m : ℕ} {α : Fin n → ℕ} :
    α ∈ multiIndicesBall n m ↔ multiIndexOrder α ≤ m := by
  simp only [multiIndicesBall, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro hord i
  exact Nat.lt_succ_of_le (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)) hord)

/-- The monomial `x^α = ∏ x_i^{α_i}` viewed as a complex-valued function on
`ℝ^n`. -/
def monomial (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∏ i : Fin n, (↑(x i) : ℂ) ^ (α i)

/-- Iterate the line derivative `∂_{x_j}` exactly `k` times on a Schwartz
function. -/
def iterSchwartzDerivCoord (j : Fin n) (k : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)))^[k] φ

/-- The multi-index partial derivative `∂^β` on Schwartz functions, defined by
iteratively applying coordinate derivatives in each direction `j` exactly
`β j` times. -/
def iterSchwartzDeriv (β : Fin n → ℕ) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j ψ => iterSchwartzDerivCoord j (β j) ψ) φ

section SchwartzLpEmbedding

open MeasureTheory

/-- `iterSchwartzDerivCoord` is additive in its Schwartz argument. -/
lemma iterSchwartzDerivCoord_map_add (j : Fin n) (k : ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (φ + ψ) =
      iterSchwartzDerivCoord j k φ + iterSchwartzDerivCoord j k ψ := by
  unfold iterSchwartzDerivCoord
  induction k generalizing φ ψ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivAdd.lineDerivOp_add]
    exact ih _ _

/-- `iterSchwartzDeriv β` is additive in its Schwartz argument. -/
lemma iterSchwartzDeriv_map_add (β : Fin n → ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (φ + ψ) =
      iterSchwartzDeriv β φ + iterSchwartzDeriv β ψ := by
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_add j (β j) _ _

/-- `iterSchwartzDerivCoord` is `ℂ`-linear in its Schwartz argument. -/
lemma iterSchwartzDerivCoord_map_smul (j : Fin n) (k : ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (c • φ) = c • iterSchwartzDerivCoord j k φ := by
  unfold iterSchwartzDerivCoord
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivSMul.lineDerivOp_smul]
    exact ih _

/-- `iterSchwartzDeriv β` is `ℂ`-linear in its Schwartz argument. -/
lemma iterSchwartzDeriv_map_smul (β : Fin n → ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (c • φ) = c • iterSchwartzDeriv β φ := by
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_smul j (β j) c _

/-- Every Schwartz derivative `∂^α φ` belongs to `L^2`. -/
theorem schwartzDerivMemLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemLp ((iterSchwartzDeriv α φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      EuclideanSpace ℝ (Fin n) → ℂ) 2 volume :=
  (iterSchwartzDeriv α φ).memLp 2

/-- Map a Schwartz function `φ` to the `L^2` equivalence class of `∂^α φ`. -/
noncomputable def schwartzToLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (schwartzDerivMemLp n α φ).toLp _

/-- `schwartzToLp` is additive in the Schwartz argument. -/
theorem schwartzToLp_add (α : Fin n → ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    schwartzToLp n α (φ + ψ) = schwartzToLp n α φ + schwartzToLp n α ψ := by
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (φ + ψ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      (⇑(iterSchwartzDeriv α φ) + ⇑(iterSchwartzDeriv α ψ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_add]
    simp [SchwartzMap.add_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).add (schwartzDerivMemLp n α ψ)) heq]
  exact MemLp.toLp_add _ _

/-- `schwartzToLp` is `ℂ`-linear in the Schwartz argument. -/
theorem schwartzToLp_smul (α : Fin n → ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    schwartzToLp n α (c • φ) = c • schwartzToLp n α φ := by
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (c • φ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      (c • ⇑(iterSchwartzDeriv α φ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_smul]
    simp [SchwartzMap.smul_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).const_smul c) heq]
  exact MemLp.toLp_const_smul c _

end SchwartzLpEmbedding

section SchwartzProdLp

end SchwartzProdLp

/-- Pairing `⟨f, φ⟩ = ∫ f(x) · φ(x) dx` of a `C_0` function `f` against a
Schwartz function `φ`, used to express tempered distributions of the form
arising in the Schwartz representation theorem. -/
def c0SchwartzPairing
    (f : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : ℂ :=
  ∫ x, f x * φ x


set_option maxHeartbeats 1600000 in
/-- Hahn–Banach + Riesz representation for sums of `L^2`-bounded operators:
given a linear functional `L : V → ℂ` controlled by `‖L v‖ ≤ C ∑_α ‖T α v‖_{L²}`,
there exist `L²` functions `g α` such that `L v = ∑_α ∫ g α · T α v`. The key
analytic tool used to derive the Schwartz representation theorem. -/
theorem hahn_banach_riesz_product_l2
    {E : Type*} [MeasureSpace E] [MeasureTheory.SigmaFinite (MeasureTheory.volume : MeasureTheory.Measure E)]
    {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (L : V →ₗ[ℂ] ℂ)
    (T : ι → V → E → ℂ)
    (hT_memLp : ∀ α ∈ A, ∀ v, MeasureTheory.MemLp (T α v) 2 MeasureTheory.volume)
    (hT_add : ∀ α ∈ A, ∀ v w, T α (v + w) =ᵐ[MeasureTheory.volume] T α v + T α w)
    (hT_smul : ∀ α ∈ A, ∀ (c : ℂ) v, T α (c • v) =ᵐ[MeasureTheory.volume] c • T α v)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ v, ‖L v‖ ≤ C * ∑ α ∈ A,
      (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
    ∃ (g : ι → E → ℂ),
      (∀ α ∈ A, MeasureTheory.MemLp (g α) 2 MeasureTheory.volume) ∧
      ∀ v, L v = ∑ α ∈ A, ∫ x, g α x * T α v x := by
  classical


  let H := PiLp 2 (fun (_ : ↥A) => ↥(Lp ℂ 2 (volume : Measure E)))
  let Φ : V →ₗ[ℂ] H :=
    { toFun := fun v => WithLp.toLp 2 (fun (i : ↥A) => (hT_memLp i.1 i.2 v).toLp _)
      map_add' := fun v w => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (v + w)).toLp _ =
          (hT_memLp α hα v).toLp _ + (hT_memLp α hα w).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (v + w))
          ((hT_memLp α hα v).add (hT_memLp α hα w)) (hT_add α hα v w)]
        exact MemLp.toLp_add _ _
      map_smul' := fun c v => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (c • v)).toLp _ = c • (hT_memLp α hα v).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (c • v))
          ((hT_memLp α hα v).const_smul c) (hT_smul α hα c v)]
        exact MemLp.toLp_const_smul c _ }


  have hΦ_comp_norm : ∀ v (i : ↥A),
      ‖(Φ v).ofLp i‖ = (∫ x, ‖T i.1 v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro v ⟨α, hα⟩
    show ‖(hT_memLp α hα v).toLp _‖ = _
    rw [Lp.norm_toLp, (hT_memLp α hα v).eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ _)]
    ring_nf

  have hbound' : ∀ v, ‖L v‖ ≤ C * ∑ i : ↥A, ‖(Φ v).ofLp i‖ := by
    intro v
    have hbd := hbound v
    rw [show ∑ α ∈ A, (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) =
      ∑ i : ↥A, ‖(Φ v).ofLp i‖ from by
        rw [← A.sum_coe_sort]; congr 1; ext ⟨α, hα⟩; exact (hΦ_comp_norm v ⟨α, hα⟩).symm] at hbd
    exact hbd

  have hker : ∀ v, Φ v = 0 → L v = 0 := by
    intro v hv
    have hzero : ∑ i : ↥A, ‖(Φ v).ofLp i‖ = 0 := by
      rw [hv]; simp [PiLp.zero_apply, WithLp.ofLp]
    have hbd := hbound' v
    rw [hzero, mul_zero] at hbd
    exact norm_eq_zero.mp (le_antisymm hbd (norm_nonneg _))


  have hwf : ∀ (v₁ v₂ : V), Φ v₁ = Φ v₂ → L v₁ = L v₂ := by
    intro v₁ v₂ heq
    have h : Φ (v₁ + (-1 : ℂ) • v₂) = 0 := by
      rw [Φ.map_add, Φ.map_smul]; simp [heq]
    have h0 := hker _ h
    have hL : L (v₁ + (-1 : ℂ) • v₂) = L v₁ - L v₂ := by
      rw [L.map_add, L.map_smul]
      simp [sub_eq_add_neg, neg_smul, one_smul]
    rw [hL] at h0
    exact sub_eq_zero.mp h0


  let ℓ_fun : ↥(LinearMap.range Φ) → ℂ := fun y => L (Classical.choose y.2)
  have hℓ_wf : ∀ (y : ↥(LinearMap.range Φ)) (v : V), Φ v = y.1 → ℓ_fun y = L v := by
    intro y v hv; exact hwf _ _ (by rw [Classical.choose_spec y.2, hv])

  let ℓ_lin : ↥(LinearMap.range Φ) →ₗ[ℂ] ℂ :=

    { toFun := ℓ_fun
      map_add' := fun a b => by
        have ha := Classical.choose_spec a.2
        have hb := Classical.choose_spec b.2
        have hab : Φ (Classical.choose a.2 + Classical.choose b.2) = (a : H) + b := by
          rw [Φ.map_add, ha, hb]
        have hkey := hwf _ _ (hab.trans (Classical.choose_spec (a + b).2).symm)
        simp only [ℓ_fun, L.map_add] at hkey ⊢
        exact hkey.symm
      map_smul' := fun c a => by
        have ha := Classical.choose_spec a.2
        have hca : Φ (c • Classical.choose a.2) = c • (a : H) := by
          rw [Φ.map_smul, ha]
        have hkey := hwf _ _ (hca.trans (Classical.choose_spec (c • a).2).symm)
        simp only [ℓ_fun, L.map_smul, RingHom.id_apply] at hkey ⊢
        exact hkey.symm }

  have hℓ_bound : ∀ y : ↥(LinearMap.range Φ), ‖ℓ_lin y‖ ≤
      (C * Real.sqrt A.card) * ‖(y : H)‖ := by
    intro ⟨y, hy⟩
    have hv := Classical.choose_spec hy
    show ‖L (Classical.choose hy)‖ ≤ _
    calc ‖L (Classical.choose hy)‖
        ≤ C * ∑ i : ↥A, ‖(Φ (Classical.choose hy)).ofLp i‖ := hbound' _
      _ = C * ∑ i : ↥A, ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ := by
          congr 2; ext i; congr 1
          exact congr_fun (congr_arg WithLp.ofLp hv) i

      _ ≤ C * (Real.sqrt A.card * Real.sqrt (∑ i : ↥A,
          ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ↥A) (fun _ => (1 : ℝ))
            (fun i => ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖)
          simp only [one_mul, one_pow, Finset.sum_const, Nat.smul_one_eq_cast,
            Finset.card_univ, Fintype.card_coe] at h
          exact h
      _ = (C * Real.sqrt A.card) * ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1‖ := by
          rw [PiLp.norm_eq_of_L2]; ring

  let ℓ_clm : ↥(LinearMap.range Φ) →L[ℂ] ℂ :=
    LinearMap.mkContinuous ℓ_lin (C * Real.sqrt A.card) hℓ_bound
  obtain ⟨L', hL'ext, _⟩ := exists_extension_norm_eq (LinearMap.range Φ) ℓ_clm

  set G := (InnerProductSpace.toDual ℂ H).symm L'

  refine ⟨fun α => if hα : α ∈ A then
    fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x) else 0, ?_, ?_⟩
  ·
    intro α hα
    simp only [dif_pos hα]
    have hmem : MemLp (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) 2 volume := Lp.memLp _
    have heq : (fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x)) =
      star (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) := by
        ext x; simp [Pi.star_apply, RCLike.star_def]
    rw [heq]; exact hmem.star
  ·
    intro v

    have hmem : Φ v ∈ LinearMap.range Φ := ⟨v, rfl⟩
    have hLv_eq : L v = L' (Φ v) := by
      have h1 : L' (Φ v) = L' ↑(⟨Φ v, hmem⟩ : ↥(LinearMap.range Φ)) := rfl
      rw [h1, hL'ext ⟨Φ v, hmem⟩]
      symm
      simp only [ℓ_clm, LinearMap.mkContinuous_apply]
      exact hℓ_wf ⟨Φ v, hmem⟩ v rfl

    have hLv_inner : L v = @inner ℂ _ _ G (Φ v) := by
      rw [hLv_eq, ← InnerProductSpace.toDual_apply_apply]
      simp [G, LinearIsometryEquiv.apply_symm_apply]
    rw [hLv_inner, PiLp.inner_apply, ← A.sum_coe_sort]
    congr 1; ext ⟨α, hα⟩
    rw [MeasureTheory.L2.inner_def]

    refine MeasureTheory.integral_congr_ae ?_
    exact (MemLp.coeFn_toLp (hT_memLp α hα v)).mono fun x hx => by
      simp only [dif_pos hα, RCLike.inner_apply]

      have hx' : (↑↑((Φ v).ofLp ⟨α, hα⟩) : E → ℂ) x = T α v x := hx
      rw [hx']; ring

/-- If a continuous linear functional `u` on Schwartz space is bounded by the
sum of `L^2` norms of Schwartz derivatives `∂^α φ` over `|α| ≤ m`, then `u`
admits an `L^2` representation `u φ = ∑_α ∫ g_α · ∂^α φ`. -/
theorem schwartz_functional_l2_deriv_bound
    (n : ℕ) (u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ)
    (m : ℕ)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖u φ‖ ≤ C * ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
    ∃ (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ),
      (∀ α, α ∈ multiIndicesBall n m →
        MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m,
          ∫ x, g α x * (iterSchwartzDeriv α φ) x := by
  classical
  obtain ⟨C, hC, hbd⟩ := hbound
  exact hahn_banach_riesz_product_l2
    (E := EuclideanSpace ℝ (Fin n))
    (ι := Fin n → ℕ)
    (A := multiIndicesBall n m)
    (V := 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u.toLinearMap)
    (fun α φ x => (iterSchwartzDeriv α φ) x)
    (fun α _ φ => schwartzDerivMemLp n α φ)
    (fun α _ φ ψ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_add, SchwartzMap.add_apply, Pi.add_apply])
    (fun α _ c φ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_smul, SchwartzMap.smul_apply, Pi.smul_apply])
    C hC hbd




















/-- Hölder-type bound for the `L^2` × Schwartz pairing: `‖∫ g · ψ‖` is
controlled by a sum of `L^2` norms of Schwartz derivatives over
`multiIndicesBall n j`. -/
theorem l2_schwartz_pairing_bound (n j : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖∫ x, g x * ψ x‖ ≤ C * ∑ β ∈ multiIndicesBall n j,
        (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by

  set A := (∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) with hA_def
  refine ⟨A + 1, by linarith [Real.rpow_nonneg (integral_nonneg (fun x => by positivity) :
    (0:ℝ) ≤ ∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2:ℝ)) (1/2 : ℝ)], fun ψ => ?_⟩

  have hderiv_zero : iterSchwartzDeriv (0 : Fin n → ℕ) ψ = ψ := by
    unfold iterSchwartzDeriv
    have h : ∀ (j : Fin n) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        iterSchwartzDerivCoord j ((0 : Fin n → ℕ) j) φ = φ := by
      intro j φ
      simp only [Pi.zero_apply]
      unfold iterSchwartzDerivCoord
      simp [Function.iterate_zero]
    induction (List.finRange n) with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldr_cons]
      rw [ih, h]


  have h0_mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n j := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]

  have h_holder : ‖∫ x, g x * ψ x‖ ≤
      A * (∫ a : EuclideanSpace ℝ (Fin n),
        ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
    calc ‖∫ x, g x * ψ x‖
        ≤ ∫ x, ‖g x * ψ x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by
          congr 1; ext x; exact Complex.norm_mul (g x) (ψ x)
      _ ≤ A * (∫ a, ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
          have h22 : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
          have hg2 : MemLp g (ENNReal.ofReal 2) volume := by
            rwa [show ENNReal.ofReal 2 = 2 from by norm_num]
          have hψ2 : MemLp (ψ : EuclideanSpace ℝ (Fin n) → ℂ) (ENNReal.ofReal 2) volume := by
            rw [show ENNReal.ofReal 2 = 2 from by norm_num]
            exact ψ.memLp 2
          exact integral_mul_norm_le_Lp_mul_Lq h22 hg2 hψ2

  have h_term_eq : (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) =
    (∫ x, ‖(iterSchwartzDeriv (0 : Fin n → ℕ) ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    congr 1; congr 1; ext x; congr 1; congr 1
    have : (iterSchwartzDeriv (0 : Fin n → ℕ) ψ : EuclideanSpace ℝ (Fin n) → ℂ) x =
        (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
      rw [hderiv_zero]
    rw [this]

  have h_sum_nonneg : ∀ β ∈ multiIndicesBall n j,
      (0:ℝ) ≤ (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro β _
    exact Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _

  have h_le_sum : (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) ≤
    ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    rw [h_term_eq]
    exact Finset.single_le_sum h_sum_nonneg h0_mem

  have hA_nonneg : (0:ℝ) ≤ A :=
    Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have h_sum_nonneg' : (0:ℝ) ≤ ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) :=
    Finset.sum_nonneg h_sum_nonneg
  calc ‖∫ x, g x * ψ x‖
      ≤ A * (∫ a : EuclideanSpace ℝ (Fin n),
          ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := h_holder
    _ ≤ A * ∑ β ∈ multiIndicesBall n j,
          (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_le_sum hA_nonneg
    _ ≤ (A + 1) * ∑ β ∈ multiIndicesBall n j,
          (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by linarith) h_sum_nonneg'


/-- The product `g · ψ` of an `L^2` function and a Schwartz function is
integrable. -/
theorem l2_schwartz_mul_integrable (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MeasureTheory.Integrable (fun x => g x * ψ x)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
  hg.integrable_mul (ψ.memLp 2)






/-- Directional derivatives on Schwartz space commute: `∂_v ∂_w φ = ∂_w ∂_v φ`.
A consequence of Schwarz's symmetry of second derivatives. -/
lemma schwartz_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (φ : 𝓢(E, F)) :
    LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp w φ) =
    LineDeriv.lineDerivOp w (LineDeriv.lineDerivOp v φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x := by
    convert (SchwartzMap.fderivCLM ℝ E F φ).differentiableAt using 1
  rw [show ⇑(LineDeriv.lineDerivOp w φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y w from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv w φ y,
    fderiv_clm_apply hd (differentiableAt_const w),
    show ⇑(LineDeriv.lineDerivOp v φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y v from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv v φ y,
    fderiv_clm_apply hd (differentiableAt_const v)]
  simp
  exact second_derivative_symmetric
    (f := (↑φ : E → F)) (f' := fderiv ℝ (↑φ))
    (fun y => φ.differentiableAt.hasFDerivAt) hd.hasFDerivAt v w

/-- Iterated directional derivatives commute past a single directional
derivative: `∂_v^k ∂_w φ = ∂_w ∂_v^k φ`. -/
lemma iterate_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (k : ℕ) (φ : 𝓢(E, F)) :
    (LineDeriv.lineDerivOp v)^[k] (LineDeriv.lineDerivOp w φ) =
    LineDeriv.lineDerivOp w ((LineDeriv.lineDerivOp v)^[k] φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [schwartz_lineDerivOp_comm v w φ, ih]

/-- Two iterated directional derivatives commute: `∂_v^k ∂_w^m φ = ∂_w^m ∂_v^k φ`. -/
lemma iterate_iterate_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (k m : ℕ) (φ : 𝓢(E, F)) :
    (LineDeriv.lineDerivOp v)^[k] ((LineDeriv.lineDerivOp w)^[m] φ) =
    (LineDeriv.lineDerivOp w)^[m] ((LineDeriv.lineDerivOp v)^[k] φ) := by
  induction m generalizing φ with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [ih (LineDeriv.lineDerivOp w φ)]
    congr 1
    exact iterate_lineDerivOp_comm v w k φ

/-- Coordinate Schwartz derivatives commute: `∂_i^a ∂_j^b φ = ∂_j^b ∂_i^a φ`. -/
lemma iterSchwartzDerivCoord_comm {n : ℕ} (i j : Fin n) (a b : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord i a (iterSchwartzDerivCoord j b φ) =
    iterSchwartzDerivCoord j b (iterSchwartzDerivCoord i a φ) := by
  simp only [iterSchwartzDerivCoord]
  exact iterate_iterate_lineDerivOp_comm _ _ a b φ

/-- A coordinate Schwartz derivative commutes with the `foldr` used to define
`iterSchwartzDeriv`, allowing rearrangement of derivative orderings. -/
lemma iterSchwartzDerivCoord_comm_foldr {n : ℕ} (j : Fin n) (k : ℕ) (γ : Fin n → ℕ)
    (l : List (Fin n)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) φ) =
    l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) (iterSchwartzDerivCoord j k φ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [iterSchwartzDerivCoord_comm j i k (γ i), ih]

/-- Coordinate Schwartz derivatives compose by addition of orders:
`∂_j^b ∂_j^a φ = ∂_j^{a+b} φ`. -/
lemma iterSchwartzDerivCoord_add {n : ℕ} (j : Fin n) (a b : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j b (iterSchwartzDerivCoord j a φ) =
    iterSchwartzDerivCoord j (a + b) φ := by
  simp only [iterSchwartzDerivCoord]
  rw [Nat.add_comm, ← Function.iterate_add_apply]

/-- Composition of multi-index Schwartz derivatives:
`∂^β (∂^α φ) = ∂^{α + β} φ`. -/
theorem iterSchwartzDeriv_comp {n : ℕ} (α β : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (iterSchwartzDeriv α φ) = iterSchwartzDeriv (α + β) φ := by
  simp only [iterSchwartzDeriv]
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, Pi.add_apply]


    conv_lhs => rw [← iterSchwartzDerivCoord_comm_foldr j (α j) β l]


    rw [iterSchwartzDerivCoord_add j (α j) (β j), ih]
    simp only [Pi.add_apply]

/-- Additivity of multi-index order: `|α + β| = |α| + |β|`. -/
theorem multiIndexOrder_add {n : ℕ} (α β : Fin n → ℕ) :
    multiIndexOrder (α + β) = multiIndexOrder α + multiIndexOrder β := by
  simp only [multiIndexOrder, Pi.add_apply, Finset.sum_add_distrib]



/-- The multi-index ball is monotone in `m`. -/
theorem multiIndicesBall_mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') :
    multiIndicesBall n m ⊆ multiIndicesBall n m' := by
  intro α hα
  rw [mem_multiIndicesBall_iff] at hα ⊢
  exact le_trans hα h


/-- The `C_0`–Schwartz pairing distributes over a finite sum of `C_0`
functions. -/
theorem c0SchwartzPairing_sum_finset {ι : Type*} (s : Finset ι)
    (f : ι → C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    c0SchwartzPairing (∑ i ∈ s, f i) ψ = ∑ i ∈ s, c0SchwartzPairing (f i) ψ := by
  simp only [c0SchwartzPairing]
  have heval : ∀ x, (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
    intro x
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      simp only [Finset.sum_cons]
      rw [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, ih]
  simp_rw [heval, Finset.sum_mul]
  rw [integral_finset_sum]
  intro i _
  exact Integrable.bdd_mul (c := ‖(f i).toBCF‖) (ψ.integrable)
    ((f i).continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall
      (fun x => BoundedContinuousFunction.norm_coe_le_norm (f i).toBCF x))




/-- The finite set of multi-indices `α` with `α_i ≤ γ_i` for all `i`. -/
def multiIndicesBelow (n : ℕ) (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (γ i + 1))


/-- The zero multi-index monomial is the constant function `1`. -/
theorem monomial_zero_eq : monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
  ext x
  simp [monomial, Pi.zero_apply]

/-- The `C_0`–Schwartz pairing is zero whenever the `C_0` factor is zero. -/
theorem c0SchwartzPairing_zero (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
  simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply, zero_mul,
    MeasureTheory.integral_zero]

/-- The zero multi-index belongs to every `multiIndicesBall n M`. -/
theorem zero_mem_multiIndicesBall (n M : ℕ) :
    (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
  rw [mem_multiIndicesBall_iff]
  simp [multiIndexOrder, Pi.zero_apply]

/-- Rewrite the `C_0`-derivative representation in the form
`∑_{α,β} c0SchwartzPairing (f α β) (∂^β (x^α · φ))`, by placing the monomial
factor inside the test function via `SchwartzMap.smulLeftCLM`. -/
theorem representation_rewrite
    (n M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
        ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (f α β)
            (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by

  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩

  have hsmul : SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) φ = φ := by
    rw [monomial_zero_eq, SchwartzMap.smulLeftCLM_const]
    simp


  change (∑ γ ∈ multiIndicesBall n M,
      c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
    ∑ α ∈ multiIndicesBall n M, ∑ β ∈ multiIndicesBall n M,
      c0SchwartzPairing (if α = 0 then v β else 0)
        (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ))
  symm
  rw [Finset.sum_eq_single_of_mem (0 : Fin n → ℕ) (zero_mem_multiIndicesBall n M)
    (fun α _ hα => by
      simp only [hα, ite_false]
      exact Finset.sum_eq_zero fun β _ => c0SchwartzPairing_zero _)]
  simp [hsmul]



/-- Alternative rewrite where the monomial factor multiplies the derived test
function from outside: `∑_{α,β} c0SchwartzPairing (g α β) (x^α · ∂^β φ)`. -/
theorem representation_rewrite_form2
    (n M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (g : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
        ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (g α β)
            (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) := by

  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩

  have h0mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]

  have hmon0 : monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
    ext x; simp [monomial]

  have hsmul0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) ψ = ψ := by
    intro ψ
    have hfun : monomial (0 : Fin n → ℕ) = fun (_ : EuclideanSpace ℝ (Fin n)) => (1 : ℂ) := hmon0
    simp [hfun]

  have hpair0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
    intro ψ; simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero]


  symm

  have step1 : ∀ α β,
      c0SchwartzPairing (if α = (0 : Fin n → ℕ) then v β else 0)
        (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) =
      if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0 := by
    intro α β
    split_ifs with h
    · subst h; rw [hsmul0]
    · exact hpair0 _
  simp_rw [step1]

  have key : ∀ α ∈ multiIndicesBall n M, α ≠ (0 : Fin n → ℕ) →
      (∑ β ∈ multiIndicesBall n M,
        if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0) = 0 := by
    intro α _ hα
    simp [hα]
  rw [Finset.sum_eq_single_of_mem 0 h0mem key]
  simp


end SchwartzRepresentation

end
