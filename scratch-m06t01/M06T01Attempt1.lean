import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped Topology Pointwise

namespace MathlibExt.Analysis.Convex.KarushKuhnTucker

/-! Provided helper: copied verbatim (apart from the explicit `E` binders) from
Atlas `MathlibExt/Analysis/Convex/KarushKuhnTucker.lean`, where it is a private lemma.
It is already proved; do not change it. You may use it. -/

/-- Gordan alternative for continuous linear functionals: either they are
jointly strictly negative somewhere, or some nontrivial nonnegative
combination vanishes. Proved by strictly separating the negative orthant
from the range-plus-nonneg-orthant sum. -/
lemma gordan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ) :
    (∃ d : E, ∀ i, (ℓ i) d < 0) ∨
      ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ p ≠ 0 ∧ ∑ i, p i • ℓ i = 0 := by
  classical
  by_cases h : ∃ d : E, ∀ i, (ℓ i) d < 0
  · exact Or.inl h
  · right
    set Lmap : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi (fun i => (ℓ i).toLinearMap)
    have hLmap : ∀ d i, Lmap d i = (ℓ i) d := fun d i => rfl
    set L : Submodule ℝ (ι → ℝ) := Lmap.range with hL
    set U : Set (ι → ℝ) := {v | ∀ i, v i < 0}
    set O : Set (ι → ℝ) := {w | ∀ i, 0 ≤ w i}
    set C : Set (ι → ℝ) := (L : Set (ι → ℝ)) + O with hC
    have hLconv : Convex ℝ (L : Set (ι → ℝ)) := by
      intro x hx y hy a b ha hb _hab
      exact L.add_mem (L.smul_mem a hx) (L.smul_mem b hy)
    have hOconv : Convex ℝ O := by
      intro x hx y hy a b ha hb _hab i
      change 0 ≤ (a • x + b • y) i
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    have hCconv : Convex ℝ C := hLconv.add hOconv
    have hUopen : IsOpen U := by
      have hUU : U = ⋂ i, (fun v : ι → ℝ => v i) ⁻¹' (Set.Iio 0) := by
        ext v
        simp [U]
      rw [hUU]
      exact isOpen_iInter_of_finite
        (fun i => IsOpen.preimage (continuous_apply i) isOpen_Iio)
    have hUconv : Convex ℝ U := by
      intro x hx y hy a b ha hb hab i
      change (a • x + b • y) i < 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      have h1 : a * x i ≤ 0 := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt (hx i)) ha
        rwa [mul_zero] at h
      have h2 : b * y i ≤ 0 := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt (hy i)) hb
        rwa [mul_zero] at h
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hab
        rw [zero_mul, zero_add, hab, one_mul]
        exact hy i
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hlt : a * x i < 0 := mul_neg_of_pos_of_neg hapos (hx i)
        have hsum := add_lt_add_of_lt_of_le hlt h2
        rwa [add_zero] at hsum
    have hdisj : Disjoint U C := by
      rw [Set.disjoint_left]
      intro x hxU hxC
      rw [hC, Set.mem_add] at hxC
      obtain ⟨v, hvL, w, hwO, rfl⟩ := hxC
      simp only [hL] at hvL
      obtain ⟨d, rfl⟩ := hvL
      apply h
      refine ⟨d, fun i => ?_⟩
      have hvi : (Lmap d) i + w i < 0 := by
        rw [← Pi.add_apply]
        exact hxU i
      have h3 : (Lmap d) i < 0 := by linarith [hwO i]
      rw [hLmap d i] at h3
      exact h3
    obtain ⟨f, u, hUlt, hCge⟩ :=
      geometric_hahn_banach_open hUconv hUopen hCconv hdisj
    have h0C : (0 : ι → ℝ) ∈ C := by
      rw [hC, Set.mem_add]
      refine ⟨0, L.zero_mem, 0, fun i => le_refl 0, ?_⟩
      simp
    have hu0 : u ≤ 0 := by
      simpa using hCge 0 h0C
    have hscale : ∀ c : ℝ, c ≠ 0 → ∃ t : ℝ, t * c < u := by
      intro c hc
      by_cases hneg : c < 0
      · refine ⟨u / c + 1, ?_⟩
        rw [add_mul, div_mul_cancel₀ _ (ne_of_lt hneg), one_mul]
        linarith
      · have hpos : 0 < c :=
          lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hc)
        refine ⟨u / c - 1, ?_⟩
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hpos), one_mul]
        linarith
    have hLker : ∀ v ∈ (L : Set (ι → ℝ)), f v = 0 := by
      intro v hv
      by_contra hne
      obtain ⟨t, ht⟩ := hscale (f v) hne
      have hmem : t • v + 0 ∈ C := by
        rw [hC, Set.mem_add]
        exact ⟨t • v, L.smul_mem t hv, 0, fun i => le_refl 0, rfl⟩
      have hle := hCge _ hmem
      rw [map_add, map_smul, smul_eq_mul, map_zero, add_zero] at hle
      exact not_lt_of_ge hle ht
    set p : ι → ℝ := fun i => f (Pi.single i 1)
    have hp_apply : ∀ i, p i = f (Pi.single i 1) := fun i => rfl
    have hpi : ∀ i, 0 ≤ p i := by
      intro i
      by_contra hneg
      rw [not_le, hp_apply] at hneg
      set t : ℝ := |u / f (Pi.single i 1)| + 1 with ht
      have ht0 : 0 ≤ t := by
        rw [ht]
        positivity
      have hmem : 0 + t • Pi.single i 1 ∈ C := by
        rw [hC, Set.mem_add]
        refine ⟨0, L.zero_mem, t • Pi.single i 1, ?_, rfl⟩
        intro j
        show 0 ≤ (t • Pi.single i (1 : ℝ)) j
        rw [Pi.smul_apply, smul_eq_mul]
        apply mul_nonneg ht0
        rw [Pi.single_apply]
        split_ifs <;> simp
      have hle := hCge _ hmem
      rw [map_add, map_zero, zero_add, map_smul, smul_eq_mul] at hle
      have hlt : t * f (Pi.single i 1) < u := by
        rw [ht]
        have h1 : u / f (Pi.single i 1) < |u / f (Pi.single i 1)| + 1 :=
          lt_of_le_of_lt (le_abs_self _) (lt_add_one _)
        have h2 := mul_lt_mul_of_neg_right h1 hneg
        rw [div_mul_cancel₀ _ (ne_of_lt hneg)] at h2
        exact h2
      exact not_lt_of_ge hle hlt
    have hexpand : ∀ v : ι → ℝ, v = ∑ j, v j • Pi.single j (1 : ℝ) := by
      intro v
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k _ (fun h => absurd (Finset.mem_univ k) h)]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne]
        · exact smul_zero _
        · exact Ne.symm hb
    have hf_expand : ∀ v : ι → ℝ, f v = ∑ i, v i * p i := by
      intro v
      conv_lhs => rw [hexpand v, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      show f (v i • Pi.single i 1) = v i * p i
      rw [map_smul, smul_eq_mul, ← hp_apply]
    have hfun : ∑ i, p i • ℓ i = 0 := by
      ext d
      change (∑ i, p i • ℓ i) d = 0
      have e1 : (∑ i, p i • ℓ i) d = ∑ i, p i * (ℓ i) d := by
        rw [sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_apply, smul_eq_mul]
      have e2 : ∑ i, p i * (ℓ i) d = 0 := by
        have hmem : Lmap d ∈ (L : Set (ι → ℝ)) := Lmap.mem_range_self d
        have hz := hLker _ hmem
        rw [hf_expand] at hz
        rw [← hz]
        apply Finset.sum_congr rfl
        intro i _
        rw [hLmap, mul_comm]
      rw [e1]
      exact e2
    have hnz : p ≠ 0 := by
      intro hz
      have h1' : ∑ i, (-1 : ℝ) * p i < u := by
        have h1 := hUlt (fun _ => (-1 : ℝ)) (fun i => by simp)
        rwa [hf_expand] at h1
      rw [hz] at h1'
      simp at h1'
      linarith [hu0]
    exact ⟨p, hpi, hnz, hfun⟩

/--
Mixed-constraint Karush–Kuhn–Tucker necessary conditions under LICQ.
Minimize `f` subject to finitely many inequality constraints `g i y ≤ 0` and equality
constraints `h j y = 0` on a finite-dimensional real normed space. If `x` is feasible, is a
local minimum of `f` on the feasible set, `f` and every `g i` are differentiable at `x`, every
`h j` is `C¹` at `x`, and the derivatives of all equality constraints together with the
derivatives of the active inequality constraints are linearly independent (LICQ), then there
are inequality multipliers `lam ≥ 0` with complementary slackness and free equality multipliers
`mu` such that `fderiv f x + ∑ i, lam i • fderiv (g i) x + ∑ j, mu j • fderiv (h j) x = 0`.
-/
theorem karush_kuhn_tucker_mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {m p : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ}
    {h : Fin p → E → ℝ} {x : E}
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hh_diff : ∀ j, ContDiffAt ℝ 1 (h j) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (heq : ∀ j, h j x = 0)
    (hmin : IsLocalMinOn f {y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0} x)
    (hLICQ : LinearIndependent ℝ
      (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
        (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x))) :
    ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i x = 0) ∧
      fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x +
        ∑ j : Fin p, mu j • fderiv ℝ (h j) x = 0 := by
  classical
  -- Active inequality set and equality-derivative map.
  set A : Type := { i : Fin m // g i x = 0 } with hA_def
  set H : E →L[ℝ] (Fin p → ℝ) := ContinuousLinearMap.pi (fun j => fderiv ℝ (h j) x) with hH_def
  -- Pointwise action of `H` (proved without rewriting `H` itself, so `ker` types stay put).
  have hH_apply : ∀ (v : E) (j : Fin p), H v j = (fderiv ℝ (h j) x) v := by
    intro v j
    simp [hH_def]
  -- LICQ implies the equality derivatives alone are independent.
  have hindep_h : LinearIndependent ℝ (fun j : Fin p => fderiv ℝ (h j) x) := by
    have hcomp := hLICQ.comp _ Sum.inl_injective
    simpa [Function.comp] using hcomp
  -- The nonlinear equality map is strictly differentiable with derivative `H`.
  have hH_strict : HasStrictFDerivAt (fun y j => h j y) H x := by
    have hcomp : ∀ j : Fin p, HasStrictFDerivAt (fun y => h j y) (fderiv ℝ (h j) x) x := by
      intro j
      exact (hh_diff j).hasStrictFDerivAt (by norm_num)
    have hpi := HasStrictFDerivAt.pi hcomp
    simpa [hH_def] using hpi
  -- `H` is surjective: otherwise a nonzero functional vanishes on its range,
  -- giving a nontrivial relation among the independent equality derivatives.
  have hH_surj : (↑H : E →ₗ[ℝ] (Fin p → ℝ)).range = ⊤ := by
    by_contra hne
    have hAnn_ne : (LinearMap.range (↑H : E →ₗ[ℝ] (Fin p → ℝ))).dualAnnihilator ≠ ⊥ := by
      intro hbot
      apply hne
      rw [← Submodule.dualAnnihilator_eq_bot_iff]
      exact hbot
    obtain ⟨φ, hφ_mem, hφ_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAnn_ne
    have hφ_vanish : ∀ v : E, φ ((↑H : E →ₗ[ℝ] (Fin p → ℝ)) v) = 0 := by
      intro v
      exact (Submodule.mem_dualAnnihilator.mp hφ_mem) _ (LinearMap.mem_range_self _ _)
    -- Expand `φ` on the standard basis to get coefficients.
    set θ : Fin p → ℝ := fun j => φ (Pi.single j (1 : ℝ)) with hθ_def
    have hexpand : ∀ v : Fin p → ℝ, v = ∑ j, v j • Pi.single j (1 : ℝ) := by
      intro v
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k _ (fun h => absurd (Finset.mem_univ k) h)]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne]
        · exact smul_zero _
        · exact Ne.symm hb
    have hφ_expand : ∀ v : Fin p → ℝ, φ v = ∑ j, v j * θ j := by
      intro v
      conv_lhs => rw [hexpand v, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, hθ_def]
    have hθ_relation : ∑ j, θ j • (fderiv ℝ (h j) x) = 0 := by
      ext v
      have e1 : (∑ j, θ j • (fderiv ℝ (h j) x)) v
          = ∑ j, θ j * (fderiv ℝ (h j) x) v := by
        rw [sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_apply, smul_eq_mul]
      have e2 : (∑ j, θ j * (fderiv ℝ (h j) x) v) = 0 := by
        have hz := hφ_vanish v
        rw [hφ_expand] at hz
        rw [← hz]
        apply Finset.sum_congr rfl
        intro j _
        have hj : ((↑H : E →ₗ[ℝ] (Fin p → ℝ)) v) j = (fderiv ℝ (h j) x) v := by
          change H v j = _
          rw [hH_apply]
        rw [hj, mul_comm]
      change (∑ j, θ j • fderiv ℝ (h j) x) v = (0 : E →L[ℝ] ℝ) v
      rw [e1]
      have hzero : (0 : E →L[ℝ] ℝ) v = 0 := rfl
      rw [hzero]
      exact e2
    -- The relation forces `θ = 0` by independence.
    have hθ_zero : θ = 0 := by
      have hiff := Fintype.linearIndependent_iff (R := ℝ) (v := fun j : Fin p => fderiv ℝ (h j) x)
      exact (hiff.mp hindep_h) _ hθ_relation
    -- `θ = 0` forces `φ = 0`, contradiction.
    have hφ_zero : φ = 0 := by
      ext v
      rw [hφ_expand, hθ_zero]
      simp
    exact hφ_ne hφ_zero
  -- Kernel of `H` and the family of restricted functionals for Gordan.
  set K : Submodule ℝ E := LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ)) with hK_def
  set fam : Option A → (↥K →L[ℝ] ℝ) := fun o =>
    match o with
    | none => (fderiv ℝ f x).comp K.subtypeL
    | some a => (fderiv ℝ (g a.val) x).comp K.subtypeL
    with hfam_def
  have hfam_none : ∀ z : ↥K, (fam none) z = (fderiv ℝ f x) (z : E) := fun z => rfl
  have hfam_some : ∀ (a : A) (z : ↥K), (fam (some a)) z = (fderiv ℝ (g a.val) x) (z : E) :=
    fun a z => rfl
  -- The nonlinear equality map vanishes at `x`.
  have hHnl_zero : (fun y j => h j y) x = 0 := by
    funext j
    exact heq j
  -- Linearized claim: there is no feasible descent direction.
  -- Given `d` with `H d = 0`, `f' d < 0`, `g'_A d < 0`, the implicit function
  -- theorem yields a feasible curve through `x` with velocity `d`, along which
  -- `f` strictly decreases, contradicting local minimality.
  have hnodesc : ¬∃ d : E, (∀ j, (fderiv ℝ (h j) x) d = 0)
      ∧ (fderiv ℝ f x) d < 0 ∧ (∀ a : A, (fderiv ℝ (g a.val) x) d < 0) := by
    rintro ⟨d, hd_eq, hd_f, hd_g⟩
    -- `d` lies in the kernel of `H`.
    have hd_mem : d ∈ K := by
      rw [hK_def, LinearMap.mem_ker]
      change H d = 0
      funext j
      rw [hH_apply]
      exact hd_eq j
    -- Implicit-function data for the equality map at `x`.
    set φ := HasStrictFDerivAt.implicitFunction hH_strict hH_surj with hφ_def
    -- Base kernel coordinate and direction in the kernel.
    set y₀ : ↥K := φ.right_fun x with hy₀_def
    set dK : ↥K := ⟨d, hd_mem⟩ with hdK_def
    -- Feasible curve: kernel coordinate `y₀ + t • dK`, value coordinate `0`.
    set γ : ℝ → E := fun t => φ.implicitFunction 0 (y₀ + t • dK) with hγ_def
    -- `γ 0 = x`.
    have hγ_zero : γ 0 = x := by
      have hmem : φ.pt ∈ φ.toOpenPartialHomeomorph.source := φ.mem_source
      have hleft : φ.left_fun φ.pt = 0 := by
        change (fun y j => h j y) x = 0
        -- `φ.pt = x` and `φ.left_fun = Hnl` by construction of `implicitFunction`
        rw [φ.pt_eq, φ.left_fun_eq]
        exact hHnl_zero
      -- `γ 0 = g 0 y₀ = g (left x) (right x) = x`
      simp [hγ_def, hy₀_def, φ.implicitFunction_apply_mem_source hmem, hleft, φ.pt_eq]
    -- `γ` stays in the equality fiber near `0`.
    have hγ_fiber : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (fun y j => h j y) (γ t) = 0 := by
      have hmem : ((0 : Fin p → ℝ), y₀) ∈ φ.toOpenPartialHomeomorph.target := by
        rw [← φ.map_pt_mem_target φ.mem_source]
        simp [hy₀_def, hHnl_zero, φ.pt_eq, φ.left_fun_eq, φ.right_fun_eq]
      have hcont : ContinuousAt (fun t : ℝ => ((0 : Fin p → ℝ), y₀ + t • dK)) 0 :=
        continuousAt_const.prodMk (by fun_prop)
      have hev := hcont.eventually hmem
      filter_upwards [hev] with t ht
      change (fun y j => h j y) (γ t) = 0
      rw [hγ_def]
      exact φ.left_fun_implicitFunction ht
    -- `γ` has velocity `d` at `0`.
    have hγ_deriv : HasDerivAt γ d 0 := by
      have hderiv := φ.hasStrictFDerivAt_implicitFunction
      -- differentiate `t ↦ (0, y₀ + t • dK)` then compose with `g`
      have hinner : HasDerivAt (fun t : ℝ => ((0 : Fin p → ℝ), y₀ + t • dK)) ((0 : Fin p → ℝ), dK) 0 :=
        (hasDerivAt_const 0 ((0 : Fin p → ℝ))).prodMk (by simpa using (HasDerivAt.add_const _ _ (HasDerivAt.smul_const _ _ (hasDerivAt_id 0))))
      have hcomp := hderiv.comp_hasDerivAt 0 hinner
      -- the derivative of `g` at `(0, y₀)` sends `(0, dK)` to `d`
      simpa [hγ_def, φ.implicitFunction_deriv_apply, hdK_def] using hcomp
    -- From here the descent direction contradicts minimality (see below).
    -- Continuity of `γ` at `0` and limit `x`.
    have hγ_cont : ContinuousAt γ 0 := hγ_deriv.continuousAt
    have hγ_tendsto : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa [hγ_zero] using hγ_cont.tendsto
    -- Derivatives of the compositions `f ∘ γ` and `g ∘ γ` at `0`.
    have hf_comp : HasDerivAt (fun t => f (γ t)) ((fderiv ℝ f x) d) 0 :=
      hf_diff.hasFDerivAt.comp_hasDerivAt 0 hγ_deriv
    have hg_comp : ∀ a : A, HasDerivAt (fun t => g a.val (γ t)) ((fderiv ℝ (g a.val) x) d) 0 := by
      intro a
      exact (hg_diff a.val).hasFDerivAt.comp_hasDerivAt 0 hγ_deriv
    -- Slope of `f ∘ γ` tends to a negative value, so `f (γ t) < f x` for small `t > 0`.
    have hslope_f : Filter.Tendsto (fun t => ((fun t => f (γ t)) t - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 ((fderiv ℝ f x) d)) := by
      have hs := hf_comp.tendsto_slope_zero
      apply hs.mono_left
      exact nhdsWithin_le_of_mem (by simp : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ)
    have hev_f : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f (γ t) < f x := by
      have hneg : Set.Iio (0 : ℝ) ∈ 𝓝 ((fderiv ℝ f x) d) := Iio_mem_nhds hd_f
      have hev := hslope_f.eventually hneg
      filter_upwards [hev, self_mem_nhdsWithin] with t ht_slope ht_pos
      simp only [Set.mem_Iio] at ht_slope
      have ht0 : (0 : ℝ) < t := ht_pos
      have hdiv : (f (γ t) - f x) / t < 0 := by
        have : ((fun t => f (γ t)) t - f x) / t < 0 := ht_slope
        simpa [hγ_zero] using this
      have := (div_neg_iff_of_pos ht0).mp hdiv
      linarith
    -- Likewise each active `g` becomes strictly negative for small `t > 0`.
    have hev_g : ∀ a : A, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), g a.val (γ t) < 0 := by
      intro a
      have hs := (hg_comp a).tendsto_slope_zero
      have hs' : Filter.Tendsto (fun t => ((fun t => g a.val (γ t)) t - g a.val x) / t) (𝓝[>] (0 : ℝ))
          (𝓝 ((fderiv ℝ (g a.val) x) d)) := by
        apply hs.mono_left
        exact nhdsWithin_le_of_mem (by simp : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ)
      have hneg : Set.Iio (0 : ℝ) ∈ 𝓝 ((fderiv ℝ (g a.val) x) d) := Iio_mem_nhds (hd_g a)
      have hev := hs'.eventually hneg
      filter_upwards [hev, self_mem_nhdsWithin] with t ht_slope ht_pos
      simp only [Set.mem_Iio] at ht_slope
      have ht0 : (0 : ℝ) < t := ht_pos
      have ha0 : g a.val x = 0 := a.property
      have hdiv : (g a.val (γ t) - g a.val x) / t < 0 := ht_slope
      have := (div_neg_iff_of_pos ht0).mp hdiv
      linarith
    -- Inactive inequalities stay negative by continuity.
    have hev_inact : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ i : Fin m, g i x < 0 → g i (γ t) < 0 := by
      have : ∀ i : Fin m, g i x < 0 → ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g i (γ t) < 0 := by
        intro i hi
        have hcont_i : Filter.Tendsto (fun t => g i (γ t)) (𝓝 (0 : ℝ)) (𝓝 (g i x)) :=
          ((hg_diff i).continuousAt.comp hγ_cont).tendsto
        have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 (g i x) := Iio_mem_nhds hi
        exact hcont_i.eventually hmem
      exact Filter.eventually_all.mpr this
    -- Hence `γ t` is feasible for small `t > 0`.
    have hγ_mem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (∀ i, g i (γ t) ≤ 0) ∧ ∀ j, h j (γ t) = 0 := by
      have h1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ a : A, g a.val (γ t) < 0 :=
        Filter.eventually_all.mpr hev_g
      have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i : Fin m, g i x < 0 → g i (γ t) < 0 :=
        hev_inact.filter_mono nhdsWithin_le_nhds
      have h3 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (fun y j => h j y) (γ t) = 0 :=
        hγ_fiber.filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      refine ⟨?_, fun j => ?_⟩
      · intro i
        by_cases hi : g i x = 0
        · have := ht1 ⟨i, hi⟩
          exact le_of_lt this
        · have hlt : g i x < 0 := lt_of_le_of_ne (hfeas i) hi
          exact le_of_lt (ht2 i hlt)
      · have := congrFun ht3 j
        simpa using this
    -- So `γ` tends to `x` within the feasible set (from the right).
    have hγ_nhdsWithin : Filter.Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[{y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0}] x) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hγ_tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [hγ_mem] with t ht
      exact ht
    -- Composing the local min with `γ` gives a one-sided local min at `0`.
    have hmin_comp : IsMinFilter (fun t => f (γ t)) (𝓝[>] (0 : ℝ)) 0 :=
      hmin.comp_tendsto hγ_nhdsWithin hγ_zero
    -- But `f (γ t) < f (γ 0)` eventually, contradiction.
    have hcontra : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f (γ t) < (fun t => f (γ t)) 0 := by
      simpa [hγ_zero] using hev_f
    have hle : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (fun t => f (γ t)) 0 ≤ f (γ t) := hmin_comp
    obtain ⟨t, hlt, hge⟩ := (hcontra.and hle).exists
    exact absurd hge (not_le_of_gt hlt)
  -- Apply Gordan's alternative on the kernel.
  obtain hdescent | ⟨q, hq_nonneg, hq_ne, hq_sum⟩ := gordan fam
  · -- A descent direction in the kernel lifts to `E`, contradicting `hnodesc`.
    obtain ⟨z, hz⟩ := hdescent
    apply hnodesc
    refine ⟨(z : E), ?_, ?_, ?_⟩
    · intro j
      have hmem : (z : E) ∈ K := z.property
      rw [hK_def, LinearMap.mem_ker] at hmem
      -- Take the `j`-th component without rewriting `H` itself (motive safety).
      have h0 : H (z : E) = 0 := hmem
      have h1 : H (z : E) j = (0 : Fin p → ℝ) j := by rw [h0]
      rw [hH_apply] at h1
      simpa using h1
    · have h := hz none
      rw [hfam_none] at h
      exact h
    · intro a
      have h := hz (some a)
      rw [hfam_some] at h
      exact h
  · -- Nontrivial nonnegative multipliers on the kernel; extend by the equalities.
    -- Combined functional on `E` (objective plus active inequalities).
    set L0 : E →L[ℝ] ℝ := (q none) • (fderiv ℝ f x)
      + ∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x) with hL0_def
    -- `L0` vanishes on `K` by the Gordan relation.
    have hL0_vanish : ∀ z : ↥K, L0 (z : E) = 0 := by
      intro z
      have hsum := congrArg (fun L : ↥K →L[ℝ] ℝ => L z) hq_sum
      rw [sum_apply] at hsum
      have hzero : (0 : ↥K →L[ℝ] ℝ) z = 0 := rfl
      rw [hzero, Fintype.sum_option] at hsum
      simp only [smul_apply, smul_eq_mul, hfam_none, hfam_some] at hsum
      have hL0_apply : L0 (z : E)
          = q none * (fderiv ℝ f x) (z : E)
            + ∑ a : A, q (some a) * (fderiv ℝ (g a.val) x) (z : E) := by
        simp [hL0_def, add_apply, sum_apply, smul_apply, smul_eq_mul]
      rw [hL0_apply]
      exact hsum
    -- Hence `ker H ≤ ker L0`.
    have hker_le : LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ)) ≤ LinearMap.ker (L0.toLinearMap) := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hvK : v ∈ K := LinearMap.mem_ker.mpr hv
      exact hL0_vanish ⟨v, hvK⟩
    -- Rewrite `ker H` as an `iInf` of kernels for the Mathlib span lemma.
    have hker_eq : LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ))
        = ⨅ j, LinearMap.ker ((fderiv ℝ (h j) x).toLinearMap) := by
      have hcoe : (↑H : E →ₗ[ℝ] (Fin p → ℝ))
          = LinearMap.pi (fun j => ((fderiv ℝ (h j) x).toLinearMap)) := by
        ext v j
        change H v j = (LinearMap.pi (fun j => ((fderiv ℝ (h j) x).toLinearMap))) v j
        rw [hH_apply, LinearMap.pi_apply]
      rw [hcoe, LinearMap.ker_pi]
    have hiInf_le : (⨅ j, LinearMap.ker ((fderiv ℝ (h j) x).toLinearMap))
        ≤ LinearMap.ker (L0.toLinearMap) := by
      rw [← hker_eq]
      exact hker_le
    -- Mathlib: vanishing on the joint kernel puts `L0` in the span; get `mu0`.
    have hmem := mem_span_of_iInf_ker_le_ker _ _ hiInf_le
    obtain ⟨mu0, hmu0⟩ := Submodule.mem_span_range_iff_exists_fun.mp hmem
    -- Lift the linear relation to continuous linear maps.
    have hL0_eq : L0 = ∑ j, mu0 j • (fderiv ℝ (h j) x) := by
      apply ContinuousLinearMap.toLinearMap_injective
      exact hmu0
    -- Stationarity at `q none`-scale, with free equality multipliers `mu' = -mu0`.
    set mu' : Fin p → ℝ := fun j => -mu0 j with hmu'_def
    have hstat0 : ((q none) • (fderiv ℝ f x) + (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x)))
        + (∑ j, mu' j • (fderiv ℝ (h j) x)) = 0 := by
      have hL0_def' : L0 = (q none) • (fderiv ℝ f x)
          + ∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x) := rfl
      have hsum_neg : (∑ j, mu' j • (fderiv ℝ (h j) x))
          = -(∑ j, mu0 j • (fderiv ℝ (h j) x)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp [hmu'_def, neg_smul]
      rw [← hL0_def', hL0_eq, hsum_neg, add_neg_cancel]
    -- LICQ in terms of `A`.
    have hLICQ_A : LinearIndependent ℝ (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
        (fun a : A => fderiv ℝ (g a.val) x)) := hLICQ
    -- `q none ≠ 0`: else all multipliers vanish, contradicting `q ≠ 0`.
    have hq_none_ne : q none ≠ 0 := by
      intro h0
      have hrel : (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x))
          + (∑ j, mu' j • (fderiv ℝ (h j) x)) = 0 := by
        simpa [h0] using hstat0
      set c : (Fin p ⊕ A) → ℝ := Sum.elim mu' (fun a => q (some a)) with hc_def
      have hsum_eq : ∑ s : (Fin p ⊕ A), c s • (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
          (fun a : A => fderiv ℝ (g a.val) x) s) = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [hc_def, Sum.elim_inl, Sum.elim_inr]
        rw [add_comm]
        exact hrel
      have hc_zero : c = 0 := by
        have hiff := Fintype.linearIndependent_iff (R := ℝ)
          (v := Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
            (fun a : A => fderiv ℝ (g a.val) x))
        exact (hiff.mp hLICQ_A) _ hsum_eq
      have hq_some : ∀ a, q (some a) = 0 := by
        intro a
        have hcongr := congrFun hc_zero (Sum.inr a)
        simpa [hc_def] using hcongr
      have hq_eq_zero : q = 0 := by
        funext o
        cases o with
        | none => exact h0
        | some a => exact hq_some a
      exact hq_ne hq_eq_zero
    have hq_pos : 0 < q none := lt_of_le_of_ne (hq_nonneg none) (Ne.symm hq_none_ne)
    -- Normalized stationarity over the active set.
    have hstatA : fderiv ℝ f x
        + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
        + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x)) = 0 := by
      have hsmul : ((q none)⁻¹ : ℝ) • ((((q none) • (fderiv ℝ f x)
          + (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x)))
          + (∑ j, mu' j • (fderiv ℝ (h j) x)))) = 0 := by
        rw [hstat0, smul_zero]
      simp only [smul_add, Finset.smul_sum, smul_smul] at hsmul
      have hcoeff_f : ((q none)⁻¹ * q none) • (fderiv ℝ f x) = fderiv ℝ f x := by
        rw [inv_mul_cancel₀ hq_none_ne, one_smul]
      have hcoeff_g : ∀ a : A, (((q none)⁻¹ * q (some a)) • (fderiv ℝ (g a.val) x))
          = ((q (some a) / q none) • (fderiv ℝ (g a.val) x)) := by
        intro a
        rw [div_eq_mul_inv, mul_comm]
      have hcoeff_h : ∀ j, (((q none)⁻¹ * mu' j) • (fderiv ℝ (h j) x))
          = ((mu' j / q none) • (fderiv ℝ (h j) x)) := by
        intro j
        rw [div_eq_mul_inv, mul_comm]
      simp only [hcoeff_f, hcoeff_g, hcoeff_h] at hsmul
      -- `hsmul` now matches the goal up to association; close by linear combination shape
      have hassoc : ((fderiv ℝ f x + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x)))
          + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x)))
          = (fderiv ℝ f x + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
            + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x))) := rfl
      rw [← hassoc]
      exact hsmul
    -- Extend the inequality multipliers by zero to inactive constraints.
    set lam : Fin m → ℝ := fun i => if hi : g i x = 0 then (q (some ⟨i, hi⟩) / q none) else 0
      with hlam_def
    set muF : Fin p → ℝ := fun j => mu' j / q none with hmuF_def
    refine ⟨lam, muF, ?_, ?_, ?_⟩
    · -- Nonnegativity.
      intro i
      by_cases hi : g i x = 0
      · have hlam_i : lam i = q (some ⟨i, hi⟩) / q none := by simp [hlam_def, hi]
        rw [hlam_i]
        exact div_nonneg (hq_nonneg _) (le_of_lt hq_pos)
      · have hlam_i : lam i = 0 := by simp [hlam_def, hi]
        rw [hlam_i]
    · -- Complementary slackness.
      intro i
      by_cases hi : g i x = 0
      · have hlam_i : lam i = q (some ⟨i, hi⟩) / q none := by simp [hlam_def, hi]
        rw [hlam_i, hi, mul_zero]
      · have hlam_i : lam i = 0 := by simp [hlam_def, hi]
        rw [hlam_i, zero_mul]
    · -- Stationarity: the `Fin m` sum reduces to the active sum.
      have hsum_eq : (∑ i : Fin m, lam i • (fderiv ℝ (g i) x))
          = ∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x) := by
        -- First reduce `univ` to the active filter, then biject with `A`.
        set s : Finset (Fin m) := Finset.filter (fun i => g i x = 0) Finset.univ with hs_def
        have hsub : s ⊆ Finset.univ := Finset.filter_subset _ _
        have hvanish : ∀ i ∈ Finset.univ, i ∉ s → lam i • (fderiv ℝ (g i) x) = 0 := by
          intro i _ hi
          have hne : ¬ g i x = 0 := by
            intro hcon
            apply hi
            rw [hs_def, Finset.mem_filter]
            exact ⟨Finset.mem_univ i, hcon⟩
          have hlam0 : lam i = 0 := by simp [hlam_def, hne]
          rw [hlam0, zero_smul]
        have hsub_eq : (∑ i ∈ s, lam i • (fderiv ℝ (g i) x))
            = ∑ i ∈ Finset.univ, lam i • (fderiv ℝ (g i) x) :=
          Finset.sum_subset hsub hvanish
        have hbij : (∑ a ∈ Finset.univ, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
            = ∑ i ∈ s, lam i • (fderiv ℝ (g i) x) := by
          apply Finset.sum_bij (fun a _ => (a.val : Fin m))
          · -- lands in `s`
            intro a _
            rw [hs_def, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, a.property⟩
          · -- injective
            intro a₁ _ a₂ _ h12
            exact Subtype.ext h12
          · -- surjective onto `s`
            intro b hb
            rw [hs_def, Finset.mem_filter] at hb
            exact ⟨⟨b, hb.2⟩, Finset.mem_univ _, rfl⟩
          · -- values agree
            intro a _
            have hlam_a : lam a.val = q (some a) / q none := by
              have ha : g a.val x = 0 := a.property
              simp [hlam_def, ha]
              -- `⟨a.val, _⟩ = a` by proof irrelevance / Subtype eta
              congr 1
              exact Subtype.ext rfl
            rw [hlam_a]
        -- Combine: `univ Fin m = s = univ A` (as sums).
        have huniv_eq : (∑ i : Fin m, lam i • (fderiv ℝ (g i) x))
            = ∑ i ∈ s, lam i • (fderiv ℝ (g i) x) := by
          rw [← hsub_eq]
          rfl
        have hA_eq : (∑ i ∈ s, lam i • (fderiv ℝ (g i) x))
            = ∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x) := by
          rw [← hbij]
          rfl
        rw [huniv_eq, hA_eq]
      rw [hsum_eq]
      -- Goal now matches `hstatA` up to `muF` unfolding (definitional).
      simpa [hmuF_def] using hstatA

-- Test 1: concrete instance on `ℝ` with an inactive inequality.
-- `f y = y^2`, `h 0 y = y - 1`, `g 0 y = -y`, `x = 1`.
example : ∃ (lam : Fin 1 → ℝ) (mu : Fin 1 → ℝ),
    (∀ i, 0 ≤ lam i)
    ∧ (∀ i, lam i * ((fun _ y : ℝ => -y) i) 1 = 0)
    ∧ (fderiv ℝ (fun y : ℝ => y ^ 2) 1
      + ∑ i : Fin 1, lam i • fderiv ℝ ((fun _ y : ℝ => -y) i) 1
      + ∑ j : Fin 1, mu j • fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1 = 0)
    ∧ lam 0 = 0 ∧ mu 0 = -2 := by
  have hf_diff : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) 1 := by fun_prop
  have hg_diff : ∀ i : Fin 1, DifferentiableAt ℝ ((fun _ y : ℝ => -y) i) 1 := by
    intro i
    fun_prop
  have hh_diff : ∀ j : Fin 1, ContDiffAt ℝ 1 ((fun _ y : ℝ => y - 1) j) 1 := by
    intro j
    fun_prop
  have hfeas : ∀ i : Fin 1, (fun _ y : ℝ => -y) i 1 ≤ 0 := by
    intro i
    change (-1 : ℝ) ≤ 0
    norm_num
  have heq : ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j 1 = 0 := by
    intro j
    change (1 : ℝ) - 1 = 0
    norm_num
  have hmin : IsLocalMinOn (fun y : ℝ => y ^ 2)
      {y | (∀ i : Fin 1, (fun _ y : ℝ => -y) i y ≤ 0)
        ∧ ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j y = 0} 1 := by
    change ∀ᶠ y : ℝ in 𝓝[{y | (∀ i : Fin 1, (fun _ y : ℝ => -y) i y ≤ 0)
        ∧ ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j y = 0}] 1,
      (fun y : ℝ => y ^ 2) 1 ≤ (fun y : ℝ => y ^ 2) y
    filter_upwards [self_of_nhdsWithin] with y hy
    obtain ⟨hg, hh⟩ := hy
    have h0 := hh 0
    simp only [] at h0
    have hy1 : y = 1 := by linarith
    rw [hy1]
    exact le_rfl _
  have hLICQ : LinearIndependent ℝ (Sum.elim
      (fun j : Fin 1 => fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1)
      (fun i : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0} =>
        fderiv ℝ ((fun _ y : ℝ => -y) i.val) 1)) := by
    -- The active set is empty.
    have hempty : ∀ a : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0}, False := by
      intro a
      have hprop : (fun _ y : ℝ => -y) a.val (1 : ℝ) = 0 := a.property
      norm_num at hprop
    -- The single equality derivative is `id`, hence nonzero.
    have hderiv : HasFDerivAt (fun y : ℝ => y - 1) (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
      HasFDerivAt.id.sub_const 1
    have hfderiv_id : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1
        = ContinuousLinearMap.id ℝ ℝ := hderiv.fderiv
    have hne : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1 ≠ 0 := by
      rw [hfderiv_id]
      intro hcon
      have hcon1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcon
      simp at hcon1
    -- Independence by direct sum analysis.
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    have hA0 : (∑ a : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0},
        c (Sum.inr a) • fderiv ℝ ((fun _ y : ℝ => -y) a.val) 1) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact (hempty a).elim
    rw [hA0, add_zero] at hc
    -- `hc` is now a singleton sum over `Fin 1`.
    rw [Fin.sum_univ_one] at hc
    -- From `c (inl 0) • id = 0`, get `c (inl 0) = 0`.
    have hfd0 : (Sum.elim (fun j : Fin 1 => fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1)
        (fun i : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0} =>
          fderiv ℝ ((fun _ y : ℝ => -y) i.val) 1)) (Sum.inl 0)
        = ContinuousLinearMap.id ℝ ℝ := by
      simp only [Sum.elim_inl]
      exact hfderiv_id
    rw [hfd0] at hc
    have hc0 : c (Sum.inl 0) = 0 := by
      have hc1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hc
      simp at hc1
      linarith [hc1]
    funext s
    cases s with
    | inl j =>
      have hj0 : j = 0 := by fin_cases j; rfl
      subst hj0
      simp [hc0]
    | inr a => exact (hempty a).elim
  obtain ⟨lam, mu, hlam, hcompl, hstat⟩ := karush_kuhn_tucker_mixed
    hf_diff hg_diff hh_diff hfeas heq hmin hLICQ
  have hlam0 : lam 0 = 0 := by
    have hc := hcompl 0
    simp only [] at hc
    -- `hc : lam 0 * -1 = 0`
    linarith
  have hmu0 : mu 0 = -2 := by
    have hstat1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L (1 : ℝ)) hstat
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply, Fin.sum_univ_one] at hstat1
    have hf1 : (fderiv ℝ (fun y : ℝ => y ^ 2) 1) 1 = 2 := by
      have hfun : (fun y : ℝ => y ^ 2) = (fun y => y * y) := by
        funext y
        exact pow_two y
      rw [hfun]
      have hmul := (HasFDerivAt.id (1 : ℝ)).mul (HasFDerivAt.id (1 : ℝ))
      have hfd : fderiv ℝ (fun y : ℝ => y * y) 1
          = (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ :=
        hmul.fderiv
      rw [hfd]
      simp [add_apply, smul_apply, smul_eq_mul]
    have hg1 : (fderiv ℝ ((fun _ y : ℝ => -y) 0) 1) 1 = -1 := by
      have hneg : HasFDerivAt (fun y : ℝ => -y) (-ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
        (HasFDerivAt.id (1 : ℝ)).neg
      have hfd : fderiv ℝ ((fun _ y : ℝ => -y) 0) 1 = -ContinuousLinearMap.id ℝ ℝ := hneg.fderiv
      rw [hfd]
      simp
    have hh1 : (fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1) 1 = 1 := by
      have hsub : HasFDerivAt (fun y : ℝ => y - 1) (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
        HasFDerivAt.id.sub_const 1
      have hfd : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1 = ContinuousLinearMap.id ℝ ℝ := hsub.fderiv
      rw [hfd]
      simp
    rw [hf1, hg1, hh1, hlam0] at hstat1
    simp at hstat1
    linarith
  exact ⟨lam, mu, hlam, hcompl, hstat, hlam0, hmu0⟩

-- Test 2: without LICQ the KKT conclusion can fail (constraint qualification probe).
-- Minimize `f y = y` subject to `g 0 y = y^2 ≤ 0` (no equalities).
-- `0` is the unique feasible point, hence a local min, but no `lam ≥ 0` gives stationarity.
example : IsLocalMinOn (fun y : ℝ => y)
      {y | (∀ i : Fin 1, (fun _ y : ℝ => y ^ 2) i y ≤ 0)
        ∧ ∀ j : Fin 0, (fun (_ : Fin 0) (_ : ℝ) => (0 : ℝ)) j y = 0} (0 : ℝ)
    ∧ ¬∃ lam : Fin 1 → ℝ, (∀ i, 0 ≤ lam i)
      ∧ (fderiv ℝ (fun y : ℝ => y) 0
        + lam 0 • fderiv ℝ ((fun _ y : ℝ => y ^ 2) 0) 0 = 0) := by
  constructor
  · -- `0` is the only feasible point, hence a (global, so local) minimum.
    change ∀ᶠ y : ℝ in 𝓝[{y | (∀ i : Fin 1, (fun _ y : ℝ => y ^ 2) i y ≤ 0)
        ∧ ∀ j : Fin 0, (fun (_ : Fin 0) (_ : ℝ) => (0 : ℝ)) j y = 0}] 0,
      (fun y : ℝ => y) 0 ≤ (fun y : ℝ => y) y
    filter_upwards [self_of_nhdsWithin] with y hy
    obtain ⟨hg, -⟩ := hy
    have h0 := hg 0
    simp only [] at h0
    have hsq : (0 : ℝ) ≤ y ^ 2 := by positivity
    have heq : y ^ 2 = 0 := le_antisymm h0 hsq
    have hy0 : y = 0 := sq_eq_zero_iff.mp heq
    rw [hy0]
    exact le_rfl _
  · -- No multipliers exist: `fderiv` of `y` is `id ≠ 0`, of `y^2` at `0` is `0`.
    rintro ⟨lam, -, hstat⟩
    have hid : fderiv ℝ (fun y : ℝ => y) 0 = ContinuousLinearMap.id ℝ ℝ :=
      (HasFDerivAt.id (0 : ℝ)).fderiv
    have hzero : fderiv ℝ ((fun _ y : ℝ => y ^ 2) 0) 0 = 0 := by
      have hfun : ((fun _ y : ℝ => y ^ 2) 0) = (fun y => y * y) := by
        funext y
        exact pow_two y
      rw [hfun]
      have hmul := (HasFDerivAt.id (0 : ℝ)).mul (HasFDerivAt.id (0 : ℝ))
      have hfd := hmul.fderiv
      simp at hfd
      exact hfd
    rw [hid, hzero, smul_zero, add_zero] at hstat
    have hcon1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hstat
    simp at hcon1

#print axioms karush_kuhn_tucker_mixed

end MathlibExt.Analysis.Convex.KarushKuhnTucker
