/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open scoped ComplexInnerProductSpace

namespace HilbertSpace

/-- A Hilbert space is a complex inner product space that is complete with respect to the norm
induced by the inner product. This is Definition 5.1 of Melrose, packaged as a type class
combining `InnerProductSpace ℂ V` with `CompleteSpace V`. -/
class IsHilbertSpace (V : Type*) [NormedAddCommGroup V] extends
    InnerProductSpace ℂ V, CompleteSpace V

variable {V : Type*} [NormedAddCommGroup V] [IsHilbertSpace V]

/-- Existence part of the closest point theorem (Lemma 5.2 of Melrose): every nonempty closed
convex subset of a Hilbert space contains an element of minimal norm, attaining the infimum
`⨅ w : C, ‖w‖`. -/
theorem exists_smallest_norm_of_closed_convex {C : Set V} (hne : C.Nonempty)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) :
    ∃ v ∈ C, ‖v‖ = ⨅ w : C, ‖(w : V)‖ := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  haveI : Nonempty ↥C := hne.to_subtype
  have hcomplete : IsComplete C := hclosed.isComplete
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex 0
  refine ⟨v, hv, ?_⟩
  simp only [zero_sub, norm_neg] at hmin
  exact hmin

/-- Uniqueness part of the closest point theorem (Lemma 5.2 of Melrose): two elements of a
closed convex subset of a Hilbert space that both attain the minimum norm must coincide. The
proof uses the parallelogram law applied to their midpoint, which also lies in the set. -/
theorem unique_smallest_norm_of_closed_convex {C : Set V} (hne : C.Nonempty)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) {v v' : V}
    (hv : v ∈ C) (hv' : v' ∈ C)
    (hmin_v : ‖v‖ = ⨅ w : C, ‖(w : V)‖)
    (hmin_v' : ‖v'‖ = ⨅ w : C, ‖(w : V)‖) :
    v = v' := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  haveI : Nonempty ↥C := hne.to_subtype

  have para := parallelogram_law_with_norm (𝕜 := ℝ) v v'

  set δ := ⨅ w : C, ‖(w : V)‖ with hδ_def
  have hδ_nn : 0 ≤ δ := le_ciInf fun ⟨w, _⟩ => norm_nonneg w

  rw [hmin_v, hmin_v'] at para

  have hmid : (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v' ∈ C := by
    have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
    exact hconvex hv hv' (by positivity) (by positivity) h2

  have hmid_norm : δ ≤ ‖(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v'‖ := by
    have hbdd : BddBelow (Set.range fun (w : ↥C) => ‖(w : V)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
    exact ciInf_le hbdd ⟨(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v', hmid⟩

  have hmid_eq : ‖(2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • v'‖ = ‖v + v'‖ / 2 := by
    rw [← smul_add, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    ring

  have key : ‖v - v'‖ ^ 2 ≤ 0 := by
    have h1 : ‖v + v'‖ ^ 2 + ‖v - v'‖ ^ 2 = 2 * (δ ^ 2 + δ ^ 2) := para
    have h2 : δ ≤ ‖v + v'‖ / 2 := by linarith [hmid_norm, hmid_eq]
    have h3 : 4 * δ ^ 2 ≤ ‖v + v'‖ ^ 2 := by nlinarith
    linarith

  have : ‖v - v'‖ = 0 := by nlinarith [sq_nonneg ‖v - v'‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Existence and uniqueness of the minimum-norm point in a nonempty closed convex subset of a
Hilbert space (Lemma 5.2 of Melrose), packaged as an `∃!` statement combining
`exists_smallest_norm_of_closed_convex` and `unique_smallest_norm_of_closed_convex`. -/
theorem exists_unique_smallest_norm_of_closed_convex {C : Set V}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) :
    ∃! v ∈ C, ‖v‖ = ⨅ w : C, ‖(w : V)‖ := by
  obtain ⟨v, hv, hmin⟩ := exists_smallest_norm_of_closed_convex hne hclosed hconvex
  refine ⟨v, ⟨hv, hmin⟩, ?_⟩
  intro v' ⟨hv', hmin'⟩
  exact unique_smallest_norm_of_closed_convex hne hclosed hconvex hv' hv hmin' hmin

/-- Riesz representation theorem (Proposition 5.3 of Melrose): every continuous linear functional
`L : V →L[ℂ] ℂ` on a Hilbert space is represented by a unique vector `v` via
`L u = ⟪v, u⟫`. -/
theorem riesz_representation (L : V →L[ℂ] ℂ) :
    ∃! v : V, ∀ u : V, L u = ⟪v, u⟫ := by
  refine ⟨(InnerProductSpace.toDual ℂ V).symm L, ?_, ?_⟩
  · intro u
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm
  · intro v' hv'
    have hv_repr : ∀ u, L u = ⟪(InnerProductSpace.toDual ℂ V).symm L, u⟫ :=
      fun u => (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm
    have : ∀ u, ⟪v', u⟫ = ⟪(InnerProductSpace.toDual ℂ V).symm L, u⟫ :=
      fun u => by rw [← hv', ← hv_repr]
    exact ext_inner_right ℂ this

end HilbertSpace

namespace HilbertSpace

open MeasureTheory Complex
open scoped ComplexConjugate ComplexInnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Concrete Riesz representation for the dual of `L²(μ; ℂ)`: every continuous linear functional
on `L²` is given by integration against (the conjugate of) some `L²` function `g`. This is the
specialisation of Proposition 5.3 to the Hilbert space `L²(α, μ; ℂ)`. -/
theorem l2_dual_eq_integral
    (L : (α →₂[μ] ℂ) →L[ℂ] ℂ) :
    ∃ g : α →₂[μ] ℂ,
      ∀ f : α →₂[μ] ℂ,
        L f = ∫ a, f a * starRingEnd ℂ (g a) ∂μ := by

  obtain ⟨g, rfl⟩ := (InnerProductSpace.toDual ℂ (α →₂[μ] ℂ)).surjective L
  refine ⟨g, fun f => ?_⟩

  simp only [InnerProductSpace.toDual_apply_apply]
  rw [L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun a => RCLike.inner_apply _ _)

end HilbertSpace

end
