/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Module.Basic

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The pairing $x \mapsto \sum_s \alpha_s\, x_s$ is continuous in $x$, as a finite
sum of continuous functions. -/
lemma continuous_pairing (α : B → ℝ) :
    Continuous (fun x : B → ℝ => pairing α x) := by
  unfold pairing
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul (continuous_apply s)

/-- The open half-space $\{x : \langle \alpha, x\rangle > 0\}$ is open in $B \to \mathbb R$. -/
lemma isOpen_pairing_pos (α : B → ℝ) :
    IsOpen {x : B → ℝ | pairing α x > 0} :=
  isOpen_lt continuous_const (continuous_pairing α)

/-- A radical vector $v_0$ (one satisfying $\sum_u v_0(u)\,B(e_u, e_t) = 0$ for all
$t$) is fixed by every simple reflection $\sigma_s$ acting on the root space. -/
lemma sigma_fixes_radical
    (M : CoxeterMatrix B)
    (v₀ : B → ℝ) (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (s : B) :
    CoxeterGroup.sigma M s v₀ = v₀ := by
  ext t
  simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hv₀_rad s]
  simp

/-- A radical vector is fixed by the iterated reflection action $\sigma_{ws}$
for any word $ws$, by induction on the length of $ws$. -/
lemma sigmaWord_fixes_radical
    (M : CoxeterMatrix B)
    (v₀ : B → ℝ) (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (ws : List B) :
    sigmaWord M ws v₀ = v₀ := by
  induction ws with
  | nil => simp [sigmaWord]
  | cons s ws' ih =>
    simp only [sigmaWord, List.foldl_cons]
    rw [sigma_fixes_radical M v₀ hv₀_rad s]
    exact ih

/-- Pairing-invariance: the pairing with a radical vector $v_0$ is invariant
under the dual word action, since $\sigma$ and its dual are mutually transpose. -/
lemma dualSigmaWord_preserves_radical_pairing
    (M : CoxeterMatrix B) [Nonempty B] [RootSystemData M]
    (v₀ : B → ℝ) (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (ws : List B) (x : B → ℝ) :
    pairing v₀ (dualSigmaWord M ws x) = pairing v₀ x := by
  rw [RootSystemData.pairing_word_comm]
  congr 1
  exact sigmaWord_fixes_radical M v₀ hv₀_rad ws.reverse

/-- Forward direction: a nonzero point of the Tits cone has strictly positive
pairing with any strictly-positive radical vector $v_0$. -/
lemma titsCone_sdiff_zero_radical_pairing_pos
    (M : CoxeterMatrix B) [Nonempty B] [RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hx : x ∈ titsConeSet M) (hx_ne : x ≠ 0) :
    pairing v₀ x > 0 := by
  obtain ⟨y, hy_nn, ws, hx_eq⟩ := hx
  subst hx_eq
  change pairing v₀ (dualSigmaWord M ws y) > 0
  rw [dualSigmaWord_preserves_radical_pairing M v₀ hv₀_rad ws y]
  have hy_ne : y ≠ 0 := by
    intro h; apply hx_ne; subst h
    exact wordAction_zero M ws
  have ⟨s, hs⟩ : ∃ s, y s > 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hy_ne; ext s; simp only [Pi.zero_apply]
    have h1 := hy_nn s; have h2 := h s; linarith
  unfold pairing
  apply Finset.sum_pos'
  · intro i _; exact mul_nonneg (le_of_lt (hv₀_pos i)) (hy_nn i)
  · exact ⟨s, Finset.mem_univ s, mul_pos (hv₀_pos s) hs⟩

/-- The set of nonpositive roots at $x$ is invariant under positive scaling of
$x$, since the sign of $\langle \alpha, x\rangle$ is preserved. -/
lemma nonposRoots_pos_scale
    (Φ : Set (B → ℝ)) (x : B → ℝ) (c : ℝ) (hc : c > 0) :
    nonposRoots Φ (fun s => c * x s) = nonposRoots Φ x := by
  ext α
  simp only [nonposRoots, Set.mem_sep_iff, pairing]
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [hsum] at h
    by_contra h'; simp only [not_le] at h'; linarith [mul_pos hc h']
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    have hsum : (∑ s : B, α s * (c * x s)) = c * (∑ s : B, α s * x s) := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [hsum]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) h

/-- Reverse direction: if $\langle v_0, x\rangle > 0$ then the nonpositive-roots
set at $x$ is finite; we rescale to the hyperplane $\langle v_0, x'\rangle = 1$
and apply finiteness on that hyperplane. -/
lemma nuFiniteAt_of_radical_pairing_pos
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hpair : pairing v₀ x > 0) :
    nuFiniteAt inst.Φpos x := by
  set c := (pairing v₀ x)⁻¹ with hc_def
  have hc_pos : c > 0 := inv_pos_of_pos hpair
  set x' := fun s => c * x s with hx'_def
  have hpair' : ∑ s, v₀ s * x' s = 1 := by
    simp only [hx'_def]
    have : ∑ s : B, v₀ s * (c * x s) = c * ∑ s : B, v₀ s * x s := by
      rw [Finset.mul_sum]; congr 1; ext s; ring
    rw [this]
    exact inv_mul_cancel₀ (ne_of_gt hpair)
  have hfin : Set.Finite (nonposRoots inst.Φpos x') :=
    inst.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x' hpair'
  rw [show x' = fun s => c * x s from rfl, nonposRoots_pos_scale _ x c hc_pos] at hfin
  exact hfin

/-- Main characterisation: the Tits cone minus the origin equals the open
half-space $\{x : \langle v_0, x\rangle > 0\}$ cut out by any strictly positive
radical vector $v_0$ — this is the Perron–Frobenius corollary in the affine
Coxeter setting. -/
theorem titsCone_sdiff_zero_eq_radical_pos
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
    titsConeSet M \ {0} = {x : B → ℝ | pairing v₀ x > 0} := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hne⟩
    exact titsCone_sdiff_zero_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hx hne
  · intro hpair
    have hne : x ≠ 0 := by
      intro h; rw [h] at hpair; simp [pairing] at hpair
    refine ⟨?_, hne⟩
    have hnu := nuFiniteAt_of_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hpair
    rw [titsCone_eq_zero_union_nuFinite (M := M)]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    right; exact hnu

/-- A nonzero point of the Tits cone has finitely many positive roots on which
it is nonpositive — the nu-finiteness consequence of the previous theorem. -/
lemma nuFiniteAt_of_mem_titsCone_sdiff_zero
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hx : x ∈ titsConeSet M \ {0}) :
    nuFiniteAt inst.Φpos x := by
  have hpair : pairing v₀ x > 0 := by
    have hmem : x ∈ {y : B → ℝ | pairing v₀ y > 0} :=
      (titsCone_sdiff_zero_eq_radical_pos M v₀ hv₀_pos hv₀_rad) ▸ hx
    exact hmem
  exact nuFiniteAt_of_radical_pairing_pos M v₀ hv₀_pos hv₀_rad x hpair

/-- At a nonzero point $x$ of the Tits cone, only finitely many positive roots
$\alpha$ satisfy $\langle \alpha, x\rangle = 0$ (a subset of the nu-finite set). -/
lemma zeroRoots_finite
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hx : x ∈ titsConeSet M \ {0}) :
    Set.Finite {α ∈ inst.Φpos | pairing α x = 0} := by
  apply Set.Finite.subset (nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad x hx)
  intro α ⟨hα, hpair⟩
  exact ⟨hα, le_of_eq hpair⟩

/-- Pointwise local finiteness of the root-hyperplane arrangement: at any
nonzero point of the Tits cone, only finitely many root hyperplanes
$\{\langle \alpha, y\rangle = 0\}$ pass through it. -/
theorem locallyFinite_hyperplanes_pointwise
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (x : B → ℝ) (hx : x ∈ titsConeSet M \ {0}) :
    Set.Finite {η : Set (B → ℝ) |
      (∃ α ∈ inst.Φpos, η = {y : B → ℝ | pairing α y = 0}) ∧
      x ∈ η} := by
  apply Set.Finite.subset
    ((zeroRoots_finite M v₀ hv₀_pos hv₀_rad x hx).image
      (fun α => {y : B → ℝ | pairing α y = 0}))
  intro η ⟨⟨α, hα_mem, hη_eq⟩, hx_in⟩
  rw [Set.mem_image]
  refine ⟨α, ?_, hη_eq.symm⟩
  simp only [Set.mem_sep_iff]
  exact ⟨hα_mem, by rw [hη_eq] at hx_in; exact hx_in⟩

end TitsCone
