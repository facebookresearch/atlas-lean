/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AdvancedKahler
import Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Atlas.GeometryOfManifolds.code.HodgeTheory
import Mathlib.Geometry.Manifold.MFDeriv.Basic


set_option autoImplicit false

open DifferentialFormSpace


/-- A tangent-bundle splitting compatible with a 2-form $\eta$.

Encodes a decomposition $TM = V \oplus H$ into vertical and horizontal subbundles via
projections `projV` and `projH`. Contraction with $\eta$ (and with any $(p+1)$-form)
distributes over the splitting, the projections are idempotent and mutually
annihilating, and the splitting is "orthogonal" with respect to $\eta$ in the sense
that $\iota_{V Y} \iota_{H X} \eta = 0$. -/
class TangentSplitting
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η : Ω 2) where
  projV : VF → VF
  projH : VF → VF
  decompose : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι X α = inst.ι (projV X) α + inst.ι (projH X) α
  projV_idem : ∀ (X : VF), projV (projV X) = projV X
  projH_idem : ∀ (X : VF), projH (projH X) = projH X
  complement_VH : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projV (projH X)) α = 0
  complement_HV : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (projH (projV X)) α = 0
  orthogonal : ∀ (X Y : VF),
    inst.ι (projV Y) (inst.ι (projH X) η) = 0


/-- A **symplectic fibration** $f: M \to B$ with generic fiber $(F, \omega_F)$ symplectic.

Bundles together the projection `f`, the fiber inclusion, the symplectic form on the
fiber, and an open cover with local trivializations whose transition maps preserve
$\omega_F$. The cocycle and inverse axioms ensure the data really comes from a
fiber-bundle structure with structure group $\mathrm{Symp}(F,\omega_F)$. -/
structure SymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F] where
  f : DFSMorphism Ω_M VF_M Ω_B VF_B
  fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M
  fiberSymplectic : SymplecticManifold Ω_F VF_F
  CoverIdx : Type
  coverNonempty : Nonempty CoverIdx
  localTriv : CoverIdx → DFSMorphism Ω_F VF_F Ω_M VF_M
  localTriv_symplectic : ∀ (i : CoverIdx) (η : Ω_M 2),
    fiberInclusion.pullback η = fiberSymplectic.ω →
    (localTriv i).pullback η = fiberSymplectic.ω
  transitionMap : CoverIdx → CoverIdx → DFSMorphism Ω_F VF_F Ω_F VF_F
  transition_from_localTriv : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_M p),
    (localTriv i).pullback α =
    (transitionMap i j).pullback ((localTriv j).pullback α)
  transition_preserves_symplectic : ∀ (i j : CoverIdx),
    (transitionMap i j).pullback fiberSymplectic.ω = fiberSymplectic.ω
  transition_inverse : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i j).pullback ((transitionMap j i).pullback α) = α
  transition_cocycle : ∀ (i j k : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap j k).pullback ((transitionMap i j).pullback α) =
    (transitionMap i k).pullback α
  transition_diagonal : ∀ (i : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i i).pullback α = α
  fiber_pullback_base_zero_general :
    ∀ {p : ℕ} (α : Ω_B (p + 1)),
    fiberInclusion.pullback (f.pullback α) = 0
  fiberInclusion_eq_localTriv :
    ∃ (i : CoverIdx), ∀ {p : ℕ} (α : Ω_M p),
      fiberInclusion.pullback α = (localTriv i).pullback α
  localTriv_surjective : ∀ (i : CoverIdx) {p : ℕ} (β : Ω_F p),
    ∃ (γ : Ω_M p), (localTriv i).pullback γ = β


/-- Tangent-bundle data for a symplectic fibration adapted to a closed 2-form $\tilde\eta$
that restricts to the fiber symplectic form $\omega_F$.

Packages a `TangentSplitting` for $\tilde\eta$ together with a vertical restriction
map $VF_M \to VF_F$, with axioms saying the vertical part kills base-pulled forms,
restriction is compatible with contraction by $\tilde\eta$, the restriction is
injective on verticals, and a non-degeneracy criterion in the horizontal direction
detected by the base symplectic form. -/
structure FibrationTangentBundle
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (η_tilde : Ω_M 2)
    (h_closed : inst_M.d η_tilde = 0)
    (h_fiber : fib.fiberInclusion.pullback η_tilde = fib.fiberSymplectic.ω) where
  splitting : @TangentSplitting _ _ inst_M η_tilde
  restrictV : VF_M → VF_F
  vertical_kills_base : ∀ (X : VF_M) {p : ℕ} (β : Ω_B (p + 1)),
    inst_M.ι (splitting.projV X) (fib.f.pullback β) = 0
  restrictV_compat : ∀ (X : VF_M),
    fib.fiberInclusion.pullback (inst_M.ι (splitting.projV X) η_tilde) =
    inst_F.ι (restrictV (splitting.projV X)) (fib.fiberInclusion.pullback η_tilde)
  restrictV_inj : ∀ (X Y : VF_M),
    restrictV (splitting.projV X) = restrictV (splitting.projV Y) →
    splitting.projV X = splitting.projV Y
  horizontal_nondegen : ∀ (baseSymplectic : SymplecticManifold Ω_B VF_B) (X Y : VF_M),
    splitting.projV X = splitting.projV Y →
    inst_M.ι X (fib.f.pullback baseSymplectic.ω) =
    inst_M.ι Y (fib.f.pullback baseSymplectic.ω) → X = Y
















/-- Pulling back the base symplectic form to $M$ and then restricting to a fiber gives
zero: $i_F^* f^* \omega_B = 0$, since $f$ is constant on each fiber. -/
theorem SymplecticFibration.fiber_pullback_base_zero
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (ωB_data : SymplecticManifold Ω_B VF_B) :
    fib.fiberInclusion.pullback (fib.f.pullback ωB_data.ω) = 0 :=
  fib.fiber_pullback_base_zero_general ωB_data.ω

/-- The fiber-inclusion pullback is surjective: every form $\beta$ on the fiber arises
as $i_F^* \gamma$ for some form $\gamma$ on $M$. Follows from the existence of a
local trivialization whose pullback agrees with $i_F^*$. -/
theorem SymplecticFibration.fiberInclusion_surjective
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    {p : ℕ} (β : Ω_F p) :
    ∃ (γ : Ω_M p), fib.fiberInclusion.pullback γ = β := by

  obtain ⟨i, hi⟩ := fib.fiberInclusion_eq_localTriv

  obtain ⟨γ, hγ⟩ := fib.localTriv_surjective i β

  exact ⟨γ, by rw [hi, hγ]⟩


/-- **Global correction step in Thurston's theorem.**

Given a closed 2-form $\eta$ on $M$ whose restriction to the fiber is cohomologous to
$\omega_F$ (i.e. $i_F^*\eta = \omega_F + d\beta$), one can find a 1-form
`correction` on $M$ such that $\eta + d(\text{correction})$ restricts exactly to
$\omega_F$ on each fiber. -/
theorem thurston_global_correction
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsCompactManifold Ω_M VF_M]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω_M 2)
    (η_closed : inst_M.d η = 0)
    (η_cohomological : ∃ (β : Ω_F 1),
      fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω + inst_F.d β) :
    ∃ (correction : Ω_M 1),
      fib.fiberInclusion.pullback (η + inst_M.d correction) = fib.fiberSymplectic.ω := by


  obtain ⟨β, hβ⟩ := η_cohomological


  obtain ⟨γ, hγ⟩ := fib.fiberInclusion_surjective (-β : Ω_F 1)

  exact ⟨γ, by

    rw [fib.fiberInclusion.pullback_add, fib.fiberInclusion.pullback_comm_d, hγ, hβ]

    have hd_neg : inst_F.d (-β) = -(inst_F.d β) := by
      have h := inst_F.d_smul (-1 : ℝ) β
      simp only [neg_one_smul] at h
      exact h
    rw [hd_neg]
    abel⟩


/-- Auxiliary class bundling the data needed for Thurston's construction:
a tangent splitting compatible with $\eta$, vanishing of the base pullback on
vertical vectors, vertical non-degeneracy of $\eta$, and (for sufficiently large $k$)
non-degeneracy of $\eta + k\, f^*\omega_B$. -/
class ThurstonSplittingData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_B : ℕ → Type*} {VF_B : Type*} [inst_B : DifferentialFormSpace Ω_B VF_B]
    {Ω_F : ℕ → Type*} {VF_F : Type*} [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst) (inst_B := inst_B) (inst_F := inst_F))
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω 2)
    (h_η_restricts : fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω)
    extends TangentSplitting (inst := inst) η where
  pullback_vanishes : ∀ (X : VF),
    inst.ι (projV X) (fib.f.pullback baseSymplectic.ω) = 0
  eta_nondegen_vertical : ∀ (X Y : VF),
    inst.ι (projV X) η = inst.ι (projV Y) η → projV X = projV Y
  horiz_nondegen : ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
    ∀ (X Y : VF), projV X = projV Y →
      inst.ι X (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) =
      inst.ι Y (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) → X = Y


/-- Vertical vectors annihilate $f^*\omega_B$, given the general kernel property of the
splitting. Simple specialization to the base symplectic form. -/
theorem pullback_vanishes_on_verticals
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    (f_map : DFSMorphism Ω_M VF_M Ω_B VF_B)
    (ωB : Ω_B 2)
    (projV : VF_M → VF_M)

    (hV_ker : ∀ (X : VF_M) {p : ℕ} (β : Ω_B (p + 1)),
      inst_M.ι (projV X) (f_map.pullback β) = 0) :
    ∀ (X : VF_M), inst_M.ι (projV X) (f_map.pullback ωB) = 0 :=
  fun X => hV_ker X ωB

/-- $\eta$ is non-degenerate on vertical vectors. If $\iota_{\mathrm{projV}\,X}\eta =
\iota_{\mathrm{projV}\,Y}\eta$, then $\mathrm{projV}\,X = \mathrm{projV}\,Y$.

The argument transfers the equation to the fiber via the pullback, uses the
non-degeneracy of $\omega_F$, and injectivity of the vertical restriction map. -/
theorem eta_nondegen_on_verticals
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M)
    (fiberSymplectic : SymplecticManifold Ω_F VF_F)
    (η : Ω_M 2)
    (h_fiber : fiberInclusion.pullback η = fiberSymplectic.ω)
    (projV : VF_M → VF_M)


    (restrictV : VF_M → VF_F)
    (h_compat : ∀ X : VF_M,
      fiberInclusion.pullback (inst_M.ι (projV X) η) =
      inst_F.ι (restrictV (projV X)) (fiberInclusion.pullback η))


    (h_restrictV_inj : ∀ X Y : VF_M,
      restrictV (projV X) = restrictV (projV Y) → projV X = projV Y) :
    ∀ (X Y : VF_M), inst_M.ι (projV X) η = inst_M.ι (projV Y) η → projV X = projV Y := by
  intro X Y h_eq

  have h_pb_eq : fiberInclusion.pullback (inst_M.ι (projV X) η) =
                 fiberInclusion.pullback (inst_M.ι (projV Y) η) :=
    congrArg fiberInclusion.pullback h_eq

  rw [h_compat X, h_compat Y] at h_pb_eq

  rw [h_fiber] at h_pb_eq

  have h_restrict_eq : restrictV (projV X) = restrictV (projV Y) :=
    fiberSymplectic.nondegenerate h_pb_eq

  exact h_restrictV_inj X Y h_restrict_eq

/-- For all sufficiently large $k$, the perturbed form $\eta + k\, f^*\omega_B$ is
non-degenerate on the horizontal directions of the splitting.

Recasts the rescaling identity $\eta + k\,f^*\omega_B = k(f^*\omega_B + k^{-1}\eta)$
and applies the open-condition stability hypothesis. -/
theorem horizontal_nondegen_for_large_k
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [IsCompactManifold Ω_M VF_M]
    (f_map : DFSMorphism Ω_M VF_M Ω_B VF_B)
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω_M 2)
    (projV : VF_M → VF_M)


    (hdf_nondegen_H : ∀ (X Y : VF_M), projV X = projV Y →
      inst_M.ι X (f_map.pullback baseSymplectic.ω) =
      inst_M.ι Y (f_map.pullback baseSymplectic.ω) → X = Y)


    (h_perturb_stable : ∀ (ω₀ : Ω_M 2),
      (∀ (X Y : VF_M), projV X = projV Y →
        inst_M.ι X ω₀ = inst_M.ι Y ω₀ → X = Y) →
      ∃ (k₀ : ℕ), 1 ≤ k₀ ∧ ∀ (k : ℕ), k₀ ≤ k →
        ∀ (X Y : VF_M), projV X = projV Y →
          inst_M.ι X (ω₀ + ((k : ℝ)⁻¹) • η) =
          inst_M.ι Y (ω₀ + ((k : ℝ)⁻¹) • η) → X = Y) :
    ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
      ∀ (X Y : VF_M), projV X = projV Y →
        inst_M.ι X (η + (k : ℝ) • f_map.pullback baseSymplectic.ω) =
        inst_M.ι Y (η + (k : ℝ) • f_map.pullback baseSymplectic.ω) → X = Y := by

  obtain ⟨k₀, hk₀_pos, hk₀⟩ := h_perturb_stable (f_map.pullback baseSymplectic.ω) hdf_nondegen_H

  refine ⟨k₀, fun k hk X Y hprojV hι => ?_⟩


  have hk_ge_one : 1 ≤ k := le_trans hk₀_pos hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hk_ge_one |>.bot_lt)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos

  have hform_eq : η + (k : ℝ) • f_map.pullback baseSymplectic.ω =
      (k : ℝ) • (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hk_ne, one_smul, add_comm]

  rw [hform_eq] at hι

  rw [inst_M.ι_smul X (k : ℝ), inst_M.ι_smul Y (k : ℝ)] at hι

  have hι_inner : inst_M.ι X (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) =
      inst_M.ι Y (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) := by
    exact (IsUnit.mk0 (k : ℝ) hk_ne).smul_left_cancel.mp hι

  exact hk₀ k hk X Y hprojV hι_inner


/-- Re-export of the vertical non-degeneracy axiom of `ThurstonSplittingData`. -/
theorem eta_nondegenerate_on_vertical
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_B : ℕ → Type*} {VF_B : Type*} [inst_B : DifferentialFormSpace Ω_B VF_B]
    {Ω_F : ℕ → Type*} {VF_F : Type*} [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst) (inst_B := inst_B) (inst_F := inst_F))
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω 2)
    (h_η_restricts : fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω)
    (tsd : ThurstonSplittingData fib baseSymplectic η h_η_restricts)
    (X Y : VF)
    (hι : inst.ι (tsd.projV X) η = inst.ι (tsd.projV Y) η) :
    tsd.projV X = tsd.projV Y :=
  tsd.eta_nondegen_vertical X Y hι


/-- Two 1-forms are equal if they have the same contraction with every vector field.
This is the non-degeneracy of the contraction pairing on 1-forms. -/
lemma ι_one_form_eq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (α β : Ω 1) (h : ∀ X : VF, inst.ι X α = inst.ι X β) : α = β := by
  have hsub : α - β = 0 := by
    apply inst.ι_one_form_nondegenerate
    intro X
    have hX := h X
    have : inst.ι X (α - β) = inst.ι X α - inst.ι X β := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rw [show -β = (-1 : ℝ) • β from (neg_one_smul ℝ β).symm]
      rw [inst.ι_add, inst.ι_smul]
      rw [neg_one_smul]
    rw [this, hX, sub_self]
  exact sub_eq_zero.mp hsub


/-- If $\iota_{X_V}\beta = 0$, then $\iota_{X_V}(\eta + k\beta) = \iota_{X_V}\eta$:
contraction by a vector annihilating $\beta$ ignores the $\beta$ term. -/
theorem vertical_contraction_ignores_base
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η β : Ω 2) (X_V : VF) (k : ℝ)
    (hV_beta : inst.ι X_V β = 0) :
    inst.ι X_V (η + k • β) = inst.ι X_V η := by
  rw [inst.ι_add, inst.ι_smul, hV_beta, smul_zero, add_zero]

/-- Extraction step in Thurston's argument: if $\iota_X(\eta + k\beta) = \iota_Y(\eta + k\beta)$
and $\beta$ is killed by all vertical vectors, then the vertical parts of $X$ and $Y$
already agree when contracted against $\eta$:
$\iota_{\mathrm{projV}\,X}\eta = \iota_{\mathrm{projV}\,Y}\eta$. -/
theorem extract_vertical_eta_eq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η β : Ω 2) (k : ℝ)
    (split : TangentSplitting (inst := inst) η)
    (hV_beta : ∀ X : VF, inst.ι (split.projV X) β = 0)
    (X Y : VF)
    (hXY : inst.ι X (η + k • β) = inst.ι Y (η + k • β)) :
    inst.ι (split.projV X) η = inst.ι (split.projV Y) η := by


  apply ι_one_form_eq (inst := inst)
  intro Z


  have hVX : inst.ι (split.projV X) (η + k • β) = inst.ι (split.projV X) η :=
    vertical_contraction_ignores_base η β (split.projV X) k (hV_beta X)
  have hVY : inst.ι (split.projV Y) (η + k • β) = inst.ι (split.projV Y) η :=
    vertical_contraction_ignores_base η β (split.projV Y) k (hV_beta Y)
  have hdecomp_X := split.decompose X (η + k • β)
  have hdecomp_Y := split.decompose Y (η + k • β)
  rw [hVX] at hdecomp_X; rw [hVY] at hdecomp_Y
  have h1_eq : inst.ι (split.projV X) η + inst.ι (split.projH X) (η + k • β) =
               inst.ι (split.projV Y) η + inst.ι (split.projH Y) (η + k • β) := by
    rw [← hdecomp_X, ← hdecomp_Y]; exact hXY


  have hHZ_VX : inst.ι (split.projH Z) (inst.ι (split.projV X) η) = 0 := by
    rw [inst.ι_ι_anticomm]; simp [split.orthogonal Z X]
  have hHZ_VY : inst.ι (split.projH Z) (inst.ι (split.projV Y) η) = 0 := by
    rw [inst.ι_ι_anticomm]; simp [split.orthogonal Z Y]


  have hVZ_HX : inst.ι (split.projV Z) (inst.ι (split.projH X) (η + k • β)) = 0 := by
    rw [inst.ι_add (split.projH X), inst.ι_smul (split.projH X)]


    rw [inst.ι_add (split.projV Z)]

    rw [split.orthogonal X Z]

    rw [inst.ι_smul (split.projV Z)]
    rw [inst.ι_ι_anticomm, hV_beta Z]
    simp [neg_zero, smul_zero, DifferentialFormSpace.ι_zero_val]
  have hVZ_HY : inst.ι (split.projV Z) (inst.ι (split.projH Y) (η + k • β)) = 0 := by
    rw [inst.ι_add (split.projH Y), inst.ι_smul (split.projH Y)]
    rw [inst.ι_add (split.projV Z)]
    rw [split.orthogonal Y Z]
    rw [inst.ι_smul (split.projV Z)]
    rw [inst.ι_ι_anticomm, hV_beta Z]
    simp [neg_zero, smul_zero, DifferentialFormSpace.ι_zero_val]


  have hVZ_eq : inst.ι (split.projV Z) (inst.ι (split.projV X) η) =
                inst.ι (split.projV Z) (inst.ι (split.projV Y) η) := by
    have := congr_arg (inst.ι (split.projV Z)) h1_eq
    rwa [inst.ι_add (split.projV Z), inst.ι_add (split.projV Z),
         hVZ_HX, hVZ_HY, add_zero, add_zero] at this


  rw [split.decompose Z (inst.ι (split.projV X) η),
      split.decompose Z (inst.ι (split.projV Y) η)]
  rw [hHZ_VX, hHZ_VY, add_zero, add_zero]
  exact hVZ_eq

/-- Pullback of the zero form is zero: $\varphi^*(0) = 0$. -/
lemma DFSMorphism.pullback_zero
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) {p : ℕ} :
    φ.pullback (0 : Ω₂ p) = 0 := by
  have := φ.pullback_smul (0 : ℝ) (0 : Ω₂ p)
  simp only [zero_smul] at this; exact this

/-- Pullback of a closed form is closed: $d\alpha = 0 \implies d(\varphi^*\alpha) = 0$,
since $\varphi^*$ commutes with $d$. -/
lemma DFSMorphism.pullback_closed_form
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) {p : ℕ} (α : Ω₂ p)
    (hclosed : inst₂.d α = 0) :
    inst₁.d (φ.pullback α) = 0 := by
  rw [← φ.pullback_comm_d, hclosed, φ.pullback_zero]






/-- Convex-combination step: if two 2-forms $\alpha_1, \alpha_2$ both restrict to
$\omega_F$ on the fiber, then so does any affine combination
$r_1\alpha_1 + r_2\alpha_2$ with $r_1 + r_2 = 1$. -/
theorem thurston_fiber_restriction_step
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (i : DFSMorphism Ω_F VF_F Ω_M VF_M)
    (α₁ α₂ : Ω_M 2) (r₁ r₂ : ℝ)
    (ωF : Ω_F 2)
    (h₁ : i.pullback α₁ = ωF)
    (h₂ : i.pullback α₂ = ωF)
    (hsum : r₁ + r₂ = 1) :
    i.pullback (r₁ • α₁ + r₂ • α₂) = ωF := by
  rw [i.pullback_add, i.pullback_smul, i.pullback_smul, h₁, h₂]
  rw [← add_smul, hsum, one_smul]


/-- Local complex coordinates $(z_1, z_2)$ on a 2-complex-dimensional patch:
two 0-forms $z_1, z_2$ with their differentials $dz_1, dz_2$, where $dz_1 \neq 0$
and $dz_2$ is not a real multiple of $dz_1$ (so $\{dz_1, dz_2\}$ are linearly
independent). Used to express the Lefschetz local model $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
structure HasComplexCoords₂
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  z₁ : Ω 0
  z₂ : Ω 0
  dz₁ : Ω 1
  dz₂ : Ω 1
  dz₁_eq : inst.d z₁ = dz₁
  dz₂_eq : inst.d z₂ = dz₂
  dz₁_ne_zero : dz₁ ≠ 0
  dz₂_indep : ∀ (r : ℝ), dz₂ ≠ r • dz₁

/-- A single local complex coordinate $w$ with non-zero differential $dw$, used as the
target coordinate for the standard Lefschetz model $w = z_1^2 + z_2^2$. -/
structure HasComplexCoord₁
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  w : Ω 0
  dw : Ω 1
  dw_eq : inst.d w = dw
  dw_ne_zero : dw ≠ 0

/-- The local model map $q: \mathbb{C}^2 \to \mathbb{C}$ at a Lefschetz critical point,
characterized in coordinates by the formula $q^*(w) = z_1^2 + z_2^2$. -/
structure IsStandardQuadraticMap
    {Ω_src : ℕ → Type*} {VF_src : Type*}
    {Ω_tgt : ℕ → Type*} {VF_tgt : Type*}
    [inst_src : DifferentialFormSpace Ω_src VF_src]
    [inst_tgt : DifferentialFormSpace Ω_tgt VF_tgt]
    (q : DFSMorphism Ω_src VF_src Ω_tgt VF_tgt)
    (coords_src : HasComplexCoords₂ Ω_src VF_src)
    (coord_tgt : HasComplexCoord₁ Ω_tgt VF_tgt) where
  q_formula : q.pullback coord_tgt.w =
    inst_src.fMul coords_src.z₁ coords_src.z₁ +
    inst_src.fMul coords_src.z₂ coords_src.z₂


/-- A map $f: M^4 \to B^2$ **has the standard Lefschetz local quadratic model** at a
critical point: there exist local source and target charts and a model map $q$ such
that $f$ pulls back to $q$ on the charted domain, $q$ has a critical point (degenerate
contraction with some non-zero 1-form), a non-degenerate symplectic 2-form
pulls back to a non-degenerate form upstairs, and the pair is the standard quadratic
map $(z_1, z_2) \mapsto z_1^2 + z_2^2$ in suitable complex coordinates. -/
def HasLocalQuadraticModel
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    (f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2) : Prop :=


  ∃ (Ω_loc_src : ℕ → Type) (VF_loc_src : Type)
    (inst_loc_src : DifferentialFormSpace Ω_loc_src VF_loc_src)
    (Ω_loc_tgt : ℕ → Type) (VF_loc_tgt : Type)
    (inst_loc_tgt : DifferentialFormSpace Ω_loc_tgt VF_loc_tgt)

    (q : @DFSMorphism Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt inst_loc_src inst_loc_tgt)

    (chartSource : @DFSMorphism Ω_loc_src VF_loc_src Ω_M VF_M inst_loc_src inst_M)

    (chartTarget : @DFSMorphism Ω_loc_tgt VF_loc_tgt Ω_B2 VF_B2 inst_loc_tgt inst_B2),

    (∀ {p : ℕ} (α : Ω_B2 p),
      chartSource.pullback (f.pullback α) = q.pullback (chartTarget.pullback α)) ∧


    (∃ (α : Ω_loc_tgt 1), α ≠ 0 ∧
      ¬ Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback α))) ∧


    (∃ (ω_tgt : Ω_loc_tgt 2),

      Function.Injective (fun (v : VF_loc_tgt) =>
        inst_loc_tgt.ι v ω_tgt) ∧

      Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback ω_tgt))) ∧


    (∃ (coords_src : @HasComplexCoords₂ Ω_loc_src VF_loc_src inst_loc_src)
       (coord_tgt : @HasComplexCoord₁ Ω_loc_tgt VF_loc_tgt inst_loc_tgt),
       @IsStandardQuadraticMap Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt
         inst_loc_src inst_loc_tgt q coords_src coord_tgt)

/-- An orientation on a differential-form space: a fixed top-degree dimension,
a nowhere-vanishing closed volume form. -/
class IsOriented
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  dim : ℕ
  volumeForm : Ω dim
  volumeForm_ne_zero : volumeForm ≠ 0
  volumeForm_closed : inst.d volumeForm = 0


/-- A **Lefschetz fibration** $f: M^4 \to \Sigma^2$ between oriented manifolds with a
finite set of isolated critical points, each locally modeled in oriented complex
coordinates as $\mathbb{C}^2 \to \mathbb{C}$, $(z_1, z_2) \mapsto z_1^2 + z_2^2$.

Carries:
- the map $f$,
- inclusion of a generic fiber,
- a finite list of critical points, and
- at each critical point, an instance of `HasLocalQuadraticModel`. -/
structure LefschetzFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [orientM : IsOriented Ω_M VF_M]
    [orientB : IsOriented Ω_B2 VF_B2] where
  f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2
  genericFiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M
  numCriticalPoints : ℕ
  dim_total_eq : orientM.dim = 4
  dim_base_eq : orientB.dim = 2
  hasLocalModel : ∀ (_ : Fin numCriticalPoints),
    HasLocalQuadraticModel (inst_M := inst_M) (inst_B2 := inst_B2) f

/-- A **vanishing cycle** of a Lefschetz fibration: a (codimension-one) cycle in a
generic fiber that collapses to a point at a designated critical point, encoded as
a morphism from a "cycle" form space into the fiber form space along with the
critical-point index. -/
structure VanishingCycle
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    {Ω_S : ℕ → Type*} {VF_S : Type*}
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [inst_S : DifferentialFormSpace Ω_S VF_S] where
  cycle : DFSMorphism Ω_S VF_S Ω_F VF_F
  criticalPointIndex : ℕ

/-- The **monodromy representation** of a Lefschetz fibration: for each singular fiber,
a Dehn twist of the generic fiber, together with its inverse, satisfying the
two-sided inverse axioms. -/
structure MonodromyRep
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_F : DifferentialFormSpace Ω_F VF_F] where
  numSingularFibers : ℕ
  dehnTwist : Fin numSingularFibers → DFSMorphism Ω_F VF_F Ω_F VF_F
  dehnTwistInv : Fin numSingularFibers → DFSMorphism Ω_F VF_F Ω_F VF_F
  left_inv : ∀ (j : Fin numSingularFibers) {p : ℕ} (α : Ω_F p),
    (dehnTwistInv j).pullback ((dehnTwist j).pullback α) = α
  right_inv : ∀ (j : Fin numSingularFibers) {p : ℕ} (α : Ω_F p),
    (dehnTwist j).pullback ((dehnTwistInv j).pullback α) = α


/-- The hypothesis "$[F] \neq 0 \in H_2(M, \mathbb{R})$" of Gompf's theorem, expressed
dually: there exists a closed 2-form $\eta$ on $M$ whose restriction to the generic
fiber is non-zero (so $[F]$ pairs non-trivially with the cohomology class $[\eta]$). -/
structure FiberClassNonzero
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsOriented Ω_M VF_M] [IsOriented Ω_B2 VF_B2]
    (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)) : Prop where
  exists_pairing_witness : ∃ (η : Ω_M 2),
    inst_M.d η = 0 ∧ lf.genericFiberInclusion.pullback η ≠ 0



/-- The symplectic manifold $S$ admits a **blowup** $\hat M$, i.e. there is a blowdown
morphism $\hat M \to M$ with finitely many exceptional divisors $E_j$, each closed
non-exact (so genuinely contributes to cohomology), and the blowdown is locally
modeled by the standard quadratic blowup
$\hat{\mathbb{C}^2} = \{(x, \ell) \in \mathbb{C}^2 \times \mathbb{CP}^1 : x \in \ell\}$. -/
class IsBlowup
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_Mhat : ℕ → Type*} {VF_Mhat : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_Mhat : DifferentialFormSpace Ω_Mhat VF_Mhat]
    (S : SymplecticManifold Ω_M VF_M) : Prop where
  exists_blowdown :
    ∃ (blowdown : DFSMorphism Ω_Mhat VF_Mhat Ω_M VF_M)
      (numBlowups : ℕ) (_ : 0 < numBlowups)
      (exceptionalClass : Fin numBlowups → Ω_Mhat 2),

      (∀ j, inst_Mhat.d (exceptionalClass j) = 0) ∧


      (∀ j, ¬ ∃ (β : Ω_Mhat 1), inst_Mhat.d β = exceptionalClass j) ∧


      (∀ _j : Fin numBlowups,
        HasLocalQuadraticModel (inst_M := inst_Mhat) (inst_B2 := inst_M) blowdown)

/-- The differential-form space admits a **Lefschetz fibration to $S^2$**: there exist
form spaces for a 2-dimensional base $B$ and a fiber $F$, orientations on both
total space and base, a `LefschetzFibration` between them, and a symplectic 2-form
on $B$ which is closed, non-degenerate, and non-exact (modeling the $S^2$ symplectic
form). -/
class AdmitsLefschetzFibration
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : Prop where
  exists_fibration :
    ∃ (Ω_B : ℕ → Type*) (VF_B : Type*) (inst_B : DifferentialFormSpace Ω_B VF_B)
      (Ω_F : ℕ → Type*) (VF_F : Type*) (inst_F : DifferentialFormSpace Ω_F VF_F)
      (_orientM : @IsOriented Ω VF inst) (_orientB : @IsOriented Ω_B VF_B inst_B)
      (_lf : @LefschetzFibration Ω VF Ω_B VF_B Ω_F VF_F inst inst_B inst_F _orientM _orientB),

      ∃ (ωB : Ω_B 2),
        inst_B.d ωB = 0 ∧
        Function.Injective (fun (X : VF_B) => inst_B.ι X ωB) ∧

        ¬ (∃ (β : Ω_B 1), inst_B.d β = ωB)




/-- Data for forming the **symplectic sum** (a.k.a. fiber sum) of two compact symplectic
manifolds $M_1, M_2$ along a common codimension-2 symplectic submanifold $Q$:
inclusions $\iota_j : Q \hookrightarrow M_j$ pulling $\omega_{M_j}$ back to
$\omega_Q$, with the codimension and a triviality witness for the normal bundle
(a closed 2-form on each $M_j$ restricting to zero on $Q$ and itself non-zero). -/
structure FiberSum.DFS
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω_Q : ℕ → Type*} {VF_Q : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_Q : DifferentialFormSpace Ω_Q VF_Q]
    [dim_M₁ : SymplecticManifoldDim Ω₁ VF₁]
    [dim_M₂ : SymplecticManifoldDim Ω₂ VF₂]
    [dim_Q : SymplecticManifoldDim Ω_Q VF_Q]
    [IsCompactManifold Ω_Q VF_Q] where
  M₁ : SymplecticManifold Ω₁ VF₁
  M₂ : SymplecticManifold Ω₂ VF₂
  Q : SymplecticManifold Ω_Q VF_Q
  ι₁ : DFSMorphism Ω_Q VF_Q Ω₁ VF₁
  ι₂ : DFSMorphism Ω_Q VF_Q Ω₂ VF₂
  ι₁_symplectic : ι₁.pullback M₁.ω = Q.ω
  ι₂_symplectic : ι₂.pullback M₂.ω = Q.ω
  codim_two_M₁ : dim_Q.n + 1 = dim_M₁.n
  codim_two_M₂ : dim_Q.n + 1 = dim_M₂.n
  normalBundleTriv_M₁ : ∃ (η : Ω₁ 2),
    inst₁.d η = 0 ∧ ι₁.pullback η = 0 ∧ η ≠ 0
  normalBundleTriv_M₂ : ∃ (η : Ω₂ 2),
    inst₂.d η = 0 ∧ ι₂.pullback η = 0 ∧ η ≠ 0




/-- A group $G$ is **finitely presented**: there exist $n, m \in \mathbb{N}$, a
surjection $f: F_n \twoheadrightarrow G$ from the free group on $n$ generators,
and $m$ relator words generating $\ker f$ as a normal subgroup. -/
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  has_finite_presentation : ∃ (n m : ℕ) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧
    ∃ (rels : Fin m → FreeGroup (Fin n)),
      MonoidHom.ker f = Subgroup.normalClosure (Set.range rels)

/-- The group $G$ is the fundamental group $\pi_1$ of the compact symplectic 4-manifold
$S$: $S$ is finitely presented, admits a compatible almost complex structure, and
there is a group isomorphism $\pi_1(S) \cong G$. -/
class IsFundGroupOfSymplectic4Mfd
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (G : Type*) [Group G] where
  fp : IsFinitelyPresented G
  has_acs : ∃ (J : AlmostComplexStr (inst := inst)), IsCompatibleACS S J
  π₁ : Type*
  grp_π₁ : Group π₁
  iso : @MulEquiv π₁ G grp_π₁.toMul _




/-- A schematic **handlebody decomposition** of a closed 4-manifold: existence of
$n_k$ $k$-handles for $k = 0, \dots, 4$ with the standard normalization (a single
0-handle and a single 4-handle, plus at least one 2-handle). -/
structure HasHandlebodyDecomposition
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : Prop where
  handle_data : ∃ (n₀ _n₁ n₂ _n₃ n₄ : ℕ),
    n₀ = 1 ∧ n₄ = 1 ∧ 0 < n₂

/-- Carrier for an Euler characteristic value $\chi \in \mathbb{Z}$. -/
structure HasEulerCharacteristic
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  euler : ℤ


/-- A pullback morphism $\varphi$ is **$\omega$-tame** if the pulled-back form
$\varphi^*\omega$ is non-degenerate on contraction. -/
class IsOmegaTame
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (φ : DFSMorphism Ω VF Ω VF) : Prop where
  taming_nondeg : Function.Injective (fun (v : VF) => inst.ι v (φ.pullback S.ω))

/-- A **symplectic branched covering**: a symplectic target $(Y, \omega_Y)$, a covering
map $f: X \to Y$, and an integer degree $\geq 1$. -/
structure SymplecticBranchedCovering
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y] where
  target : SymplecticManifold Ω_Y VF_Y
  f : DFSMorphism Ω_X VF_X Ω_Y VF_Y
  degree : ℕ
  degree_pos : 0 < degree

/-- A linear combination $\eta + \varepsilon\alpha$ of two closed 2-forms is closed:
$d(\eta + \varepsilon\alpha) = d\eta + \varepsilon\, d\alpha = 0$. -/
theorem branched_cover_form_closed
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (η : Ω 2) (α : Ω 2) (ε : ℝ)
    (hη_closed : inst.d η = 0)
    (hα_exact : inst.d α = 0) :
    inst.d (η + ε • α) = 0 := by
  rw [inst.d_add, inst.d_smul, hη_closed, hα_exact, smul_zero, add_zero]


/-- Data for the **perturbation step** in symplectifying a branched cover: a closed
auxiliary 2-form $\alpha$ and parameter $\varepsilon \neq 0$ together with a
tangent splitting whose vertical kernel is annihilated by $\eta$ (the pullback
of the base symplectic form), $\alpha$ is non-degenerate on the kernel, and
$\eta + \varepsilon\alpha$ is non-degenerate on horizontal vectors. -/
class BranchedCoverPerturbationData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η α : Ω 2) (ε : ℝ)
    extends TangentSplitting (inst := inst) α where
  ε_ne_zero : ε ≠ 0
  pullback_vanishes_on_K : ∀ (X : VF), inst.ι (projV X) η = 0
  alpha_nondeg_on_K : ∀ (X Y : VF),
    inst.ι (projV X) α = inst.ι (projV Y) α → projV X = projV Y
  complement_nondeg : ∀ (X Y : VF), projV X = projV Y →
    inst.ι X (η + ε • α) = inst.ι Y (η + ε • α) → X = Y
  alpha_closed : inst.d α = 0

/-- Rescaling identity for the contraction pairing: if $\iota_X(\eta + \varepsilon\alpha)
= \iota_Y(\eta + \varepsilon\alpha)$, then $\iota_X(\alpha + \varepsilon^{-1}\eta)
= \iota_Y(\alpha + \varepsilon^{-1}\eta)$, using $\eta + \varepsilon\alpha =
\varepsilon(\alpha + \varepsilon^{-1}\eta)$ and the $\mathbb R$-linearity of $\iota$. -/
lemma rescale_contraction_eq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η α : Ω 2) (ε : ℝ) (hε : ε ≠ 0)
    (X Y : VF)
    (h : inst.ι X (η + ε • α) = inst.ι Y (η + ε • α)) :
    inst.ι X (α + ε⁻¹ • η) = inst.ι Y (α + ε⁻¹ • η) := by

  have key : η + ε • α = ε • (α + ε⁻¹ • η) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hε, one_smul, add_comm]
  rw [key] at h
  rw [inst.ι_smul, inst.ι_smul] at h

  have h1 : ε⁻¹ • (ε • inst.ι X (α + ε⁻¹ • η)) = ε⁻¹ • (ε • inst.ι Y (α + ε⁻¹ • η)) :=
    congrArg (ε⁻¹ • ·) h
  simp [smul_smul, inv_mul_cancel₀ hε] at h1
  exact h1

/-- Given a perturbation data instance, there exist a closed $\alpha'$ and parameter
$\varepsilon'$ such that $f^*\omega_Y + \varepsilon'\alpha'$ is non-degenerate
upstairs. This is the symplectic non-degeneracy step in the branched-cover
construction. -/
theorem branched_cover_perturbation_nondegeneracy
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
    (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y))
    (α : Ω_X 2) (ε : ℝ)
    (bcpd : BranchedCoverPerturbationData (inst := inst_X)
      (bc.f.pullback bc.target.ω) α ε) :
    ∃ (α' : Ω_X 2) (ε' : ℝ),
      inst_X.d α' = 0 ∧
      Function.Injective (fun (X : VF_X) => inst_X.ι X (bc.f.pullback bc.target.ω + ε' • α')) := by
  let η := bc.f.pullback bc.target.ω
  let split := bcpd.toTangentSplitting
  refine ⟨α, ε, bcpd.alpha_closed, fun X Y hXY => ?_⟩

  have h_rescaled : inst_X.ι X (α + ε⁻¹ • η) = inst_X.ι Y (α + ε⁻¹ • η) :=
    rescale_contraction_eq η α ε bcpd.ε_ne_zero X Y hXY


  have h_alpha_K_eq : inst_X.ι (split.projV X) α = inst_X.ι (split.projV Y) α :=
    extract_vertical_eta_eq α η ε⁻¹ split
      (fun Z => bcpd.pullback_vanishes_on_K Z)
      X Y h_rescaled

  have hK_eq : split.projV X = split.projV Y :=
    bcpd.alpha_nondeg_on_K X Y h_alpha_K_eq

  exact bcpd.complement_nondeg X Y hK_eq hXY

/-- A symplectic branched covering equipped with valid perturbation data carries a
symplectic form $\omega_X$ on the source: it is closed and non-degenerate. -/
theorem branched_cover_symplectic
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
    (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y))
    (α : Ω_X 2) (ε : ℝ)
    (bcpd : BranchedCoverPerturbationData (inst := inst_X)
      (bc.f.pullback bc.target.ω) α ε) :
    ∃ (ωX : Ω_X 2),
      inst_X.d ωX = 0 ∧
      Function.Injective (fun (X : VF_X) => inst_X.ι X ωX) := by

  obtain ⟨α', ε', hα_closed, h_nondeg⟩ :=
    branched_cover_perturbation_nondegeneracy bc α ε bcpd

  refine ⟨bc.f.pullback bc.target.ω + ε' • α', ?_, h_nondeg⟩

  have h_pullback_closed : inst_X.d (bc.f.pullback bc.target.ω) = 0 :=
    bc.f.pullback_closed_form bc.target.ω bc.target.closed
  exact branched_cover_form_closed (bc.f.pullback bc.target.ω) α' ε' h_pullback_closed hα_closed


/-- Data for the **adjunction formula** for a symplectic surface inside a 4-manifold:
the genus $g$, self-intersection $[\Sigma]\cdot[\Sigma]$, the value $\langle c_1, [\Sigma]\rangle$,
the first Chern numbers of the tangent and normal bundles, and the relations
- $c_1(T\Sigma) = 2 - 2g$ (Gauss-Bonnet),
- $c_1(N\Sigma) = [\Sigma]\cdot[\Sigma]$ (normal-bundle degree),
- $\langle c_1, [\Sigma]\rangle = c_1(T\Sigma) + c_1(N\Sigma)$ (splitting of $c_1(TM)|_\Sigma$). -/
structure HasAdjunctionData
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  genus : ℕ
  selfIntersection : ℤ
  c₁_eval : ℤ
  chern_tangent : ℤ
  chern_normal : ℤ
  gauss_bonnet_eq : chern_tangent = 2 - 2 * (genus : ℤ)
  normal_bundle_degree_eq : chern_normal = selfIntersection
  chern_split_eq : c₁_eval = chern_tangent + chern_normal


/-- Gauss-Bonnet: $c_1(T\Sigma) = 2 - 2g$. -/
theorem HasAdjunctionData.gauss_bonnet
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (hA : HasAdjunctionData S) :
    hA.chern_tangent = 2 - 2 * (hA.genus : ℤ) :=
  hA.gauss_bonnet_eq

/-- Normal-bundle degree: $c_1(N\Sigma) = [\Sigma]\cdot[\Sigma]$. -/
theorem HasAdjunctionData.normal_bundle_degree
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (hA : HasAdjunctionData S) :
    hA.chern_normal = hA.selfIntersection :=
  hA.normal_bundle_degree_eq

/-- Chern-class splitting: $\langle c_1, [\Sigma]\rangle = c_1(T\Sigma) + c_1(N\Sigma)$. -/
theorem HasAdjunctionData.chern_split
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (hA : HasAdjunctionData S) :
    hA.c₁_eval = hA.chern_tangent + hA.chern_normal :=
  hA.chern_split_eq

/-- The genus formula deduced from the data: $\langle c_1, [\Sigma]\rangle = 2 - 2g + [\Sigma]\cdot[\Sigma]$. -/
theorem HasAdjunctionData.genus_formula
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (hA : HasAdjunctionData S) :
    hA.c₁_eval = 2 - 2 * (hA.genus : ℤ) + hA.selfIntersection := by
  rw [hA.chern_split, hA.gauss_bonnet, hA.normal_bundle_degree]

/-- **Adjunction formula.** For a symplectic surface $\Sigma \subset M$ with adjunction
data, $\langle c_1, [\Sigma]\rangle = 2 - 2g + [\Sigma]\cdot[\Sigma]$. -/
theorem adjunction_formula
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (hA : HasAdjunctionData S) :
    hA.c₁_eval = 2 - 2 * (hA.genus : ℤ) + hA.selfIntersection :=
  hA.genus_formula


/-- **Genus lower bound for a square-zero symplectic surface.**

If $[\Sigma]\cdot[\Sigma] = 0$ and the adjunction inequality $2g - 2 \geq [\Sigma]\cdot[\Sigma]$
holds when $[\Sigma]\cdot[\Sigma] \geq 0$, then $g \geq 1$. -/
theorem adjunction_inequality_fiber_genus
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (hA : HasAdjunctionData S)
    (h_self_zero : hA.selfIntersection = 0)


    (h_adjunction_ineq : hA.selfIntersection ≥ 0 →
      2 * (hA.genus : ℤ) - 2 ≥ hA.selfIntersection) :
    hA.genus ≥ 1 := by
  have hge : hA.selfIntersection ≥ 0 := by omega
  have h := h_adjunction_ineq hge
  omega


/-- Data for the **ramification locus** $R \subset X$ of a symplectic branched cover
$f: X \to Y$ and its image $D \subset Y$ (the branch divisor): inclusions $R
\hookrightarrow X$ and $D \hookrightarrow Y$, the restricted map $f|_R: R \to D$,
the property that $f^*\omega_Y$ degenerates along $R$, and the factorization
$f \circ \mathrm{incl}_R = \mathrm{incl}_D \circ (f|_R)$. -/
structure RamificationData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
    (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y)) where
  Ω_R : ℕ → Type*
  VF_R : Type*
  [inst_R : DifferentialFormSpace Ω_R VF_R]
  Ω_D : ℕ → Type*
  VF_D : Type*
  [inst_D : DifferentialFormSpace Ω_D VF_D]
  inclR : @DFSMorphism Ω_R VF_R Ω_X VF_X inst_R inst_X
  inclD : @DFSMorphism Ω_D VF_D Ω_Y VF_Y inst_D inst_Y
  fRestrict : @DFSMorphism Ω_R VF_R Ω_D VF_D inst_R inst_D
  pullback_degenerate_on_R :
    ¬ Function.Injective (fun (v : VF_R) =>
        inst_R.ι v (inclR.pullback (bc.f.pullback bc.target.ω)))
  factorization : ∀ {p : ℕ} (α : Ω_Y p),
    inclR.pullback (bc.f.pullback α) = fRestrict.pullback (inclD.pullback α)


/-- A **symplectic form on a manifold $M$** in the manifold-with-corners formalism:
half the dimension, a skew-symmetric non-degenerate bilinear form on the model
space $E$. -/
structure ManifoldSymplecticForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ⊤ M] where
  halfDim : ℕ
  form : E →L[ℝ] E →L[ℝ] ℝ
  skew : ∀ (v w : E), form v w = -(form w v)
  nondegenerate : Function.Injective form


/-- **Symplectic fiber-sum data** in the manifold-with-corners formalism: two
symplectic manifolds $M_1, M_2$ with a common codimension-2 submanifold $Q$,
smooth injective embeddings $\iota_j: Q \hookrightarrow M_j$, matching dimensions,
and chosen trivializations of the normal $\mathbb R^2$-bundles of $Q$ in $M_1$
and $M_2$ along the zero section. -/
structure FiberSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M₁ M₂ Q : Type*)
    [TopologicalSpace M₁] [ChartedSpace H M₁] [IsManifold I ⊤ M₁]
    [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ⊤ M₂]
    [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ⊤ Q] where
  ι₁ : Q → M₁
  ι₂ : Q → M₂
  ι₁_injective : Function.Injective ι₁
  ι₂_injective : Function.Injective ι₂
  ι₁_smooth : MDifferentiable I I ι₁
  ι₂_smooth : MDifferentiable I I ι₂
  symp₁ : ManifoldSymplecticForm I M₁
  symp₂ : ManifoldSymplecticForm I M₂
  sympQ : ManifoldSymplecticForm I Q
  codim_two₁ : sympQ.halfDim + 1 = symp₁.halfDim
  codim_two₂ : sympQ.halfDim + 1 = symp₂.halfDim
  normalBundleTriv₁ : ∃ (U₁ : Set M₁) (φ₁ : U₁ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₁ ∧

    (∀ q : Q, ∃ h : ι₁ q ∈ U₁, φ₁ ⟨ι₁ q, h⟩ = (q, 0))
  normalBundleTriv₂ : ∃ (U₂ : Set M₂) (φ₂ : U₂ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₂ ∧
    (∀ q : Q, ∃ h : ι₂ q ∈ U₂, φ₂ ⟨ι₂ q, h⟩ = (q, 0))


/-- **Lefschetz pencil data** in the manifold-with-corners formalism: a smooth map
$f: M^4 \to B^2$ between manifolds, finitely many isolated critical points where
the derivative vanishes, and surjective derivative (i.e. submersion) at non-critical
points; together with the existence of a generic regular value $b$ such that
$f^{-1}(b)$ is non-empty and avoids the critical set. -/
structure LefschetzPencil.Mfld
    {E₄ : Type*} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    {H₄ : Type*} [TopologicalSpace H₄]
    (I₄ : ModelWithCorners ℝ E₄ H₄)
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    (I₂ : ModelWithCorners ℝ E₂ H₂)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H₄ M] [IsManifold I₄ ⊤ M]
    (B₂ : Type*) [TopologicalSpace B₂] [ChartedSpace H₂ B₂] [IsManifold I₂ ⊤ B₂]
    where
  f : M → B₂
  numCriticalPoints : ℕ
  criticalPoints : Fin numCriticalPoints → M
  smooth_away : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    MDifferentiableAt I₄ I₂ f x
  deriv_zero_at_crit : ∀ i : Fin numCriticalPoints,
    mfderiv I₄ I₂ f (criticalPoints i) = 0
  hessian_nondegenerate : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    Function.Surjective (mfderiv I₄ I₂ f x)
  generic_fiber_nonempty : ∃ (b : B₂),
    (∀ i, f (criticalPoints i) ≠ b) ∧
    Set.Nonempty (f ⁻¹' {b})
