/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.LefschetzPencils

set_option autoImplicit false

open DifferentialFormSpace


/-- Definition 1: a map $f : M \to B$ is a symplectic fibration with fiber $(F, \omega_F)$ if there exists a `SymplecticFibration` structure realizing $f$, the fiber inclusion, and the fiber symplectic form (so the structure group reduces to $\mathrm{Symp}(F, \omega_F)$). -/
def IsSymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (f : DFSMorphism Ω_M VF_M Ω_B VF_B)
    (fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M)
    (fiberSymplectic : SymplecticManifold Ω_F VF_F) : Prop :=
  ∃ (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)),
    fib.f = f ∧
    fib.fiberInclusion = fiberInclusion ∧
    fib.fiberSymplectic = fiberSymplectic


/-- A map $f : M \to B^2$ is a Lefschetz fibration (with generic fiber inclusion) if it is realized by some `LefschetzFibration` structure. -/
def IsLefschetzFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsOriented Ω_M VF_M] [IsOriented Ω_B2 VF_B2]
    (f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2)
    (genericFiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M) : Prop :=
  ∃ (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)),
    lf.f = f ∧
    lf.genericFiberInclusion = genericFiberInclusion




/-- Extract the underlying `LefschetzFibration` structure from `IsLefschetzFibration` data. -/
theorem IsLefschetzFibration.toLefschetzFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsOriented Ω_M VF_M] [IsOriented Ω_B2 VF_B2]
    {f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2}
    {fiberIncl : DFSMorphism Ω_F VF_F Ω_M VF_M}
    (hfib : IsLefschetzFibration f fiberIncl) :
    ∃ (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)),
      lf.f = f ∧ lf.genericFiberInclusion = fiberIncl := by
  obtain ⟨lf, hf, hfi⟩ := hfib
  exact ⟨lf, hf, hfi⟩

/-- Extract the underlying `SymplecticFibration` structure from `IsSymplecticFibration` data. -/
theorem IsSymplecticFibration.toSymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    {f : DFSMorphism Ω_M VF_M Ω_B VF_B}
    {fiberIncl : DFSMorphism Ω_F VF_F Ω_M VF_M}
    {fiberSymp : SymplecticManifold Ω_F VF_F}
    (hfib : IsSymplecticFibration f fiberIncl fiberSymp) :
    ∃ (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)),
      fib.f = f ∧ fib.fiberInclusion = fiberIncl ∧ fib.fiberSymplectic = fiberSymp :=
  hfib


/-- A self-transition $g_{ii}$ acts as the identity on forms: $(g_{ii})^* \alpha = \alpha$, deduced from the cocycle and inverse axioms. -/
theorem SymplecticFibration.transition_self_eq
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (i : fib.CoverIdx) {p : ℕ} (α : Ω_F p) :
    (fib.transitionMap i i).pullback α = α := by


  have h_inv := fib.transition_inverse i i α


  have h_cyc := fib.transition_cocycle i i i α


  rw [h_cyc] at h_inv
  exact h_inv


/-- Data for local trivializations of a symplectic fibration: local fiber projections $p_i : M \supset U_i \to F$ that are compatible with transition functions, plus primitives $\beta_i$ realizing $p_i^*\omega_F - \eta = d\beta_i$ for a global $2$-form $\eta$ (used in Thurston's construction). -/
structure SymplecticFibration.LocalTrivializationData
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)) where
  localProj : fib.CoverIdx → DFSMorphism Ω_M VF_M Ω_F VF_F
  proj_transition_compat : ∀ (i j : fib.CoverIdx) {p : ℕ} (α : Ω_F p),
    (localProj i).pullback ((fib.transitionMap i j).pullback α) =
    (localProj j).pullback α
  localPrimitive : fib.CoverIdx → Ω_M 1
  proj_pullback_eq : ∀ (i : fib.CoverIdx) (η : Ω_M 2),
    (localProj i).pullback fib.fiberSymplectic.ω =
      η + inst_M.d (localPrimitive i)

/-- A convex combination $r_1 p_i^*\omega_F + r_2 p_j^*\omega_F$ (with $r_1 + r_2 = 1$) restricts to $\omega_F$ on the fiber, provided each summand does — a key step in Thurston's patching argument. -/
theorem SymplecticFibration.LocalTrivializationData.patching_restricts_to_fiber
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    {fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)}
    (triv : SymplecticFibration.LocalTrivializationData fib)
    (i j : fib.CoverIdx)
    (r₁ r₂ : ℝ)
    (hsum : r₁ + r₂ = 1)
    (h_η_restricts_via_i :
      fib.fiberInclusion.pullback ((triv.localProj i).pullback fib.fiberSymplectic.ω) =
      fib.fiberSymplectic.ω)
    (h_η_restricts_via_j :
      fib.fiberInclusion.pullback ((triv.localProj j).pullback fib.fiberSymplectic.ω) =
      fib.fiberSymplectic.ω) :
    fib.fiberInclusion.pullback
      (r₁ • (triv.localProj i).pullback fib.fiberSymplectic.ω +
       r₂ • (triv.localProj j).pullback fib.fiberSymplectic.ω) =
    fib.fiberSymplectic.ω := by
  rw [fib.fiberInclusion.pullback_add, fib.fiberInclusion.pullback_smul,
      fib.fiberInclusion.pullback_smul, h_η_restricts_via_i, h_η_restricts_via_j]
  rw [← add_smul, hsum, one_smul]
