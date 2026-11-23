/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic

open ContinuousAlternatingMap

/-- A (concrete) differential $n$-form on a normed space $E$: a smooth map assigning to each point an alternating continuous $n$-linear form. -/
abbrev DiffForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  E → E [⋀^Fin n]→L[ℝ] ℝ

/-- Pullback of a differential form along a smooth map: $(f^*\omega)_x(v_1,\dots,v_n) = \omega_{f(x)}(df_x v_1, \dots, df_x v_n)$. -/
noncomputable def pullbackForm {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (f : E₁ → E₂) {n : ℕ} (ω : DiffForm E₂ n) : DiffForm E₁ n :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

namespace DeRhamConcrete

section CohomologyIsomorphism

variable {E_X E_U : Type*}
  [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
  [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]

/-- Concrete deformation retract data $i : X \hookrightarrow U$ and $\pi : U \to X$ with a chain homotopy operator $K$ satisfying $dK + Kd = \mathrm{id} - \pi^* i^*$, used to prove $i^* : H^*(U) \xrightarrow{\sim} H^*(X)$. -/
structure HasDeformationRetractConcrete
    (i : E_X → E_U) (π : E_U → E_X) where
  smooth_i : ContDiff ℝ ⊤ i
  smooth_π : ContDiff ℝ ⊤ π
  retraction : ∀ {n : ℕ} (ω : DiffForm E_X n),
    pullbackForm i (pullbackForm π ω) = ω
  K : ∀ {p : ℕ}, DiffForm E_U (p + 1) → DiffForm E_U p
  K_smul : ∀ {p : ℕ} (r : ℝ) (β : DiffForm E_U (p + 1)),
    K (r • β) = r • K β
  homotopy_formula : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    extDeriv (K β) + K (extDeriv β) = β - pullbackForm π (pullbackForm i β)
  K_vanishes : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    pullbackForm i (K β) = 0
  deg0_injectivity : ∀ (β : DiffForm E_U 0),
    extDeriv β = 0 → pullbackForm i β = 0 → β = 0
  smooth_forms_U : ∀ {n : ℕ} (ω : DiffForm E_U n), ContDiff ℝ ⊤ ω

namespace HasDeformationRetractConcrete

variable {i : E_X → E_U} {π : E_U → E_X}

/-- The exterior derivative squares to zero: $d \circ d = 0$ on smooth forms in $U$. -/
theorem d_squared (hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} (ω : DiffForm E_U n) :
    extDeriv (extDeriv ω) = 0 :=
  extDeriv_extDeriv (hdr.smooth_forms_U ω) le_top

/-- $d$ is linear in subtraction: $d(\omega_1 - \omega_2) = d\omega_1 - d\omega_2$. -/
theorem d_sub (hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} (ω₁ ω₂ : DiffForm E_U n) :
    extDeriv (ω₁ - ω₂) = extDeriv ω₁ - extDeriv ω₂ := by
  funext x
  have h1 := (hdr.smooth_forms_U ω₁).differentiable WithTop.top_ne_zero x
  have h2 := (hdr.smooth_forms_U ω₂).differentiable WithTop.top_ne_zero x
  simp only [extDeriv, Pi.sub_apply, fderiv_sub h1 h2]
  exact map_sub _ _ _

/-- $d$ is additive: $d(\omega_1 + \omega_2) = d\omega_1 + d\omega_2$. -/
theorem d_add (hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} (ω₁ ω₂ : DiffForm E_U n) :
    extDeriv (ω₁ + ω₂) = extDeriv ω₁ + extDeriv ω₂ := by
  funext x
  exact extDeriv_add
    ((hdr.smooth_forms_U ω₁).differentiable WithTop.top_ne_zero x)
    ((hdr.smooth_forms_U ω₂).differentiable WithTop.top_ne_zero x)

/-- Pullback along $i$ commutes with the exterior derivative: $i^*(d\omega) = d(i^*\omega)$. -/
theorem i_comm_d (hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} (ω : DiffForm E_U n) :
    pullbackForm i (extDeriv ω) = extDeriv (pullbackForm i ω) := by
  funext x
  have hω_diff : DifferentiableAt ℝ ω (i x) :=
    (hdr.smooth_forms_U ω).differentiable WithTop.top_ne_zero (i x)
  have := extDeriv_pullback (r := ⊤) hω_diff hdr.smooth_i.contDiffAt le_top
  simp only [pullbackForm] at this ⊢
  exact this.symm

/-- Pullback distributes over subtraction: $i^*(\omega_1 - \omega_2) = i^*\omega_1 - i^*\omega_2$. -/
theorem i_sub (_hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} (ω₁ ω₂ : DiffForm E_U n) :
    pullbackForm i (ω₁ - ω₂) = pullbackForm i ω₁ - pullbackForm i ω₂ := rfl

/-- Pullback of the zero form by $\pi$ is the zero form: $\pi^* 0 = 0$. -/
theorem π_zero (_hdr : HasDeformationRetractConcrete i π)
    {n : ℕ} :
    pullbackForm π (0 : DiffForm E_X n) = (0 : DiffForm E_U n) := rfl

end HasDeformationRetractConcrete


/-- Surjectivity at the cocycle level: every form $\alpha$ on $X$ is the pullback $i^*\beta$ of a form $\beta$ on $U$ (take $\beta = \pi^*\alpha$). -/
theorem cohomology_isomorphism_surjectivity_concrete
    (i : E_X → E_U) (π : E_U → E_X)
    (hdr : HasDeformationRetractConcrete i π) :
    ∀ {p : ℕ} (α : DiffForm E_X p),
      ∃ (β : DiffForm E_U p), pullbackForm i β = α :=
  fun α => ⟨pullbackForm π α, hdr.retraction α⟩


/-- Injectivity at cohomology level: a closed form $\beta$ on $U$ whose restriction $i^*\beta$ is exact is itself exact, proved using the chain-homotopy formula. -/
theorem cohomology_isomorphism_injectivity_concrete
    (i : E_X → E_U) (π : E_U → E_X)
    (hdr : HasDeformationRetractConcrete i π) :
    ∀ (p : ℕ) (β : DiffForm E_U (p + 1)),
      extDeriv β = 0 →
      (∃ (γ : DiffForm E_X p), pullbackForm i β = extDeriv γ) →
      ∃ (η : DiffForm E_U p), β = extDeriv η := by
  intro p β hclosed ⟨γ, hγ⟩

  set dπγ := extDeriv (pullbackForm π γ)
  set β' := β - dπγ with hβ'_def

  have hβ'_closed : extDeriv β' = 0 := by
    rw [hdr.d_sub β dπγ, hclosed, hdr.d_squared, sub_zero]


  have hβ'_vanish : pullbackForm i β' = 0 := by
    rw [hdr.i_sub β dπγ, hdr.i_comm_d (pullbackForm π γ), hdr.retraction γ, hγ, sub_self]


  have hformula := hdr.homotopy_formula β'
  have hK_zero : hdr.K (extDeriv β') = (0 : DiffForm E_U (p + 1)) := by
    rw [hβ'_closed]
    have := hdr.K_smul (0 : ℝ) (0 : DiffForm E_U (p + 1 + 1))
    simp [zero_smul] at this
    exact this
  have hpull_zero : pullbackForm π (pullbackForm i β') = (0 : DiffForm E_U (p + 1)) := by
    rw [hβ'_vanish, hdr.π_zero]
  have hKβ' : extDeriv (hdr.K β') = β' := by
    rw [hK_zero, hpull_zero, add_zero, sub_zero] at hformula
    exact hformula

  refine ⟨hdr.K β' + pullbackForm π γ, ?_⟩
  rw [hdr.d_add (hdr.K β') (pullbackForm π γ), hKβ']
  simp only [hβ'_def]
  abel


/-- Corollary 1: for a deformation retract $i: X \hookrightarrow U$, the pullback $i^* : H^*(U, \mathbb{R}) \to H^*(X, \mathbb{R})$ is an isomorphism (surjective on cocycles, injective in positive degree, and injective on degree-$0$ closed forms). -/
theorem cohomology_isomorphism
    (i : E_X → E_U) (π : E_U → E_X)
    (hdr : HasDeformationRetractConcrete i π) :

    (∀ {p : ℕ} (α : DiffForm E_X p),
      ∃ (β : DiffForm E_U p), pullbackForm i β = α) ∧

    (∀ (p : ℕ) (β : DiffForm E_U (p + 1)),
      extDeriv β = 0 →
      (∃ (γ : DiffForm E_X p), pullbackForm i β = extDeriv γ) →
      ∃ (η : DiffForm E_U p), β = extDeriv η) ∧

    (∀ (β : DiffForm E_U 0),
      extDeriv β = 0 → pullbackForm i β = 0 → β = 0) :=
  ⟨cohomology_isomorphism_surjectivity_concrete i π hdr,
   cohomology_isomorphism_injectivity_concrete i π hdr,
   hdr.deg0_injectivity⟩

end CohomologyIsomorphism

end DeRhamConcrete

section Instances

open DeRhamConcrete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback along the identity is the identity: $\mathrm{id}^*\omega = \omega$. -/
lemma pullbackForm_id {n : ℕ} (ω : DiffForm E n) :
    pullbackForm id ω = ω := by
  ext x v
  simp [pullbackForm, fderiv_id, ContinuousAlternatingMap.compContinuousLinearMap]

/-- The exterior derivative of the zero form is zero: $d 0 = 0$. -/
lemma extDeriv_zero_eq_zero {n : ℕ} :
    extDeriv (0 : DiffForm E n) = (0 : DiffForm E (n + 1)) := by
  funext x
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) x) = 0
  rw [show (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) = Function.const E 0 from rfl]
  simp [ContinuousAlternatingMap.alternatizeUncurryFin, ContinuousLinearMap.map_zero]

/-- Any function out of a subsingleton normed space is smooth (it is constant). -/
lemma contDiff_of_subsingleton_domain {E' F : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E' → F) : ContDiff ℝ ⊤ f := by
  have : f = Function.const E' (f 0) := by
    ext x; have h : x = 0 := Subsingleton.elim x 0; subst h; rfl
  rw [this]; exact contDiff_const

/-- The trivial deformation retract instance on a subsingleton (e.g., a point), with $K \equiv 0$. -/
noncomputable def DeRhamConcrete.HasDeformationRetractConcrete.ofSubsingleton
    (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E'] :
    HasDeformationRetractConcrete (id : E' → E') (id : E' → E') where
  smooth_i := contDiff_id
  smooth_π := contDiff_id
  retraction := fun ω => by rw [pullbackForm_id, pullbackForm_id]
  K := fun _ => 0
  K_smul := fun r β => by simp
  homotopy_formula := fun {p} β => by
    simp only [pullbackForm_id, sub_self]
    rw [extDeriv_zero_eq_zero]
    simp
  K_vanishes := fun _ => by
    ext x v; simp [pullbackForm]
  deg0_injectivity := fun β _ h => by
    rw [pullbackForm_id] at h; exact h
  smooth_forms_U := fun ω => contDiff_of_subsingleton_domain ω

end Instances
