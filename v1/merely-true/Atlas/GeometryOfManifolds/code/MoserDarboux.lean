/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Atlas.GeometryOfManifolds.code.SymplecticEvenDim
import Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Atlas.GeometryOfManifolds.code.HamiltonianVectorFields

set_option autoImplicit false

universe u_chart v_chart

open Module FiniteDimensional Finset
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- The standard symplectic form on $\mathbb{R}^{2n} = \mathbb{R}^n \times \mathbb{R}^n$:
$\omega_0((p_1, q_1), (p_2, q_2)) = \sum_i (p_{1,i} q_{2,i} - p_{2,i} q_{1,i})$. -/
noncomputable def stdSymplForm (n : ℕ) :
    LinearMap.BilinForm ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ i : Fin n, (u.1 i * v.2 i - v.1 i * u.2 i))
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add]
        have key : ∀ i : Fin n, (u.1 + v.1) i * w.2 i - w.1 i * (u.2 + v.2) i =
          (u.1 i * w.2 i - w.1 i * u.2 i) + (v.1 i * w.2 i - w.1 i * v.2 i) := by
          intro i; simp [Pi.add_apply]; ring
        simp_rw [key, Finset.sum_add_distrib])
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd]
        have key : ∀ i : Fin n, (c • u.1) i * v.2 i - v.1 i * (c • u.2) i =
          c * (u.1 i * v.2 i - v.1 i * u.2 i) := by
          intro i; simp [Pi.smul_apply, smul_eq_mul]; ring
        simp_rw [key, ← Finset.mul_sum, smul_eq_mul])
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add]
        have key : ∀ i : Fin n, u.1 i * (v.2 + w.2) i - (v.1 + w.1) i * u.2 i =
          (u.1 i * v.2 i - v.1 i * u.2 i) + (u.1 i * w.2 i - w.1 i * u.2 i) := by
          intro i; simp [Pi.add_apply]; ring
        simp_rw [key, Finset.sum_add_distrib])
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd]
        have key : ∀ i : Fin n, u.1 i * (c • v.2) i - (c • v.1) i * u.2 i =
          c * (u.1 i * v.2 i - v.1 i * u.2 i) := by
          intro i; simp [Pi.smul_apply, smul_eq_mul]; ring
        simp_rw [key, ← Finset.mul_sum, smul_eq_mul])

/-- Unfolds the standard symplectic form to its explicit sum formula. -/
lemma stdSymplForm_apply (n : ℕ) (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    stdSymplForm n u v = ∑ i : Fin n, (u.1 i * v.2 i - v.1 i * u.2 i) := by
  simp [stdSymplForm, LinearMap.mk₂_apply]

/-- The standard symplectic form is alternating: $\omega_0(v, v) = 0$ for all $v$. -/
lemma stdSymplForm_alt (n : ℕ) : (stdSymplForm n).IsAlt := by
  intro v
  show ∑ i : Fin n, (v.1 i * v.2 i - v.1 i * v.2 i) = 0
  simp

/-- The standard symplectic form is nondegenerate (separating in its left argument):
if $\omega_0(x, \cdot) = 0$ then $x = 0$. -/
lemma stdSymplForm_separatingLeft (n : ℕ) : (stdSymplForm n).SeparatingLeft := by
  intro x hx
  have h1 : ∀ i : Fin n, x.1 i = 0 := by
    intro i
    have h := hx (0, Function.update 0 i 1)
    rw [stdSymplForm_apply] at h
    simp only [Pi.zero_apply, zero_mul, sub_zero] at h
    simpa [Finset.sum_ite_eq', Function.update_apply] using h
  have h2 : ∀ i : Fin n, x.2 i = 0 := by
    intro i
    have h := hx (Function.update 0 i 1, 0)
    rw [stdSymplForm_apply] at h
    simp only [Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero] at h
    simpa [Finset.sum_ite_eq', Function.update_apply] using h
  exact Prod.ext (funext h1) (funext h2)


/-- Expansion of a bilinear form in a basis $B$: $\Omega(u, v) = \sum_{i,j} u_i v_j \Omega(b_i, b_j)$,
where $u_i, v_j$ are the coordinates of $u, v$ in the basis. -/
lemma bilinForm_basis_expand {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] (Ω : LinearMap.BilinForm ℝ V) (B : Basis ι ℝ V) (u v : V) :
    Ω u v = ∑ i, ∑ j, (B.repr u i) * (B.repr v j) * Ω (B i) (B j) := by
  conv_lhs => rw [← B.sum_repr u]
  rw [LinearMap.BilinForm.sum_left]
  congr 1; ext i
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  conv_lhs => rw [← B.sum_repr v]
  rw [LinearMap.BilinForm.sum_right]
  rw [Finset.mul_sum]
  congr 1; ext j
  rw [map_smul, smul_eq_mul]
  ring

/-- **Linear Darboux theorem.** Every symplectic vector space $(V, \Omega)$ admits a linear
isomorphism $\varphi : V \cong \mathbb{R}^{2n}$ pulling back the standard symplectic
form: $\Omega(u, v) = \omega_0(\varphi u, \varphi v)$. -/
theorem linear_darboux {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω) :
    ∃ (n : ℕ) (φ : V ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ)),
      ∀ u v, Ω u v = stdSymplForm n (φ u) (φ v) := by

  obtain ⟨n, e, f, hdim, hee, hff, hef, hli, hspan⟩ := symplectic_standard_basis hΩ

  let B : Basis (Fin n ⊕ Fin n) ℝ V := Basis.mk hli hspan

  let ψ₁ : V ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := B.equivFun

  let ψ₂ : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℝ ℝ
  let φ : V ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ) := ψ₁.trans ψ₂
  refine ⟨n, φ, ?_⟩

  have hB : ∀ i, B i = Sum.elim e f i := fun i => Basis.mk_apply hli hspan i

  have hφ : ∀ v : V, φ v = (fun i => B.repr v (Sum.inl i), fun i => B.repr v (Sum.inr i)) := by
    intro v; rfl

  intro u v
  rw [stdSymplForm_apply, bilinForm_basis_expand Ω B u v]

  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, hB, Sum.elim_inl, Sum.elim_inr]


  simp only [hee, hff, mul_zero, Finset.sum_const_zero, add_zero, zero_add]


  have hfe : ∀ i j, Ω (f i) (e j) = if i = j then -1 else 0 := by
    intro i j
    rw [sympl_skew hΩ.alt (f i) (e j), hef j i]
    split
    · simp_all
    · simp_all [Ne.symm]
  simp only [hef, hfe]
  rw [hφ u, hφ v]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring


/-- Two symplectic forms $\omega_0, \omega_1$ are **deformation equivalent** if there is a
continuous family $\omega_t$ of symplectic $2$-forms connecting them (closed and nondegenerate
for $t \in [0, 1]$). -/
def IsDeformationEquivalent
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] [TopologicalSpace (Ω 2)]
    (ω₀ ω₁ : Ω 2) : Prop :=
  ∃ (ω : ℝ → Ω 2),
    Continuous ω ∧
    (∀ t ∈ Set.Icc 0 1, d VF (ω t) = 0) ∧
    (∀ t ∈ Set.Icc 0 1, Function.Injective (fun (X : VF) => ι X (ω t))) ∧
    ω 0 = ω₀ ∧ ω 1 = ω₁

/-- Two symplectic forms $\omega_0, \omega_1$ are **isotopic** if they are connected by a
continuous family $\omega_t$ of symplectic forms whose cohomology class is constant:
$[\omega_t - \omega_0] = 0$ in $H^2$, i.e., $\omega_t - \omega_0 = d\alpha$ for some $\alpha$. -/
def IsIsotopic
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] [TopologicalSpace (Ω 2)]
    (ω₀ ω₁ : Ω 2) : Prop :=
  ∃ (ω : ℝ → Ω 2),
    Continuous ω ∧
    (∀ t ∈ Set.Icc 0 1, d VF (ω t) = 0) ∧
    (∀ t ∈ Set.Icc 0 1, Function.Injective (fun (X : VF) => ι X (ω t))) ∧
    ω 0 = ω₀ ∧ ω 1 = ω₁ ∧
    (∀ t ∈ Set.Icc 0 1, ∃ α : Ω 1, ω t - ω₀ = d VF α)

/-- Isotopy implies deformation equivalence: forgetting the cohomological condition. -/
theorem IsIsotopic.toIsDeformationEquivalent
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] [TopologicalSpace (Ω 2)]
    {ω₀ ω₁ : Ω 2} (h : IsIsotopic (VF := VF) ω₀ ω₁) :
    IsDeformationEquivalent (VF := VF) ω₀ ω₁ := by
  obtain ⟨ω, hcont, hclosed, hnd, h0, h1, _⟩ := h
  exact ⟨ω, hcont, hclosed, hnd, h0, h1⟩


/-- Setup data for **Moser's trick**: a smooth path of closed $2$-forms $\omega_t$ with time
derivative $\dot\omega_t$, primitives $\alpha_t$ satisfying $d\alpha_t = \dot\omega_t$, and
the canonically-induced vector fields $X_t$ solving $\iota_{X_t} \omega_t = -\alpha_t$. -/
structure MoserSetup {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  ω_t : ℝ → Ω 2
  closed_t : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → inst.d (ω_t t) = 0
  α_t : ℝ → Ω 1
  dω_dt : ℝ → Ω 2
  derivative_consistency : ∀ t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
    ω_t s - ω_t t = (s - t) • dω_dt t
  defining_eq : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → inst.d (α_t t) = dω_dt t
  X_t : ℝ → VF
  X_t_eq : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → inst.ι (X_t t) (ω_t t) = -(α_t t)

/-- **Cartan's formula in Moser's setup**: $\mathcal{L}_{X_t} \omega_t = -d\alpha_t$,
derived from $\iota_{X_t} \omega_t = -\alpha_t$ and $d\omega_t = 0$. -/
theorem moser_lie_deriv_eq
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (setup : MoserSetup (Ω := Ω) (VF := VF)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inst.L (setup.X_t t) (setup.ω_t t) = -(inst.d (setup.α_t t)) := by
  rw [cartan_formula (setup.X_t t) (setup.ω_t t)]
  rw [setup.X_t_eq t ht]
  rw [setup.closed_t t ht, ι_zero_val, add_zero]

  have hd_neg : inst.d (-(setup.α_t t)) = -(inst.d (setup.α_t t)) := by
    have := inst.d_smul (-1 : ℝ) (setup.α_t t)
    simp at this
    exact this
  exact hd_neg

/-- The isotopy $\rho_t$ generated by the Moser vector field $X_t$: a time-dependent family of
pullback morphisms with $\rho_0 = \mathrm{id}$ satisfying the flow ODE
$\frac{d}{dt}\rho_t^*\omega_t = \rho_t^*(\mathcal{L}_{X_t}\omega_t + \dot\omega_t)$, so that if
this derivative vanishes then $\rho_t^*\omega_t \equiv \omega_0$. -/
structure MoserFlow {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (setup : MoserSetup (Ω := Ω) (VF := VF)) where
  ρ : ℝ → DFSMorphism Ω VF Ω VF
  ρ_zero : ∀ {p : ℕ} (α : Ω p), (ρ 0).pullback α = α
  pullback_deriv : ℝ → Ω 2
  flow_ode : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → pullback_deriv t = (ρ t).pullback (inst.L (setup.X_t t) (setup.ω_t t) + setup.dω_dt t)
  deriv_zero_const : (∀ t, t ∈ Set.Icc (0 : ℝ) 1 → pullback_deriv t = 0) →
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (ρ t).pullback (setup.ω_t t) = setup.ω_t 0

/-- The Moser **transport equation** is satisfied: $\mathcal{L}_{X_t}\omega_t + \dot\omega_t = 0$,
combining Cartan's formula with $d\alpha_t = \dot\omega_t$. -/
theorem moser_transport_zero
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (setup : MoserSetup (Ω := Ω) (VF := VF)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inst.L (setup.X_t t) (setup.ω_t t) + setup.dω_dt t = 0 := by
  rw [moser_lie_deriv_eq setup t ht, setup.defining_eq t ht]
  exact neg_add_cancel _

/-- Under the Moser transport equation, the flow pulls back $\omega_t$ to a constant:
$\rho_t^* \omega_t = \omega_0$ for all $t \in [0,1]$. -/
theorem moser_flow_transport_const
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (setup : MoserSetup (Ω := Ω) (VF := VF))
    (flow : MoserFlow setup) :
    (∀ t, t ∈ Set.Icc (0 : ℝ) 1 → inst.L (setup.X_t t) (setup.ω_t t) + setup.dω_dt t = 0) →
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (flow.ρ t).pullback (setup.ω_t t) = setup.ω_t 0 := by
  intro htransport
  apply flow.deriv_zero_const
  intro t ht
  rw [flow.flow_ode t ht, htransport t ht]

  have := (flow.ρ t).pullback_smul (0 : ℝ) (0 : Ω 2)
  simp [zero_smul] at this
  exact this

/-- **Moser's theorem**: the isotopy $\rho_t$ satisfies $\rho_0 = \mathrm{id}$ and
$\rho_t^*\omega_t = \omega_0$ for all $t \in [0, 1]$, giving a diffeomorphism trivializing the
family of symplectic forms. -/
theorem moser_theorem
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (setup : MoserSetup (Ω := Ω) (VF := VF))
    (flow : MoserFlow setup) :
    (∀ {p : ℕ} (α : Ω p), (flow.ρ 0).pullback α = α) ∧
    (∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (flow.ρ t).pullback (setup.ω_t t) = setup.ω_t 0) :=
  ⟨flow.ρ_zero, moser_flow_transport_const setup flow (fun t ht => moser_transport_zero setup t ht)⟩

/-- The convex combination $(1 - t)\omega_0 + t\omega_1$ of two closed $2$-forms is closed. -/
lemma interpolating_closed
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (ω₀ ω₁ : Ω 2) (hclosed₀ : inst.d ω₀ = 0) (hclosed₁ : inst.d ω₁ = 0)
    (t : ℝ) :
    inst.d ((1 - t) • ω₀ + t • ω₁) = 0 := by
  rw [inst.d_add, inst.d_smul, inst.d_smul, hclosed₀, hclosed₁,
      smul_zero, smul_zero, add_zero]

/-- Interior product distributes over convex combinations:
$\iota_X((1-t)\omega_0 + t\omega_1) = (1-t)\iota_X\omega_0 + t\iota_X\omega_1$. -/
lemma contraction_interpolation
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (X : VF) (ω₀ ω₁ : Ω 2) (t : ℝ) :
    inst.ι X ((1 - t) • ω₀ + t • ω₁) = (1 - t) • inst.ι X ω₀ + t • inst.ι X ω₁ := by
  rw [inst.ι_add, inst.ι_smul, inst.ι_smul]

/-- Endpoint of the interpolated contraction at $t = 0$: recovers $\iota_X \omega_0$. -/
lemma contraction_interpolation_zero
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (X : VF) (ω₀ ω₁ : Ω 2) :
    inst.ι X ((1 - (0 : ℝ)) • ω₀ + (0 : ℝ) • ω₁) = inst.ι X ω₀ := by
  rw [contraction_interpolation]
  simp

/-- Endpoint of the interpolated contraction at $t = 1$: recovers $\iota_X \omega_1$. -/
lemma contraction_interpolation_one
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (X : VF) (ω₀ ω₁ : Ω 2) :
    inst.ι X ((1 - (1 : ℝ)) • ω₀ + (1 : ℝ) • ω₁) = inst.ι X ω₁ := by
  rw [contraction_interpolation]
  simp

/-- Axiomatization of finite-dimensional behavior of the interior-product map: for a
nondegenerate $2$-form $\omega$, the map $X \mapsto \iota_X\omega$ is bijective, and the
interpolation $(1 - t)\omega_0 + t\omega_1$ of two nondegenerate closed forms remains
nondegenerate for $t \in [0, 1]$. -/
class HasFiniteDimContraction (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  contraction_surjective_of_injective :
    ∀ (ω : Ω 2), Function.Injective (fun X => inst.ι X ω) →
      Function.Surjective (fun X => inst.ι X ω)
  interpolated_contraction_injective :
    ∀ (ω₀ ω₁ : Ω 2),
      inst.d ω₀ = 0 → inst.d ω₁ = 0 →
      Function.Injective (fun X => inst.ι X ω₀) →
      Function.Injective (fun X => inst.ι X ω₁) →
      ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁))

/-- Nondegeneracy of $(1 - t)\omega_0 + t\omega_1$ for $t \in [0, 1]$ when $\omega_0, \omega_1$
are closed and nondegenerate (uses the `HasFiniteDimContraction` axiom). -/
theorem interpolated_form_nondegenerate
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    [hfdc : HasFiniteDimContraction Ω VF]
    (ω₀ ω₁ : Ω 2)
    (hclosed₀ : inst.d ω₀ = 0) (hclosed₁ : inst.d ω₁ = 0)
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
    (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁)) :=
  hfdc.interpolated_contraction_injective ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht

/-- For the interpolated form $(1 - t)\omega_0 + t\omega_1$, the contraction
$X \mapsto \iota_X((1-t)\omega_0 + t\omega_1)$ is surjective onto $\Omega^1$. -/
theorem interpolated_form_contraction_surjective
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    [hfdc : HasFiniteDimContraction Ω VF]
    (ω₀ ω₁ : Ω 2)
    (hclosed₀ : inst.d ω₀ = 0) (hclosed₁ : inst.d ω₁ = 0)
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
    (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Function.Surjective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁)) :=
  hfdc.contraction_surjective_of_injective _
    (interpolated_form_nondegenerate (hfdc := hfdc) ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht)

/-- For the local Moser construction: given $d\alpha = \omega_1 - \omega_0$, one can solve
$\iota_X((1 - t)\omega_0 + t\omega_1) = -\alpha$ for a vector field $X$ at each $t \in [0, 1]$. -/
theorem local_moser_interior_product_solvable
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    [hfdc : HasFiniteDimContraction Ω VF]
    (ω₀ ω₁ : Ω 2) (α : Ω 1)
    (hclosed₀ : inst.d ω₀ = 0) (hclosed₁ : inst.d ω₁ = 0)
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
    (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
    (_hα : inst.d α = ω₁ - ω₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (X : VF), inst.ι X ((1 - t) • ω₀ + t • ω₁) = -α := by
  exact interpolated_form_contraction_surjective ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht (-α)


/-- **Local Moser theorem.** Given closed nondegenerate $\omega_0, \omega_1$ with
$\omega_1 - \omega_0 = d\alpha$ exact, there exists a diffeomorphism $\varphi$ with
$\varphi^*\omega_1 = \omega_0$. -/
theorem local_moser_theorem
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    [hfdc : HasFiniteDimContraction Ω VF]
    (ω₀ ω₁ : Ω 2)
    (hclosed₀ : inst.d ω₀ = 0) (hclosed₁ : inst.d ω₁ = 0)
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
    (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
    (hcohom : ∃ α : Ω 1, inst.d α = ω₁ - ω₀)

    (hflow_exists : ∀ (s : MoserSetup (Ω := Ω) (VF := VF)), MoserFlow s) :
    ∃ (φ : DFSMorphism Ω VF Ω VF), φ.pullback ω₁ = ω₀ := by
  obtain ⟨α, hα⟩ := hcohom

  have hsolve : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∃ (X : VF), inst.ι X ((1 - t) • ω₀ + t • ω₁) = -α :=
    fun t ht => local_moser_interior_product_solvable ω₀ ω₁ α hclosed₀ hclosed₁ hnd₀ hnd₁ hα t ht


  have hinst : Nonempty VF := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    exact ⟨(hsolve 0 h0).choose⟩
  let X_t : ℝ → VF := fun t =>
    if h : t ∈ Set.Icc (0 : ℝ) 1 then (hsolve t h).choose else Classical.arbitrary VF
  have hX_t : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
      inst.ι (X_t t) ((1 - t) • ω₀ + t • ω₁) = -α := by
    intro t ht
    simp only [X_t, dif_pos ht]
    exact (hsolve t ht).choose_spec

  let setup : MoserSetup (Ω := Ω) (VF := VF) :=
    { ω_t := fun t => (1 - t) • ω₀ + t • ω₁
      closed_t := fun t _ => interpolating_closed ω₀ ω₁ hclosed₀ hclosed₁ t
      α_t := fun _ => α
      dω_dt := fun _ => ω₁ - ω₀
      derivative_consistency := by
        intro t s _ _
        simp [smul_sub, sub_smul]
        abel
      defining_eq := fun _ _ => hα
      X_t := X_t
      X_t_eq := hX_t }

  let flow : MoserFlow setup := hflow_exists setup

  have hmoser := moser_theorem setup flow

  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have htransport := hmoser.2 1 h1_mem

  have hω1 : setup.ω_t 1 = ω₁ := by simp [setup]

  have hω0 : setup.ω_t 0 = ω₀ := by simp [setup]
  rw [hω1, hω0] at htransport
  exact ⟨flow.ρ 1, htransport⟩

/-- Composition of DFS morphisms: given $f : (\Omega_1, VF_1) \to (\Omega_2, VF_2)$ and
$g : (\Omega_2, VF_2) \to (\Omega_3, VF_3)$, the composite pulls back via $g$ then $f$. -/
def DFSMorphism.comp
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω₃ : ℕ → Type*} {VF₃ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst₃ : DifferentialFormSpace Ω₃ VF₃]
    (g : DFSMorphism Ω₂ VF₂ Ω₃ VF₃)
    (f : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) :
    DFSMorphism Ω₁ VF₁ Ω₃ VF₃ where
  pullback α := f.pullback (g.pullback α)
  pullback_add α β := by rw [g.pullback_add, f.pullback_add]
  pullback_smul r α := by rw [g.pullback_smul, f.pullback_smul]
  pullback_comm_d α := by rw [g.pullback_comm_d, f.pullback_comm_d]





universe u_M v_M u_X v_X


/-- Relative Moser data along a submanifold inclusion $i : X \hookrightarrow M$: charts $U_0, U_1$
around $X$ and a diffeomorphism $\varphi : U_0 \to U_1$ pulling $\omega_1$ to $\omega_0$ while
restricting to the identity on $X$. Encodes the local statement underlying relative versions
of Moser's theorem (e.g., the relative Darboux/Weinstein neighborhood theorems). -/
structure HasMoserFlowData
    {Ω_M : ℕ → Type u_M} {VF_M : Type v_M}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    {Ω_X : ℕ → Type u_X} {VF_X : Type v_X}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (ω₀ ω₁ : Ω_M 2) where
  Ω_U₀ : ℕ → Type u_M
  VF_U₀ : Type v_M
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  incl₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M inst_U₀ inst_M
  i_X_U₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  Ω_U₁ : ℕ → Type u_M
  VF_U₁ : Type v_M
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  incl₁ : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  i_X_U₁ : @DFSMorphism Ω_X VF_X Ω_U₁ VF_U₁ inst_X inst_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  compat₀ : ∀ {p : ℕ} (α : Ω_M p), i_X_U₀.pullback (incl₀.pullback α) = i.pullback α
  compat₁ : ∀ {p : ℕ} (α : Ω_M p), i_X_U₁.pullback (incl₁.pullback α) = i.pullback α
  pullback_eq : φ.pullback (incl₁.pullback ω₁) = incl₀.pullback ω₀
  φ_identity_on_X : ∀ {p : ℕ} (α : Ω_U₁ p),
      i_X_U₀.pullback (φ.pullback α) = i_X_U₁.pullback α
  φ_inv_left : ∀ {p : ℕ} (α : Ω_U₁ p),
      φ_inv.pullback (φ.pullback α) = α
  φ_inv_right : ∀ {p : ℕ} (α : Ω_U₀ p),
      φ.pullback (φ_inv.pullback α) = α
  φ_inv_identity_on_X : ∀ {p : ℕ} (α : Ω_U₀ p),
      i_X_U₁.pullback (φ_inv.pullback α) = i_X_U₀.pullback α
