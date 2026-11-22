/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

universe u

noncomputable section

open Module

section GoalTwentyFour

/-- Context for the $H_Ω ≃ k[Ω]$ structure result: an algebra $H$ over $k$ together
with a $k$-linearly independent monoid homomorphism `ch : Ω → H`. -/
structure BNPairOmegaContext (k : Type u) [CommRing k] (Ω : Type u) [Group Ω] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  ch : Ω → H
  ch_mul : ∀ σ τ : Ω, ch σ * ch τ = ch (σ * τ)
  ch_one : ch 1 = (1 : H)
  ch_linearIndependent : LinearIndependent k ch

attribute [instance] BNPairOmegaContext.algH BNPairOmegaContext.ringH

namespace BNPairOmegaContext

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω]
variable (ctx : BNPairOmegaContext k Ω)

/-- Packages `ch : Ω → H` as a monoid homomorphism. -/
def chMonoidHom : Ω →* ctx.H where
  toFun := ctx.ch
  map_one' := ctx.ch_one
  map_mul' σ τ := by rw [ctx.ch_mul]

/-- Induced $k$-algebra homomorphism $k[Ω] → H$ extending `chMonoidHom`. -/
def algHomOmega : MonoidAlgebra k Ω →ₐ[k] ctx.H :=
  MonoidAlgebra.lift k ctx.H Ω ctx.chMonoidHom

/-- Injectivity of the algebra map $k[Ω] → H$, which follows from linear independence of `ch`. -/
theorem algHomOmega_injective : Function.Injective ctx.algHomOmega := by
  intro x y hxy
  suffices h : ∀ (a : MonoidAlgebra k Ω), ctx.algHomOmega a = 0 → a = 0 by
    have := h (x - y) (by rw [map_sub]; exact sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp this
  intro a ha
  have hli := ctx.ch_linearIndependent
  rw [linearIndependent_iff] at hli
  apply hli
  rw [Finsupp.linearCombination_apply]
  simp only [algHomOmega, MonoidAlgebra.lift_apply, chMonoidHom] at ha
  exact ha

/-- The algebra isomorphism $k[Ω] ≃ₐ H_Ω$, where $H_Ω$ is the image subalgebra. -/
def HOmega_algEquiv : MonoidAlgebra k Ω ≃ₐ[k] (ctx.algHomOmega).range :=
  AlgEquiv.ofInjective ctx.algHomOmega ctx.algHomOmega_injective

end BNPairOmegaContext

end GoalTwentyFour


section GoalTwentyThree

/-- Full BN-pair context recording the data needed for the generalized Hecke-algebra
structure theorem $H ≅ k[Ω] ⊗ H_o$: characters of $Ω$ and $W$, an inclusion $H_o → H$,
a joint basis indexed by $Ω × W$, and the conjugation action `omegaConj`. -/
structure FullBNPairContext (k : Type u) [CommRing k] (Ω : Type u) [Group Ω]
    (W : Type u) [Group W] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  H_o : Type u
  [ringHo : Ring H_o]
  [algHo : Algebra k H_o]
  ch : Ω → H
  ch_o : W → H_o
  incl : H_o →ₐ[k] H
  ch_full : Ω × W → H
  H_basis : Basis (Ω × W) k H
  H_basis_eq : ∀ σw : Ω × W, H_basis σw = ch_full σw
  ch_full_one : ∀ σ : Ω, ch_full (σ, 1) = ch σ
  ch_full_incl : ∀ w : W, ch_full (1, w) = incl (ch_o w)
  omegaConj : Ω → W → W
  omegaConj_one : ∀ w : W, omegaConj 1 w = w
  omegaConj_mul : ∀ σ τ : Ω, ∀ w : W,
    omegaConj (σ * τ) w = omegaConj τ (omegaConj σ w)
  omegaConj_action_one : ∀ σ : Ω, omegaConj σ 1 = 1
  omegaConj_action_mul : ∀ σ : Ω, ∀ w w' : W,
    omegaConj σ (w * w') = omegaConj σ w * omegaConj σ w'
  ch_mul_omega : ∀ σ τ : Ω, ch σ * ch τ = ch (σ * τ)
  incl_mul : ∀ a b : H_o, incl (a * b) = incl a * incl b
  ch_one : ch 1 = (1 : H)
  ch_o_one : ch_o 1 = (1 : H_o)
  incl_one : incl 1 = (1 : H)

attribute [instance] FullBNPairContext.algH FullBNPairContext.ringH
  FullBNPairContext.algHo FullBNPairContext.ringHo




namespace FullBNPairContext

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω] {W : Type u} [Group W]
variable (ctx : FullBNPairContext k Ω W)










/-- Linear equivalence $H ≃ k^{(Ω × W)}$ given by the joint basis. -/
def structureIso : ctx.H ≃ₗ[k] (Ω × W →₀ k) :=
  ctx.H_basis.repr

/-- The joint character map `ch_full` is injective. -/
theorem ch_full_injective [Nontrivial k] : Function.Injective ctx.ch_full := by
  intro ⟨σ₁, w₁⟩ ⟨σ₂, w₂⟩ h
  have h₁ := ctx.H_basis_eq (σ₁, w₁)
  have h₂ := ctx.H_basis_eq (σ₂, w₂)
  rw [← h₁, ← h₂] at h
  exact ctx.H_basis.injective h


end FullBNPairContext

end GoalTwentyThree

end
