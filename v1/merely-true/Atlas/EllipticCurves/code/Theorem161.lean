/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Lattice
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Group.Quotient

namespace ComplexLattice

noncomputable section

open Pointwise Function ZSpan

/-- The complex torus `ℂ / L` associated to a lattice `L ⊆ ℂ`. -/
abbrev torusQuot (L : ComplexLattice) : Type :=
  ℂ ⧸ L.lattice.toAddSubgroup

/-- The canonical quotient map `ℂ → ℂ / L`, as an additive group homomorphism. -/
def proj (L : ComplexLattice) : ℂ →+ torusQuot L :=
  QuotientAddGroup.mk' L.lattice.toAddSubgroup

/-- Two complex numbers project to the same point in `ℂ / L` iff they differ by a lattice element. -/
theorem proj_eq_iff (L : ComplexLattice) (z w : ℂ) :
    proj L z = proj L w ↔ ∃ v ∈ L.lattice.toAddSubgroup, z + v = w :=
  QuotientAddGroup.mk'_eq_mk' L.lattice.toAddSubgroup

/-- A complex number projects to `0` in `ℂ / L` iff it lies in the lattice `L`. -/
theorem proj_eq_zero_iff (L : ComplexLattice) (z : ℂ) :
    proj L z = 0 ↔ z ∈ L.lattice.toAddSubgroup :=
  QuotientAddGroup.eq_zero_iff z

/-- The set `{ α ∈ ℂ : α L₁ ⊆ L₂ }` of scalars whose multiplication sends `L₁` into `L₂`. -/
def latticeMulSet (L₁ L₂ : ComplexLattice) : Set ℂ :=
  { α : ℂ | ∀ z ∈ (L₁.lattice : Set ℂ), α * z ∈ (L₂.lattice : Set ℂ) }

/-- The scalar `0` always sends `L₁` into `L₂`, so it lies in `latticeMulSet`. -/
theorem zero_mem_latticeMulSet (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ := by
  intro z _; simp [L₂.lattice.zero_mem]

/-- Membership in `latticeMulSet L₁ L₂` unfolds to the condition `α z ∈ L₂` for every `z ∈ L₁`. -/
@[simp]
theorem mem_latticeMulSet_iff {L₁ L₂ : ComplexLattice} {α : ℂ} :
    α ∈ latticeMulSet L₁ L₂ ↔
      ∀ z ∈ (L₁.lattice : Set ℂ), α * z ∈ (L₂.lattice : Set ℂ) :=
  Iff.rfl

/-- Multiplication by a fixed `α : ℂ` packaged as an additive group homomorphism `ℂ →+ ℂ`. -/
def mulByAlphaHom (α : ℂ) : ℂ →+ ℂ where
  toFun z := α * z
  map_zero' := mul_zero α
  map_add' x y := mul_add α x y

/-- For `α ∈ latticeMulSet L₁ L₂`, the induced morphism `ℂ / L₁ → ℂ / L₂` between complex tori
obtained by passing multiplication-by-`α` to the quotient. -/
def inducedMap (L₁ L₂ : ComplexLattice) (α : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) :
    torusQuot L₁ →+ torusQuot L₂ :=
  QuotientAddGroup.lift L₁.lattice.toAddSubgroup
    ((proj L₂).comp (mulByAlphaHom α))
    (fun z hz => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, proj,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mulByAlphaHom]
      exact hα z hz)

/-- The induced map applied to `proj L₁ z` equals `proj L₂ (α * z)`. -/
@[simp]
theorem inducedMap_proj (L₁ L₂ : ComplexLattice) (α : ℂ) (hα : α ∈ latticeMulSet L₁ L₂)
    (z : ℂ) :
    inducedMap L₁ L₂ α hα (proj L₁ z) = proj L₂ (α * z) := by
  simp only [inducedMap, proj, mulByAlphaHom, QuotientAddGroup.lift_mk',
    AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    QuotientAddGroup.mk'_apply]

/-- A holomorphic morphism between complex tori `ℂ / L₁ → ℂ / L₂`, packaged together with a
holomorphic lift `ℂ → ℂ` making the projection diagram commute. -/
structure ComplexTorusHolMap (L₁ L₂ : ComplexLattice) where
  toFun : torusQuot L₁ → torusQuot L₂
  lift : ℂ → ℂ
  lift_differentiable : Differentiable ℂ lift
  diagram_commutes : ∀ z : ℂ, toFun (proj L₁ z) = proj L₂ (lift z)

/-- A continuous function from `ℂ` (connected) to a lattice (discrete) must be constant. -/
theorem const_of_continuous_latticeValued (L : ComplexLattice) (g : ℂ → ℂ)
    (hg : Continuous g) (himg : ∀ z, g z ∈ (L.lattice : Set ℂ)) :
    ∀ x y, g x = g y := by
  let g' : ℂ → L.lattice := fun z => ⟨g z, himg z⟩
  have hg' : Continuous g' := continuous_induced_rng.mpr hg
  intro x y
  have h := @PreconnectedSpace.constant ℂ _ L.lattice _ _ inferInstance g' hg' x y
  exact congrArg Subtype.val h

/-- If `f(z + ω) = f(z) + c` for a constant `c`, then the derivative of `f` is `ω`-periodic. -/
theorem deriv_periodic_of_shift_const (f : ℂ → ℂ)
    (ω : ℂ) (c : ℂ) (hc : ∀ z, f (z + ω) = f z + c) :
    ∀ z, deriv f (z + ω) = deriv f z := by
  intro z
  have h1 : deriv (fun x => f (x + ω)) z = deriv f (z + ω) := deriv_comp_add_const f ω z
  have h2 : deriv (fun x => f x + c) z = deriv f z := deriv_add_const c
  have h3 : (fun x => f (x + ω)) = (fun x => f x + c) := funext hc
  rw [← h1, ← h2, h3]

/-- A differentiable function on `ℂ` with constant derivative `α` is affine: `f(z) = α z + f(0)`. -/
theorem affine_of_const_deriv (f : ℂ → ℂ) (hf : Differentiable ℂ f) (α : ℂ)
    (hderiv_eq : ∀ w, deriv f w = α) :
    ∀ z, f z = α * z + f 0 := by
  intro z
  let g : ℂ → ℂ := fun z => f z - (α * z + f 0)
  suffices h : g z = g 0 by
    simp only [g, mul_zero, zero_add, sub_self] at h
    linear_combination h
  apply is_const_of_deriv_eq_zero
  · exact hf.sub ((differentiable_const α).mul differentiable_id |>.add (differentiable_const _))
  · intro w
    have hfw : HasDerivAt f α w := by rw [← hderiv_eq]; exact (hf w).hasDerivAt
    have haw : HasDerivAt (fun z => α * z + f 0) α w := by
      have h1 : HasDerivAt (fun z => α * z) α w := by
        have := (hasDerivAt_id w).const_mul α
        simp only [mul_one] at this; exact this
      simpa only [add_zero] using h1.add (hasDerivAt_const w (f 0))
    have : HasDerivAt g 0 w := by
      simpa only [sub_self] using hfw.sub haw
    exact this.deriv

/-- A function periodic with respect to the two generators `ω₁, ω₂` of a lattice `L` is periodic
with respect to every element of `L`. -/
theorem periodic_of_generators (f : ℂ → ℂ) (L : ComplexLattice)
    (hp1 : Periodic f L.ω₁) (hp2 : Periodic f L.ω₂) :
    ∀ z w, w ∈ L.lattice → f (z + w) = f z := by
  intro z w hw
  rw [ComplexLattice.mem_lattice_iff] at hw
  obtain ⟨n₁, n₂, rfl⟩ := hw

  have hper1 : Periodic f ((n₁ : ℂ) * L.ω₁) := hp1.int_mul n₁
  have hper2 : Periodic f ((n₂ : ℂ) * L.ω₂) := hp2.int_mul n₂
  calc f (z + ((n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂))
      = f (z + (n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂) := by rw [add_assoc]
    _ = f (z + (n₁ : ℂ) * L.ω₁) := hper2 _
    _ = f z := hper1 _

/-- An entire function that is doubly periodic with respect to a lattice has bounded range
(the key input for Liouville's theorem). -/
theorem entire_periodic_isBounded_range
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (L : ComplexLattice)
    (hp1 : Periodic f L.ω₁) (hp2 : Periodic f L.ω₂) :
    Bornology.IsBounded (Set.range f) := by
  have hper : ∀ z w, w ∈ L.lattice → f (z + w) = f z :=
    periodic_of_generators f L hp1 hp2
  exact (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous hper).isBounded

/-- Existence half of Theorem 16.1: every holomorphic morphism `ℂ / L₁ → ℂ / L₂` sending `0` to `0`
arises from multiplication by some `α ∈ ℂ` with `α L₁ ⊆ L₂`. -/
theorem theorem_16_1_existence (L₁ L₂ : ComplexLattice)
    (φ : ComplexTorusHolMap L₁ L₂) (hφ0 : φ.toFun 0 = 0) :
    ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂,
      ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) := by
  set f := φ.lift with hf_def
  have hf := φ.lift_differentiable
  have hcomm := φ.diagram_commutes

  have hshift : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, f (z + ω) - f z ∈ (L₂.lattice : Set ℂ) := by
    intro ω hω z
    have hπ : proj L₁ (z + ω) = proj L₁ z := by
      rw [map_add]
      have : proj L₁ ω = 0 := (proj_eq_zero_iff L₁ ω).mpr hω
      rw [this, add_zero]
    have : proj L₂ (f (z + ω)) = proj L₂ (f z) := by
      rw [← hcomm (z + ω), ← hcomm z, hπ]
    rw [← sub_eq_zero, ← map_sub, proj_eq_zero_iff] at this
    exact this

  have hconst : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, f (z + ω) - f z = f ω - f 0 := by
    intro ω hω z
    have hcont : Continuous (fun z => f (z + ω) - f z) :=
      (hf.comp (differentiable_id.add (differentiable_const ω))).continuous.sub hf.continuous
    have := const_of_continuous_latticeValued L₂ _ hcont (hshift ω hω) z 0
    simp only [zero_add] at this
    exact this

  have hderiv_per : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, deriv f (z + ω) = deriv f z := by
    intro ω hω z
    apply deriv_periodic_of_shift_const f ω (f ω - f 0) (fun w => ?_) z
    have := hconst ω hω w
    linear_combination this

  have hp1 : Periodic (deriv f) L₁.ω₁ :=
    fun z => hderiv_per L₁.ω₁ (ComplexLattice.ω₁_mem L₁) z
  have hp2 : Periodic (deriv f) L₁.ω₂ :=
    fun z => hderiv_per L₁.ω₂ (ComplexLattice.ω₂_mem L₁) z

  have hdf : Differentiable ℂ (deriv f) :=
    (hf.contDiff (n := 2)).differentiable_deriv_two

  have hbdd := entire_periodic_isBounded_range (deriv f) hdf L₁ hp1 hp2

  have hconst_deriv : ∀ z w, deriv f z = deriv f w :=
    fun z w => hdf.apply_eq_apply_of_bounded hbdd z w

  set α := deriv f 0
  have haffine := affine_of_const_deriv f hf α (fun w => hconst_deriv w 0)

  have hf0 : f 0 ∈ (L₂.lattice : Set ℂ) := by
    have : proj L₂ (f 0) = 0 := by rw [← hcomm 0, map_zero, hφ0]
    rwa [proj_eq_zero_iff] at this

  have hα_mem : α ∈ latticeMulSet L₁ L₂ := by
    intro ω hω

    have hfω_sub : f ω - f 0 ∈ (L₂.lattice : Set ℂ) := by
      have := hshift ω hω 0; simp only [zero_add] at this; exact this
    have : f ω - f 0 = α * ω := by
      have := haffine ω; linear_combination this
    rwa [this] at hfω_sub

  refine ⟨α, hα_mem, fun z => ?_⟩
  show φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα_mem (proj L₁ z)
  rw [hcomm z, inducedMap_proj]
  have hfz : φ.lift z = α * z + f 0 := haffine z
  rw [hfz, map_add]
  have : proj L₂ (f 0) = 0 := (proj_eq_zero_iff L₂ (f 0)).mpr hf0
  rw [this, add_zero]

/-- The scalar `α` such that `inducedMap α = inducedMap γ` on all of `ℂ / L₁` is uniquely
determined. -/
theorem inducedMap_unique (L₁ L₂ : ComplexLattice) (α γ : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂)
    (heq : ∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) =
                      inducedMap L₁ L₂ γ hγ (proj L₁ z)) :
    α = γ := by

  have hproj : ∀ z, proj L₂ (α * z) = proj L₂ (γ * z) := by
    intro z; rw [← inducedMap_proj L₁ L₂ α hα, ← inducedMap_proj L₁ L₂ γ hγ]; exact heq z

  have hdiff : ∀ z, (α - γ) * z ∈ (L₂.lattice : Set ℂ) := by
    intro z
    have h := hproj z
    rw [proj_eq_iff] at h
    obtain ⟨v, hv, hvz⟩ := h
    have hv_eq : (α - γ) * z = -v := by
      have : v = γ * z - α * z := by linear_combination hvz
      rw [this]; ring
    rw [hv_eq]
    exact L₂.lattice.toAddSubgroup.neg_mem hv

  have hconst := const_of_continuous_latticeValued L₂ (fun z => (α - γ) * z)
    (continuous_const.mul continuous_id) hdiff

  have h0 := hconst 1 0
  simp only [mul_one, mul_zero] at h0

  exact sub_eq_zero.mp h0

/-- Theorem 16.1 (Sutherland): The map `{α ∈ ℂ : α L₁ ⊆ L₂} → Hom(ℂ/L₁, ℂ/L₂)` sending
`α ↦ φ_α` is an isomorphism — i.e., every holomorphic torus morphism sending `0` to `0` is
uniquely induced by some such scalar `α`. -/
theorem theorem_16_1 (L₁ L₂ : ComplexLattice)
    (φ : ComplexTorusHolMap L₁ L₂) (hφ0 : φ.toFun 0 = 0) :
    ∃! α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂,
      ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) := by
  obtain ⟨α, hα, hφα⟩ := theorem_16_1_existence L₁ L₂ φ hφ0
  refine ⟨α, ⟨hα, hφα⟩, ?_⟩
  intro γ ⟨hγ, hφγ⟩
  exact (inducedMap_unique L₁ L₂ α γ hα hγ (fun z => by rw [← hφα z, ← hφγ z])).symm

/-- The set `latticeMulSet L₁ L₂` is closed under addition (it is an additive subgroup of `ℂ`). -/
theorem add_mem_latticeMulSet (L₁ L₂ : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    α + β ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  have : (α + β) * z = α * z + β * z := add_mul α β z
  rw [this]
  exact L₂.lattice.add_mem (hα z hz) (hβ z hz)

/-- The induced map is additive in the scalar: `inducedMap (α + β) = inducedMap α + inducedMap β`
on every projected point. -/
theorem inducedMap_add_proj (L₁ L₂ : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    ∀ z : ℂ, inducedMap L₁ L₂ (α + β) (add_mem_latticeMulSet L₁ L₂ α β hα hβ) (proj L₁ z) =
      inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z) := by
  intro z
  simp only [inducedMap_proj]
  rw [show (α + β) * z = α * z + β * z from add_mul α β z]
  exact map_add (proj L₂) (α * z) (β * z)

/-- Conjunction packaging the four properties witnessing that `α ↦ φ_α` is an additive group
isomorphism `latticeMulSet L₁ L₂ ≃+ Hom(ℂ/L₁, ℂ/L₂)`: additivity, sending `0 ↦ 0`, injectivity,
and surjectivity (Theorem 16.1). -/
theorem latticeMulSet_to_torusMorphism_addGroupIso (L₁ L₂ : ComplexLattice) :

    (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂),
      ∀ z : ℂ, inducedMap L₁ L₂ (α + β) (add_mem_latticeMulSet L₁ L₂ α β hα hβ) (proj L₁ z) =
        inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z)) ∧

    (∀ z : ℂ, inducedMap L₁ L₂ 0 (zero_mem_latticeMulSet L₁ L₂) (proj L₁ z) = 0) ∧

    (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂),
      (∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) =
                 inducedMap L₁ L₂ γ hγ (proj L₁ z)) → α = γ) ∧

    (∀ (φ : ComplexTorusHolMap L₁ L₂), φ.toFun 0 = 0 →
      ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂,
        ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z)) := by
  refine ⟨fun α β hα hβ => inducedMap_add_proj L₁ L₂ α β hα hβ, fun z => ?_,
    fun α γ hα hγ => inducedMap_unique L₁ L₂ α γ hα hγ,
    fun φ hφ0 => theorem_16_1_existence L₁ L₂ φ hφ0⟩
  simp only [inducedMap_proj, zero_mul, map_zero]

/-- When `L₁ = L₂ = L`, the set `latticeMulSet L L` is closed under multiplication
(it is a subring of `ℂ`, the endomorphism ring of `ℂ / L`). -/
theorem mul_mem_latticeMulSet (L : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L) :
    α * β ∈ latticeMulSet L L := by
  intro z hz
  have : α * β * z = α * (β * z) := mul_assoc α β z
  rw [this]
  exact hα (β * z) (hβ z hz)

/-- The scalar `1` lies in `latticeMulSet L L`, corresponding to the identity endomorphism. -/
theorem one_mem_latticeMulSet (L : ComplexLattice) :
    (1 : ℂ) ∈ latticeMulSet L L := by
  intro z hz; simp; exact hz

/-- Composition of induced endomorphisms corresponds to multiplication of scalars:
`inducedMap (α β) = inducedMap α ∘ inducedMap β`. This gives the ring-isomorphism structure
when `L₁ = L₂`. -/
theorem inducedMap_comp (L : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L) :
    ∀ z : ℂ, inducedMap L L (α * β) (mul_mem_latticeMulSet L α β hα hβ) (proj L z) =
      (inducedMap L L α hα) (inducedMap L L β hβ (proj L z)) := by
  intro z
  simp only [inducedMap_proj]
  rw [show α * β * z = α * (β * z) from mul_assoc α β z]

end

end ComplexLattice
