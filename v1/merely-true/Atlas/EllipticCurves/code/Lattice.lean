/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.ZLattice.Basic

open Complex Module ZSpan Set

noncomputable section

/-- A complex lattice is identified with a `PeriodPair`: a pair `(ω₁, ω₂)` of complex
numbers that are linearly independent over `ℝ`, generating a rank-`2` `ℤ`-lattice in `ℂ`. -/
abbrev ComplexLattice := PeriodPair

namespace ComplexLattice

variable (L : ComplexLattice)

/-- Construct a complex lattice from two periods `ω₁`, `ω₂ : ℂ` together with a proof
that they are linearly independent over `ℝ`. -/
def mk' (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) : ComplexLattice :=
  PeriodPair.mk ω₁ ω₂ h

/-- The two periods `ω₁`, `ω₂` of a complex lattice are linearly independent over `ℝ`. -/
theorem linearIndependent : LinearIndependent ℝ ![L.ω₁, L.ω₂] :=
  L.indep

/-- A complex number `x` lies in the lattice `L` iff it has an integer expression
`n₁ ω₁ + n₂ ω₂` in terms of the lattice's periods. -/
theorem mem_lattice_iff {x : ℂ} :
    x ∈ L.lattice ↔ ∃ n₁ n₂ : ℤ, (n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂ = x :=
  PeriodPair.mem_lattice

/-- The first period `ω₁` belongs to the lattice `L`. -/
theorem ω₁_mem : L.ω₁ ∈ L.lattice := L.ω₁_mem_lattice

/-- The second period `ω₂` belongs to the lattice `L`. -/
theorem ω₂_mem : L.ω₂ ∈ L.lattice := L.ω₂_mem_lattice

/-- The subgroup underlying a complex lattice carries the discrete topology induced from `ℂ`. -/
instance discreteTopology_lattice : DiscreteTopology L.lattice := inferInstance

/-- A complex lattice is a `ℤ`-lattice in `ℂ` (viewed as an `ℝ`-vector space). -/
instance isZLattice_lattice : IsZLattice ℝ L.lattice := inferInstance

/-- The complex lattice has `ℤ`-rank equal to `2`. -/
theorem finrank_eq_two : finrank ℤ L.lattice = 2 := L.finrank_lattice

/-- A `ℤ`-basis of the lattice of size `2`, given by the two periods of `L`. -/
def intBasis : Module.Basis (Fin 2) ℤ L.lattice := L.latticeBasis

/-- The `ℤ`-linear equivalence between the lattice `L` and `ℤ × ℤ` provided by the
basis of periods. -/
def equivIntProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ := L.latticeEquivProd

/-- A complex lattice is a closed subset of `ℂ`. -/
theorem isClosed : IsClosed (L.lattice : Set ℂ) := L.isClosed_lattice

/-- The complex lattice viewed as an additive subgroup of `ℂ`. -/
def toAddSubgroup : AddSubgroup ℂ := L.lattice.toAddSubgroup

/-- The periods `ω₁`, `ω₂` of a complex lattice are linearly independent over `ℤ`:
the only integer combination summing to `0` is the trivial one. -/
theorem linearIndependent_int :
    ∀ (a b : ℤ), a • L.ω₁ + b • L.ω₂ = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  have hli := LinearIndependent.pair_iff.mp L.linearIndependent (a : ℝ) (b : ℝ)
  rw [Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ] at hli
  obtain ⟨ha, hb⟩ := hli h
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

/-- The lattice as a set: all complex numbers of the form `a • ω₁ + b • ω₂` with
`a, b ∈ ℤ`. -/
def toSet : Set ℂ := {z : ℂ | ∃ a b : ℤ, z = a • L.ω₁ + b • L.ω₂}

/-- A complex lattice `L` is normalized if `ω₂ / ω₁` lies in the upper half plane,
i.e. its imaginary part is positive. -/
def IsNormalized : Prop :=
  0 < (L.ω₂ / L.ω₁).im

section Homothety

open Pointwise

/-- Two complex lattices `L` and `L'` are homothetic if there is a nonzero complex
scalar `c` such that `L'` (as a set in `ℂ`) equals `c • L`. -/
def IsHomothetic (L L' : ComplexLattice) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)

/-- Homothety is reflexive: any lattice is homothetic to itself via the scalar `1`. -/
theorem IsHomothetic.refl (L : ComplexLattice) : IsHomothetic L L :=
  ⟨1, one_ne_zero, (one_smul ℂ (L.lattice : Set ℂ)).symm⟩

/-- Homothety is symmetric: if `L` and `L'` are homothetic via `c`, they are homothetic
via `c⁻¹` the other way. -/
theorem IsHomothetic.symm {L L' : ComplexLattice} (h : IsHomothetic L L') :
    IsHomothetic L' L := by
  obtain ⟨c, hc, hcL⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [hcL, inv_smul_smul₀ hc]⟩

/-- Homothety is transitive: composing two homotheties yields a homothety. -/
theorem IsHomothetic.trans {L₁ L₂ L₃ : ComplexLattice}
    (h₁₂ : IsHomothetic L₁ L₂) (h₂₃ : IsHomothetic L₂ L₃) :
    IsHomothetic L₁ L₃ := by
  obtain ⟨c₁, hc₁, hc₁L⟩ := h₁₂
  obtain ⟨c₂, hc₂, hc₂L⟩ := h₂₃
  exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, by rw [hc₂L, hc₁L, smul_smul]⟩

/-- Homothety of complex lattices is an equivalence relation. -/
theorem isHomothetic_equivalence : Equivalence IsHomothetic :=
  ⟨IsHomothetic.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end Homothety

/-- The discriminant `g₂³ - 27·g₃²` of the Weierstrass cubic associated to the lattice. -/
def discriminantLattice : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- Definitional equation for the discriminant of a complex lattice. -/
@[simp]
theorem discriminantLattice_def :
    L.discriminantLattice = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := rfl

/-- The `j`-invariant of a complex lattice, given by `1728 g₂³ / Δ` where `Δ` is the
discriminant. -/
def jInvariantLattice : ℂ := 1728 * L.g₂ ^ 3 / L.discriminantLattice

/-- Definitional equation for the `j`-invariant of a complex lattice. -/
@[simp]
theorem jInvariantLattice_def :
    L.jInvariantLattice = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := rfl

/-- The fundamental parallelogram translated by `α`: the image of the fundamental
domain of `L` under translation by `α`. -/
def fundamentalParallelogram (α : ℂ) : Set ℂ :=
  (α + ·) '' ZSpan.fundamentalDomain L.basis

/-- When the translation is `0`, the fundamental parallelogram coincides with the
standard fundamental domain of the lattice. -/
@[simp]
theorem fundamentalParallelogram_zero :
    fundamentalParallelogram L 0 = ZSpan.fundamentalDomain L.basis := by
  simp [fundamentalParallelogram]

/-- The coordinates of `t₁ ω₁ + t₂ ω₂` with respect to the basis `(ω₁, ω₂)` are
exactly `t₁` and `t₂`. -/
lemma basis_repr_omega (t₁ t₂ : ℝ) (i : Fin 2) :
    L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i := by
  rw [show t₁ • L.ω₁ + t₂ • L.ω₂ = t₁ • L.basis 0 + t₂ • L.basis 1 from by simp]
  simp only [map_add, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.add_apply, Finsupp.single_apply]
  fin_cases i <;>
    simp [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide]

/-- A point `z` lies in the fundamental parallelogram based at `α` iff it can be
written as `α + t₁ ω₁ + t₂ ω₂` with `0 ≤ t₁, t₂ < 1`. -/
theorem mem_fundamentalParallelogram_iff {α z : ℂ} :
    z ∈ fundamentalParallelogram L α ↔
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
        z = α + t₁ • L.ω₁ + t₂ • L.ω₂ := by
  simp only [fundamentalParallelogram, Set.mem_image, ZSpan.mem_fundamentalDomain]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨L.basis.repr w 0, L.basis.repr w 1, ?_⟩
    have h0 := hw 0; have h1 := hw 1
    simp only [Set.mem_Ico] at h0 h1
    refine ⟨h0.1, h0.2, h1.1, h1.2, ?_⟩
    have decomp : w = L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by
      have h := L.basis.sum_repr w
      rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
      exact h.symm
    conv_lhs => rw [decomp]
    ring
  · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
    refine ⟨t₁ • L.ω₁ + t₂ • L.ω₂, fun i => ?_, by ring⟩
    rw [L.basis_repr_omega]
    fin_cases i <;> simp <;> constructor <;> linarith

/-- The quotient `ℂ / L` is in bijection with the fundamental domain of the lattice:
every coset has a unique representative in the fundamental parallelogram. -/
def quotientEquivFundDomain :
    ℂ ⧸ L.lattice ≃ ZSpan.fundamentalDomain L.basis := by
  rw [L.lattice_eq_span_range_basis]
  exact ZSpan.quotientEquiv L.basis

end ComplexLattice

end
