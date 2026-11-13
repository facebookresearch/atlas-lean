/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.ComplexMultiplication

namespace ComplexMultiplication

open ComplexLattice

noncomputable section

/-- A complex lattice $L$ has *complex multiplication* if its endomorphism ring
contains an element that is not an integer.  Equivalently (Definition 12.21),
$\mathrm{End}(L) \not\cong \mathbb{Z}$. -/
def HasCM (L : ComplexLattice) : Prop :=
  ∃ α : ℂ, α ∈ L.endomorphismRing ∧ ∀ n : ℤ, α ≠ (n : ℂ)

/-- The lattice $L$ has complex multiplication *by the order* $\mathcal{O}$
if $L$ is a proper $\mathcal{O}$-ideal and $\mathcal{O}$ is an order in an
imaginary quadratic field. -/
def HasCMBy (L : ComplexLattice) (𝒪 : Subring ℂ) : Prop :=
  ComplexLattice.IsProperIdeal 𝒪 L ∧ ComplexLattice.IsImagQuadOrder 𝒪

/-- A lattice has complex multiplication iff there exists an order $\mathcal{O}$
in an imaginary quadratic field such that $L$ has CM by $\mathcal{O}$. -/
theorem hasCM_iff_exists_hasCMBy (L : ComplexLattice) :
    HasCM L ↔ ∃ 𝒪 : Subring ℂ, HasCMBy L 𝒪 := by
  constructor
  · intro ⟨τ, hτ_mem, hτ_not_int⟩
    refine ⟨L.endomorphismRing, ?_, ?_⟩
    · exact rfl
    · exact endomorphismRing_order_witness L τ hτ_mem hτ_not_int
  · intro ⟨𝒪, h𝒪_prop, h𝒪_imag⟩
    obtain ⟨τ, hτ_mem, hτ_not_int, _b, _c, _hpoly, _hdisc⟩ := h𝒪_imag
    have : L.endomorphismRing = 𝒪 := h𝒪_prop
    exact ⟨τ, this ▸ hτ_mem, hτ_not_int⟩

/-- A lattice has complex multiplication iff its endomorphism ring is an
order in an imaginary quadratic field. -/
theorem hasCM_iff_isImagQuadOrder (L : ComplexLattice) :
    HasCM L ↔ ComplexLattice.IsImagQuadOrder L.endomorphismRing := by
  constructor
  · intro ⟨τ, hτ_mem, hτ_not_int⟩
    obtain ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩ :=
      endomorphismRing_order_witness L τ hτ_mem hτ_not_int
    exact ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩
  · intro ⟨τ, hτ_mem, hτ_not_int, _⟩
    exact ⟨τ, hτ_mem, hτ_not_int⟩

/-- A lattice does *not* have complex multiplication iff every element of its
endomorphism ring is an integer; i.e. $\mathrm{End}(L) = \mathbb{Z}$. -/
theorem not_hasCM_iff_endRing_eq_Z (L : ComplexLattice) :
    ¬ HasCM L ↔ ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ) := by
  constructor
  · intro h α hα
    by_contra hne
    push_neg at hne
    exact h ⟨α, hα, hne⟩
  · intro h ⟨τ, hτ_mem, hτ_not_int⟩
    obtain ⟨n, rfl⟩ := h τ hτ_mem
    exact hτ_not_int n rfl

end

end ComplexMultiplication
