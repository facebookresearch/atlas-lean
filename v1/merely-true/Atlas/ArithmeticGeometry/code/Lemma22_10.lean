/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AdelePlusFDim

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily






/-- A nonzero element of $F$ has finite order at every place $p$. -/
lemma dvf_ord_ne_top_of_ne_zero
    {F : Type*} [Field F] {P : Type*}
    (k : Type*) [Field k] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (x : F) (hx : x ≠ 0) :
    DiscreteValuationFamily.ord (k := k) p x ≠ ⊤ := by
  intro h
  have hmul := DiscreteValuationFamily.ord_mul (k := k) p x x⁻¹
  rw [mul_inv_cancel₀ hx] at hmul
  have hone : DiscreteValuationFamily.ord (k := k) p (1 : F) = (0 : ℤ) := by
    have := DiscreteValuationFamily.ord_algebraMap (k := k) (F := F) p (1 : k) one_ne_zero
    rwa [map_one] at this
  rw [hone, h] at hmul
  simp at hmul

/-- For a nonzero $x \in F$, the order $\mathrm{ord}_p(x)$ is given by a (finite) integer. -/
lemma dvf_ord_eq_coe_of_ne_zero
    {F : Type*} [Field F] {P : Type*}
    (k : Type*) [Field k] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (x : F) (hx : x ≠ 0) :
    ∃ n : ℤ, DiscreteValuationFamily.ord (k := k) p x = ↑n := by
  cases hv : DiscreteValuationFamily.ord (k := k) p x with
  | top => exact absurd hv (dvf_ord_ne_top_of_ne_zero k p x hx)
  | coe n => exact ⟨n, rfl⟩


section Lemma22_10

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]




/-- Linear-algebra lemma: if $S \le T$ are submodules of $M$ over a division ring with finite
$T/S$ of dimension $0$, then $S = T$. -/
lemma submodule_eq_of_finrank_quotient_zero {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (hST : S ≤ T)
    [hFD : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype S)]
    (h0 : Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) = 0) :
    S = T := by
  have hforall := finrank_zero_iff_forall_zero.mp h0
  ext x
  constructor
  · exact fun hx => hST hx
  · intro hx
    have := hforall (Submodule.Quotient.mk (⟨x, hx⟩ : T))
    rw [Submodule.Quotient.mk_eq_zero] at this
    rw [Submodule.mem_comap, Submodule.subtype_apply] at this
    exact this


end Lemma22_10
