/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SmoothnessOmega

noncomputable section

open KaehlerDifferential Algebra IsLocalRing

universe u v

section Prop30Characterization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]


omit [IsNoetherianRing R] in
/-- A local ring `R` is regular iff its Krull dimension equals its embedding
dimension; the definitional unfolding of regularity. -/
theorem isRegularLocal_iff_eq :
    IsRegularLocal R ↔ ringKrullDim R = ↑(embDim R) :=
  Iff.rfl

/-- For a Noetherian local ring, regularity is equivalent to the inequality
`embDim ≤ krullDim`, combined with the general bound `krullDim ≤ embDim`. -/
theorem isRegularLocal_iff_le :
    IsRegularLocal R ↔ (↑(embDim R) ≤ ringKrullDim R) := by
  constructor
  · intro h
    exact le_of_eq h.symm
  · intro h
    exact le_antisymm (krullDim_le_embDim R) h

/-- Prop 30 (Lec, regularity): the Krull dimension of a Noetherian local ring
is bounded above by its embedding dimension. -/
theorem prop30_inequality : ringKrullDim R ≤ ↑(embDim R) :=
  krullDim_le_embDim R

omit [IsNoetherianRing R] in
/-- Symmetric reformulation: regular ⇔ `embDim = krullDim`. -/
theorem isRegularLocal_iff_embDim_eq :
    IsRegularLocal R ↔ ↑(embDim R) = ringKrullDim R := by
  rw [isRegularLocal_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

end Prop30Characterization

section CotangentSpaceConnection

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The cotangent space `m/m²` of a Noetherian local ring is a finite-dimensional
vector space over the residue field. -/
theorem cotangentSpace_finiteDimensional_regular :
    FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  inferInstance

/-- The cotangent space vanishes iff `R` is a field, i.e. `dim_k m/m² = 0`. -/
theorem cotangentSpace_subsingleton_iff :
    Subsingleton (CotangentSpace R) ↔ IsField R :=
  subsingleton_cotangentSpace_iff

/-- `dim_k m/m² ≤ 1` iff the maximal ideal is principal (a discrete valuation
ring or a field). -/
theorem cotangentSpace_finrank_le_one_iff :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 ↔
    (maximalIdeal R).IsPrincipal :=
  finrank_cotangentSpace_le_one_iff

end CotangentSpaceConnection

section SmoothnessRegularity

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Smoothness at a prime is detected by smoothness on a Zariski-open
neighborhood; if `R → A` is smooth at `p`, there exists `f ∉ p` with `A_f` smooth. -/
theorem smooth_at_implies_exists_smooth_localization
    [FinitePresentation R A] (p : Ideal A) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ f ∉ p, Smooth R (Localization.Away f) :=
  exists_localization_smooth_of_smooth_at p

/-- Characterization of the smooth locus: complement of the support of `H¹`
of the cotangent intersected with the free locus of `Ω[A/R]`. -/
theorem smooth_locus_regularity_criterion [EssFiniteType R A] :
    smoothLocus R A =
      (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] :=
  smoothLocus_eq_kahler_free_locus

/-- An `R`-algebra `A` is formally smooth iff its smooth locus is all of `Spec A`. -/
theorem smooth_iff_all_local_rings_in_smooth_locus [FinitePresentation R A] :
    smoothLocus R A = Set.univ ↔ FormallySmooth R A :=
  smooth_iff_smoothLocus_univ

end SmoothnessRegularity

section Examples

variable (k : Type u) [Field k]

/-- A field is a regular local ring (trivial case of regularity). -/
theorem field_isRegular (hk : IsField k) :
    IsRegularLocal k := isRegularLocal_of_field k hk

/-- Every discrete valuation ring is a regular local ring of dimension one. -/
theorem DVR_isRegular (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsRegularLocal R := isRegularLocal_of_DVR R

/-- The Krull dimension of the polynomial ring `k[X_1, …, X_n]` over a field is `n`. -/
theorem polynomial_ring_dim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = ↑n :=
  smooth_ringKrullDim_mvPolynomial k n

/-- Prop 30 applied to localizations of a polynomial ring at a prime: Krull
dimension is bounded by embedding dimension. -/
theorem prop30_for_polynomial_localization (n : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin n) k)) [𝔭.IsPrime] :
    ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑(embDim (Localization.AtPrime 𝔭)) :=
  localization_mvPoly_krullDim_le_embDim k n 𝔭

end Examples

end
