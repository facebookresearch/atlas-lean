/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.TateCechInfra

noncomputable section

namespace TateResidueOrthogonality

open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator TateCechInfra


section SelfDuality

variable {k : Type*} [Field k]

/-- Non-degeneracy of the residue pairing on Laurent-style finitely supported
functions `ℤ →₀ k`: if `f` pairs to zero against every `g`, then `f = 0`. -/
theorem residue_pairing_nondegenerate (f : ℤ →₀ k)
    (hpair : ∀ g : ℤ →₀ k,
      (∑ j ∈ f.support, f j * g (-1 - j)) = 0) :
    f = 0 := by
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  specialize hpair (Finsupp.single (-1 - i) 1)
  simp only [Finsupp.single_apply] at hpair
  have key : ∀ j ∈ f.support,
      f j * (if -1 - i = -1 - j then (1 : k) else 0) =
      if j = i then f j else 0 := by
    intro j _
    split_ifs with h1 h2
    · simp
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl key] at hpair
  by_cases hm : i ∈ f.support
  · rw [Finset.sum_ite_eq' f.support i] at hpair
    simp [hm] at hpair
    exact hpair
  · exact Finsupp.notMem_support_iff.mp hm

/-- Right-side non-degeneracy of the residue pairing: if `g` pairs to zero
against every `f`, then `g = 0`. -/
theorem residue_pairing_nondegenerate_right (g : ℤ →₀ k)
    (hpair : ∀ f : ℤ →₀ k,
      (∑ j ∈ f.support, f j * g (-1 - j)) = 0) :
    g = 0 := by
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  have h := hpair (Finsupp.single (-1 - i) 1)
  simp only [Finsupp.single_apply, Finsupp.support_single_ne_zero _ one_ne_zero,
    Finset.sum_singleton] at h
  have : -1 - (-1 - i) = i := by omega
  rw [this] at h
  simpa using h

end SelfDuality


section LatticeOrthogonality

variable {k : Type*} [Field k]

/-- The nonneg-supported lattice is self-orthogonal under the residue pairing:
if `f` and `g` are both supported on `ℕ ⊂ ℤ`, the residue pairing vanishes. -/
theorem nonneg_annihilates_nonneg (f : ℤ →₀ k)
    (hf : ∀ i, i < 0 → f i = 0)
    (g : ℤ →₀ k) (hg : ∀ i, i < 0 → g i = 0) :
    (∑ j ∈ f.support, f j * g (-1 - j)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj_neg : j < 0
  · simp [hf j hj_neg]
  · have : -1 - j < 0 := by omega
    simp [hg (-1 - j) this]

/-- Characterization: `f` annihilates every nonneg-supported `g` under the
residue pairing iff `f` itself is nonneg-supported. -/
theorem lattice_annihilator_nonneg_iff (f : ℤ →₀ k) :
    (∀ g : ℤ →₀ k, (∀ i, i < 0 → g i = 0) →
      (∑ j ∈ f.support, f j * g (-1 - j)) = 0) ↔
    (∀ i, i < 0 → f i = 0) := by
  constructor
  · exact lattice_annihilator_nonneg f
  · intro hf g hg
    exact nonneg_annihilates_nonneg f hf g hg

end LatticeOrthogonality


section DiscreteCocompact

variable (k : Type*) [Field k]

/-- `Λ` is arithmetically discrete with respect to `W` iff `Λ / (W ∩ Λ)` is
finite-dimensional over `k`. -/
structure IsArithmeticallyDiscrete {V : Type*} [AddCommGroup V] [Module k V]
    (W Λ : Submodule k V) : Prop where
  finiteDim : Module.Finite k (Λ ⧸ Submodule.comap Λ.subtype (W ⊓ Λ))

/-- `Λ` is arithmetically cocompact with respect to `W` iff `V / (W + Λ)` is
finite-dimensional over `k`. -/
structure IsArithmeticallyCocompact {V : Type*} [AddCommGroup V] [Module k V]
    (W Λ : Submodule k V) : Prop where
  finiteDim : Module.Finite k (V ⧸ (W ⊔ Λ))

/-- Duality between discreteness and cocompactness: in the finite-dimensional
setting, the annihilators of a discrete/cocompact pair are themselves a
discrete/cocompact pair. -/
theorem discrete_cocompact_dual
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W Λ : Submodule k V)
    (_ : IsArithmeticallyDiscrete k W Λ)
    (_ : IsArithmeticallyCocompact k W Λ) :
    IsArithmeticallyDiscrete k W.dualAnnihilator Λ.dualAnnihilator ∧
    IsArithmeticallyCocompact k W.dualAnnihilator Λ.dualAnnihilator := by
  exact ⟨⟨Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)⟩,
         ⟨Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)⟩⟩

/-- The annihilator of a subspace inside the dual of a finite-dimensional
space is itself finite-dimensional. -/
theorem annihilator_finiteDim
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Submodule k V) :
    FiniteDimensional k W.dualAnnihilator :=
  inferInstance

end DiscreteCocompact


section InclusionToEquality

variable {k : Type*} [Field k]

/-- An inclusion of subspaces becomes an equality once their dimensions agree
and the larger one is finite-dimensional. -/
theorem inclusion_to_equality_by_dimension
    {V : Type*} [AddCommGroup V] [Module k V]
    (W₁ W₂ : Submodule k V) [FiniteDimensional k W₂]
    (h_le : W₁ ≤ W₂)
    (h_dim : Module.finrank k W₁ = Module.finrank k W₂) :
    W₁ = W₂ :=
  Submodule.eq_of_le_of_finrank_eq h_le h_dim

/-- Specialization of `inclusion_to_equality_by_dimension` to comparing a
subspace of the dual to the annihilator of `V₁`. -/
theorem annihilator_equality_from_inclusion_and_dim
    {V : Type*} [AddCommGroup V] [Module k V]
    (V₁ : Submodule k V)
    (V₁' : Submodule k (Module.Dual k V))
    [FiniteDimensional k V₁.dualAnnihilator]
    (h_inc : V₁' ≤ V₁.dualAnnihilator)
    (h_dim : Module.finrank k V₁' = Module.finrank k V₁.dualAnnihilator) :
    V₁' = V₁.dualAnnihilator :=
  Submodule.eq_of_le_of_finrank_eq h_inc h_dim

end InclusionToEquality


section TateOrthogonalityChain

variable {k : Type*} [Field k]

/-- Complete Tate orthogonality: under the annihilator identifications, the
intersection `V₁' ⊓ V₂'` equals the annihilator of `V₁ ⊔ V₂` and has the same
dimension as the quotient `V / (V₁ ⊔ V₂)`. -/
theorem tate_orthogonality_complete
    (S : TateDualitySetup k) [FiniteDimensional k S.V]
    (V₁' V₂' : Submodule k (Module.Dual k S.V))
    (h_V1_eq : V₁' = S.V₁.dualAnnihilator)
    (h_V2_eq : V₂' = S.V₂.dualAnnihilator) :
    V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator ∧
    Module.finrank k ↥(V₁' ⊓ V₂') =
      Module.finrank k (S.V ⧸ (S.V₁ ⊔ S.V₂)) := by
  constructor
  · rw [h_V1_eq, h_V2_eq]
    exact (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm
  · rw [h_V1_eq, h_V2_eq, (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm]
    have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (S.V₁ ⊔ S.V₂)
    have h_quot := Submodule.finrank_quotient_add_finrank (S.V₁ ⊔ S.V₂)
    omega

/-- Tate orthogonality implies Serre duality at the level of dimensions:
the intersection of dual annihilators matches `H¹`. -/
theorem tate_orthogonality_gives_serre_duality
    (S : TateDualitySetup k) [FiniteDimensional k S.V]
    (V₁' V₂' : Submodule k (Module.Dual k S.V))
    (h_V1_eq : V₁' = S.V₁.dualAnnihilator)
    (h_V2_eq : V₂' = S.V₂.dualAnnihilator) :
    Module.finrank k ↥(V₁' ⊓ V₂') =
      Module.finrank k S.cechH1 :=
  (tate_orthogonality_complete S V₁' V₂' h_V1_eq h_V2_eq).2


end TateOrthogonalityChain


section ResidueConnection

variable {k : Type*} [Field k]

/-- Separation: any nonzero `f` admits a `g` against which the residue pairing
is nonzero, i.e. residues separate Laurent-style sections (Lem 36, Tate
residue orthogonality). -/
theorem residue_pairing_separating (f : ℤ →₀ k) (hf : f ≠ 0) :
    ∃ g : ℤ →₀ k, (∑ j ∈ f.support, f j * g (-1 - j)) ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (residue_pairing_nondegenerate f h)

/-- Dual basis: the indicator at `i` pairs with itself via the index `-1 - i`
to give `1`. -/
theorem residue_dual_basis (i : ℤ) :
    (∑ j ∈ (Finsupp.single i (1 : k)).support,
      (Finsupp.single i (1 : k)) j *
      (Finsupp.single (-1 - i) (1 : k)) (-1 - j)) = (1 : k) := by
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_apply]
  simp

/-- Orthogonality of distinct dual basis elements under the residue pairing. -/
theorem residue_dual_basis_orthog (i j : ℤ) (hij : i ≠ j) :
    (∑ l ∈ (Finsupp.single i (1 : k)).support,
      (Finsupp.single i (1 : k)) l *
      (Finsupp.single (-1 - j) (1 : k)) (-1 - l)) = (0 : k) := by
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_apply]
  simp [show -1 - j ≠ -1 - i from by omega]

end ResidueConnection

end TateResidueOrthogonality

end
