/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-- Over a discrete valuation ring, every finitely generated torsion-free
module is free. -/
theorem dvr_fg_torsionFree_is_free (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free R M :=

  inferInstance

/-- An explicit basis (with rank) for a finitely generated torsion-free
module over a DVR. -/
noncomputable def dvr_fg_torsionFree_basis (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Σ n : ℕ, Module.Basis (Fin n) R M :=
  Module.basisOfFiniteTypeTorsionFree' (R := R)

/-- Over a DVR, a finitely generated module splits as the product of its
torsion submodule and its torsion-free quotient. -/
theorem dvr_torsionSplitting (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Nonempty ((↥(Submodule.torsion R M) × (M ⧸ Submodule.torsion R M)) ≃ₗ[R] M) := by

  have : Module.IsTorsionFree R (M ⧸ Submodule.torsion R M) := inferInstance
  have : Module.Free R (M ⧸ Submodule.torsion R M) := inferInstance

  obtain ⟨f, hf⟩ := Module.projective_lifting_property _
    LinearMap.id (Submodule.torsion R M).mkQ_surjective

  exact ⟨lequivProdOfRightSplitExact (Submodule.torsion R M).injective_subtype
    (by simp [Submodule.range_subtype, Submodule.ker_mkQ]) hf⟩

universe u v

/-- Structure theorem: every finitely generated module over a DVR (or, more
generally, a PID) decomposes as a free part plus a direct sum of cyclic
torsion modules `R / (p^e)` for irreducible `p`. -/
theorem dvr_fg_structure (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R)
      (_ : ∀ i, Irreducible (p i)) (e : ι → ℕ),
      Nonempty (M ≃ₗ[R] (Fin n →₀ R) × DirectSum ι fun i => R ⧸ R ∙ p i ^ e i) :=
  Module.equiv_free_prod_directSum R M

/-- The quotient of a finitely generated DVR-module by its torsion is free. -/
theorem dvr_quotient_torsion_free (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.Free R (M ⧸ Submodule.torsion R M) :=
  inferInstance

/-- For a finitely generated module over a DVR, freeness is equivalent to
torsion-freeness. -/
theorem dvr_free_iff_torsionFree (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.Free R M ↔ Module.IsTorsionFree R M :=
  Module.free_iff_isTorsionFree
