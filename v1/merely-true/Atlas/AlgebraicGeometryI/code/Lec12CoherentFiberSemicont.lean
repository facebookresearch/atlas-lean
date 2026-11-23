/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option maxHeartbeats 400000

open scoped TensorProduct
open TensorProduct

universe u

/-- Fiber dimension of an `R`-module `M` at a prime `𝔭`: the dimension of the residue
field tensor product `κ(𝔭) ⊗_R M` over `κ(𝔭)`. -/
noncomputable def fiberDim {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (𝔭 : Ideal R) [𝔭.IsPrime] : ℕ :=
  Module.finrank 𝔭.ResidueField (𝔭.ResidueField ⊗[R] M)

/-- For a flat finite module, the fiber dimension agrees with the rank at the stalk. -/
lemma fiberDim_eq_rankAtStalk {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Flat R M] [Module.Finite R M]
    (p : PrimeSpectrum R) :
    fiberDim M p.asIdeal = Module.rankAtStalk M p :=
  (Module.rankAtStalk_eq p).symm

/-- Lemma 25 (Lec 12), part 1: the fiber `κ(𝔭) ⊗_R M` of a finitely generated module
is finite-dimensional over the residue field. -/
theorem lemma25_fiber_finite
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Module.Finite 𝔭.ResidueField (𝔭.ResidueField ⊗[R] M) :=
  Module.Finite.base_change R 𝔭.ResidueField M

/-- Lemma 25 (Lec 12): the fiber `M ⊗_R κ(p)` vanishes at `p` iff `p` is not in the
support of `M`. -/
theorem lemma25_fiber_zero_iff_not_mem_support
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) :
    fiberDim M p.asIdeal = 0 ↔ p ∉ Module.support R M := by
  unfold fiberDim
  haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) :=
    Module.Finite.base_change R p.asIdeal.ResidueField M
  rw [Module.finrank_zero_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]

/-- Lemma 25 (Lec 12): the support of a finitely generated module is a closed subset
of `Spec R` (cut out by the annihilator). -/
theorem lemma25_support_isClosed
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsClosed (Module.support R M) := by
  rw [Module.support_eq_zeroLocus]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- The base change `A ⊗_R (⊤ : Submodule R M) ≃ₗ[A] A ⊗_R M`: tensoring with the
inclusion of the top submodule is an isomorphism. -/
noncomputable def topEquivTensor (A R M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] :
    A ⊗[R] (↥(⊤ : Submodule R M)) ≃ₗ[A] A ⊗[R] M :=
  LinearEquiv.ofLinear
    (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) Submodule.topEquiv.toLinearMap)
    (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) Submodule.topEquiv.symm.toLinearMap)
    (by apply AlgebraTensorModule.ext; intro a m; simp [Submodule.topEquiv])
    (by apply AlgebraTensorModule.ext; intro a m; simp [Submodule.topEquiv])

/-- The minimal number of generators of `M` (`spanFinrank` of the top submodule) is
invariant under linear equivalences. -/
lemma spanFinrank_top_eq_of_linearEquiv {R : Type*} {M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (⊤ : Submodule R M).spanFinrank = (⊤ : Submodule R N).spanFinrank := by
  have h1 : Submodule.map e.toLinearMap (⊤ : Submodule R M) = ⊤ := by simp [LinearEquiv.range]
  have h2 : Submodule.map e.symm.toLinearMap (⊤ : Submodule R N) = ⊤ := by simp [LinearEquiv.range]
  have le1 : (⊤ : Submodule R N).spanRank ≤ (⊤ : Submodule R M).spanRank := by
    rw [← h1]; exact Submodule.spanRank_map_le e.toLinearMap ⊤
  have le2 : (⊤ : Submodule R M).spanRank ≤ (⊤ : Submodule R N).spanRank := by
    rw [← h2]; exact Submodule.spanRank_map_le e.symm.toLinearMap ⊤
  simp [Submodule.spanFinrank, le_antisymm le2 le1]

/-- Over a local ring, the dimension of the fiber `κ ⊗_R M` equals the minimal number
of generators of `M` (Nakayama). -/
lemma finrank_residueField_tensor_eq_spanFinrank_top
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = (⊤ : Submodule R M).spanFinrank := by
  set κ := IsLocalRing.ResidueField R
  set N : Submodule R M := ⊤
  calc Module.finrank κ (κ ⊗[R] M)
      = Module.finrank κ (κ ⊗[R] ↥N) := (topEquivTensor κ R M).finrank_eq.symm
    _ = (⊤ : Submodule κ (κ ⊗[R] ↥N)).spanFinrank := Module.finrank_eq_spanFinrank_of_free
    _ = N.spanFinrank :=
        TensorProduct.spanFinrank_top_eq_of_residueField N Module.Finite.fg_top

/-- Bridge between fiber dimension and the localized module: `fiberDim M 𝔭` equals the
minimal number of generators of the stalk `M_𝔭`. -/
lemma fiberDim_eq_spanFinrank_stalk
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    fiberDim M 𝔭 = (⊤ : Submodule (Localization.AtPrime 𝔭)
      (Localization.AtPrime 𝔭 ⊗[R] M)).spanFinrank := by
  set R𝔭 := Localization.AtPrime 𝔭
  set M𝔭 := R𝔭 ⊗[R] M
  set κ𝔭 := 𝔭.ResidueField
  haveI : Module.Finite R𝔭 M𝔭 := Module.Finite.base_change R R𝔭 M
  haveI : SMulCommClass R R𝔭 R𝔭 := Algebra.to_smulCommClass
  have cbc : κ𝔭 ⊗[R𝔭] M𝔭 ≃ₗ[κ𝔭] κ𝔭 ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R R𝔭 κ𝔭 κ𝔭 M
  unfold fiberDim
  rw [show Module.finrank κ𝔭 (κ𝔭 ⊗[R] M) = Module.finrank κ𝔭 (κ𝔭 ⊗[R𝔭] M𝔭)
      from cbc.finrank_eq.symm]
  exact finrank_residueField_tensor_eq_spanFinrank_top

/-- Lemma 25 (Lec 12) — Upper semi-continuity of fiber dimension: if `𝔭 ⊆ 𝔮` are
primes, then `fiberDim M 𝔭 ≤ fiberDim M 𝔮`. -/
theorem lemma25_fiber_upper_semicontinuity
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 𝔮 : Ideal R) [𝔭.IsPrime] [𝔮.IsPrime] (h : 𝔭 ≤ 𝔮) :
    fiberDim M 𝔭 ≤ fiberDim M 𝔮 := by
  set R𝔭 := Localization.AtPrime 𝔭
  set R𝔮 := Localization.AtPrime 𝔮
  set M𝔭 : Type u := R𝔭 ⊗[R] M
  set M𝔮 : Type u := R𝔮 ⊗[R] M

  have hsub : 𝔮.primeCompl ≤ 𝔭.primeCompl := fun x hx hmem => hx (h hmem)
  letI : Algebra R𝔮 R𝔭 :=
    IsLocalization.localizationAlgebraOfSubmonoidLe R𝔮 R𝔭 𝔮.primeCompl 𝔭.primeCompl hsub
  haveI : IsScalarTower R R𝔮 R𝔭 :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R𝔮 R𝔭 𝔮.primeCompl 𝔭.primeCompl hsub
  haveI : SMulCommClass R𝔮 R𝔭 R𝔭 := Algebra.to_smulCommClass
  haveI : Module.Finite R𝔭 M𝔭 := Module.Finite.base_change R R𝔭 M
  haveI : Module.Finite R𝔮 M𝔮 := Module.Finite.base_change R R𝔮 M

  rw [fiberDim_eq_spanFinrank_stalk 𝔭, fiberDim_eq_spanFinrank_stalk 𝔮]

  have cbc := AlgebraTensorModule.cancelBaseChange R R𝔮 R𝔭 R𝔭 M
  calc (⊤ : Submodule R𝔭 M𝔭).spanFinrank
      = (⊤ : Submodule R𝔭 (R𝔭 ⊗[R𝔮] M𝔮)).spanFinrank :=
          spanFinrank_top_eq_of_linearEquiv cbc.symm
    _ = (⊤ : Submodule R𝔭 (R𝔭 ⊗[R𝔮] ↥(⊤ : Submodule R𝔮 M𝔮))).spanFinrank :=
          spanFinrank_top_eq_of_linearEquiv (topEquivTensor R𝔭 R𝔮 M𝔮).symm
    _ ≤ (⊤ : Submodule R𝔮 M𝔮).spanFinrank :=
          TensorProduct.spanFinrank_top_le_of_fg (⊤ : Submodule R𝔮 M𝔮) Module.Finite.fg_top

/-- Forward direction of the local-free criterion: if `M` is free over a local domain,
then fiber dimension at the closed point equals fiber dimension at the generic point. -/
theorem lemma25_locally_free_criterion_mp
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] :
    fiberDim M (IsLocalRing.maximalIdeal R) =
      Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) := by
  show Module.finrank _ _ = Module.finrank _ _
  have h1 : Module.finrank (IsLocalRing.maximalIdeal R).ResidueField
      ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R] M) = Module.finrank R M :=
    Module.finrank_baseChange
  have h2 : Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) = Module.finrank R M :=
    Module.finrank_baseChange
  rw [h1, h2]


