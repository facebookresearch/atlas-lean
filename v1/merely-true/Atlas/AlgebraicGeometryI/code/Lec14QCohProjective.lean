/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

/-- A sheaf of `O_X`-modules `ℱ` is quasi-coherent (Def 24, Lec 10) — abbreviation for
the mathlib predicate `SheafOfModules.IsQuasicoherent`. -/
def IsQuasicoherentSheaf {X : Scheme.{u}} (ℱ : X.Modules) : Prop :=
  ℱ.IsQuasicoherent


/-- A graded module over a graded ring `𝒜 = ⨁ₙ 𝒜ₙ`: an `A`-module `carrier` together
with a `ℤ`-indexed decomposition `carrier = ⨁_d component d` compatible with the grading
in the sense `𝒜ₙ · component d ⊆ component (n + d)`. -/
structure GrMod {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module A carrier]
  component : ℤ → AddSubgroup carrier
  internal : DirectSum.IsInternal component
  graded_smul : ∀ (n : ℕ) (d : ℤ) (a : A) (m : carrier),
    a ∈ (𝒜 n : Set A) → m ∈ component d → a • m ∈ component (↑n + d)

attribute [instance] GrMod.instAddCommGroup GrMod.instModule

namespace GrMod

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A graded module is finitely generated if its underlying `A`-module is finite. -/
def IsFinitelyGenerated (M : GrMod 𝒜) : Prop :=
  Module.Finite A M.carrier

/-- A graded module is "finite-dimensional" (concentrated in finitely many degrees) if
all but finitely many graded components vanish. -/
def IsFiniteDimensional (M : GrMod 𝒜) : Prop :=
  ∃ (S : Finset ℤ), ∀ d, d ∉ S → M.component d = ⊥

/-- A graded module is locally nilpotent with respect to the irrelevant ideal `𝒜₊` if
every element is annihilated by a power of every element of `𝒜₊`. -/
def IsLocallyNilpotent (M : GrMod 𝒜) : Prop :=
  ∀ (x : M.carrier), ∃ (d : ℕ),
    ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal → a ^ d • x = 0

/-- A morphism of graded modules: an underlying `A`-linear map (here without graded
constraints — kept as a flexible wrapper). -/
structure Hom (M N : GrMod 𝒜) where
  toLinearMap : M.carrier →ₗ[A] N.carrier

/-- Extensionality for `GrMod.Hom`: two morphisms are equal iff their underlying
linear maps coincide. -/
@[ext]
theorem Hom.ext {M N : GrMod 𝒜} {f g : Hom M N}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; congr

/-- A short exact sequence of graded modules `0 → M₁ → M₂ → M₃ → 0`, packaged with
injectivity of `f`, surjectivity of `g`, and exactness `ker g = range f`. -/
structure ShortExact (M₁ M₂ M₃ : GrMod 𝒜) where
  f : M₁.carrier →ₗ[A] M₂.carrier
  g : M₂.carrier →ₗ[A] M₃.carrier
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  exact : LinearMap.ker g = LinearMap.range f





end GrMod

/-- Category instance on graded modules over `𝒜`: morphisms are `GrMod.Hom`, identity
and composition come from the underlying linear maps. -/
instance grModCategory {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Category (GrMod 𝒜) where
  Hom := GrMod.Hom
  id M := ⟨LinearMap.id⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap⟩
  id_comp f := by apply GrMod.Hom.ext; simp
  comp_id f := by apply GrMod.Hom.ext; simp
  assoc f g h := by apply GrMod.Hom.ext; simp [LinearMap.comp_assoc]




variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

















/-- The full subcategory of quasi-coherent sheaves of `O_{Proj 𝒜}`-modules. -/
abbrev QCohCat {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :=
  (show ObjectProperty ((Proj 𝒜).Modules) from fun ℱ => IsQuasicoherentSheaf ℱ).FullSubcategory









end
