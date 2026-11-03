/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.GradedPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Module
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.DirectSum.Basic

set_option maxHeartbeats 4000000

open MvPolynomial

noncomputable section

namespace QCohProjective

/-- Homogeneous coordinate ring `k[X_0, …, X_n]` of `ℙ^n_k`. -/
abbrev HomogCoordRing (k : Type*) [CommSemiring k] (n : ℕ) := MvPolynomial (Fin (n + 1)) k

/-- Degree-`d` homogeneous component of the homogeneous coordinate ring of `ℙ^n_k`. -/
def gradedComponent (k : Type*) [CommSemiring k] (n d : ℕ) :
    Submodule k (HomogCoordRing k n) :=
  homogeneousSubmodule (Fin (n + 1)) k d

/-- The irrelevant ideal `(X_0, …, X_n)` of the homogeneous coordinate ring of `ℙ^n_k`. -/
def irrelevantIdeal (k : Type*) [CommSemiring k] (n : ℕ) :
    Ideal (HomogCoordRing k n) :=
  Ideal.span (Set.range (fun i : Fin (n + 1) => MvPolynomial.X i))

/-- Abstract data of a graded module over the homogeneous coordinate ring of
`ℙ^n_k`: an integer-indexed family of `k`-vector spaces with a graded
multiplication action by homogeneous polynomials. -/
structure GradedModuleData (k : Type*) [Field k] (n : ℕ) where
  component : ℤ → Type*
  instACG : ∀ d : ℤ, AddCommGroup (component d)
  instMod : ∀ d : ℤ, Module k (component d)
  gsmul : ∀ (i : ℕ) (j : ℤ), gradedComponent k n i → component j → component (↑i + j)

attribute [instance] GradedModuleData.instACG GradedModuleData.instMod

/-- Degree shift `M ↦ M(d)` of a graded module, corresponding to tensoring
with the twist `𝒪(d)` on `ℙ^n_k`. -/
def GradedModuleData.twist {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) : GradedModuleData k n where
  component i := M.component (i + d)
  instACG i := M.instACG (i + d)
  instMod i := M.instMod (i + d)
  gsmul a j s m := cast (by congr 1; omega) (M.gsmul a (j + d) s m)

/-- Iterating the twist: `(M(d₁))(d₂)` agrees component-wise with the shift by `d₁ + d₂`. -/
theorem twist_twist {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d₁ d₂ : ℤ) (i : ℤ) :
    ((M.twist d₁).twist d₂).component i = M.component (i + d₂ + d₁) := by
  rfl

/-- The trivial twist `M(0)` agrees with `M` on every degree component. -/
theorem twist_zero {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (i : ℤ) :
    (M.twist 0).component i = M.component i := by
  simp [GradedModuleData.twist]

/-- Twisting by `d` then by `-d` recovers the original module component-wise. -/
theorem twist_neg_cancel {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) (i : ℤ) :
    ((M.twist d).twist (-d)).component i = M.component i := by
  simp [GradedModuleData.twist, add_assoc]

/-- Successive twists add: `(M(d₁))(d₂) ≅ M(d₁ + d₂)` component-wise. -/
theorem twist_add {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d₁ d₂ : ℤ) (i : ℤ) :
    ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i := by
  simp [GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

/-- Over a domain, `m` is torsion iff it is annihilated by some nonzero scalar. -/
theorem torsion_iff_killed {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] (m : M) :
    m ∈ Submodule.torsion R M ↔ ∃ (r : R), r ≠ 0 ∧ r • m = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ham⟩
    exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ham⟩
  · rintro ⟨r, hr, hrm⟩
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrm⟩

/-- Over a domain, a module is entirely torsion iff every element is annihilated
by some nonzero scalar. -/
theorem torsion_module_iff_all_torsion {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] :
    (∀ m : M, m ∈ Submodule.torsion R M) ↔
      ∀ m : M, ∃ (r : R), r ≠ 0 ∧ r • m = 0 := by
  constructor
  · intro h m
    have hm := h m
    rw [Submodule.mem_torsion_iff] at hm
    obtain ⟨⟨a, ha⟩, ham⟩ := hm
    exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ham⟩
  · intro h m
    rw [Submodule.mem_torsion_iff]
    obtain ⟨r, hr, hrm⟩ := h m
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrm⟩

/-- Set-level description of the torsion submodule over a domain. -/
theorem torsion_submodule_eq_set {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] :
    (Submodule.torsion R M : Set M) =
      {m : M | ∃ (r : R), r ≠ 0 ∧ r • m = 0} := by
  ext m
  exact torsion_iff_killed m

/-- Serre quotient criterion: a kernel-killing / cokernel-killing condition for a
linear map `f : M → N` implies that `f` becomes an isomorphism after quotienting
by torsion (mirrors the proof that graded modules and quasi-coherent sheaves on
`ℙ^n` agree modulo torsion). -/
theorem serre_quotient_iso_criterion {R : Type*} [CommRing R] [IsDomain R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (∀ m : M, f m = 0 → m ∈ Submodule.torsion R M) ∧
    (∀ n : N, ∃ (r : R), r ≠ 0 ∧ r • n ∈ LinearMap.range f) →


    (∀ m : M, f m ∈ Submodule.torsion R N → m ∈ Submodule.torsion R M) ∧
    (∀ n : N, n ∈ Submodule.torsion R N ∨ ∃ (r : R), r ≠ 0 ∧ r • n ∈ LinearMap.range f) := by
  intro ⟨h_ker, h_coker⟩
  constructor
  · intro m hfm
    rw [torsion_iff_killed] at hfm ⊢
    obtain ⟨r, hr, hrfm⟩ := hfm

    have hfr : f (r • m) = 0 := by rw [map_smul, hrfm]
    have hrm_tors := h_ker _ hfr
    rw [torsion_iff_killed] at hrm_tors
    obtain ⟨s, hs, hsrm⟩ := hrm_tors

    refine ⟨s * r, mul_ne_zero hs hr, ?_⟩
    rw [mul_smul, hsrm]
  · intro n
    obtain ⟨r, hr, hrn⟩ := h_coker n
    exact Or.inr ⟨r, hr, hrn⟩

/-- Exactness of localization for the tilde construction on `Proj`:
applying `S^{-1}(−)` preserves exactness of a pair of consecutive maps. -/
theorem tilde_proj_exact {R : Type*} [CommRing R]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hex : Function.Exact f g) (S : Submonoid R) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
  LocalizedModule.map_exact S f g hex

/-- Degree-`0` component of the shift `M(d)` equals the degree-`d` component
of `M`, the basic identity behind `Γ(ℙ^n, 𝒪(d)) = S_d`. -/
theorem shiftedModule_degree_zero_eq (k : Type*) [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) :
    (M.twist d).component 0 = M.component d := by
  simp [GradedModuleData.twist]

/-- Dimension formula `dim_k Γ(ℙ^n, 𝒪(d)) = (n+d choose n)` for the degree-`d`
homogeneous component of `k[X_0, …, X_n]`. -/
theorem globalSections_Od_finrank (k : Type*) [Field k] (n d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d) = (n + d).choose n := by
  rw [_root_.homogeneousSubmodule_finrank]
  have h1 : n + 1 + d - 1 = n + d := by omega
  rw [h1, Nat.choose_symm_add.symm]

/-- The degree-`d` homogeneous component of a polynomial ring in finitely many
variables is finite-dimensional over the base. -/
theorem homogeneous_component_finiteDim (k : Type*) [Field k] (n d : ℕ) :
    Module.Finite k (homogeneousSubmodule (Fin n) k d) :=
  _root_.homogeneousSubmodule_finiteDimensional k n d

/-- Surjectivity is preserved by `Submodule.mapQ`: a surjection on the ambient
modules descends to a surjection on the quotients. -/
theorem surjective_mapQ {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (p : Submodule R M) (q : Submodule R N) (hpq : p ≤ Submodule.comap f q) :
    Function.Surjective (p.mapQ q f hpq) := by
  intro y
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective q y
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨Submodule.Quotient.mk m, rfl⟩

/-- The composition of two surjective linear maps is surjective. -/
theorem localization_preserves_surjectivity {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : N →ₗ[R] P) (hg : Function.Surjective g) :
    Function.Surjective (g.comp f) :=
  hg.comp hf

/-- Every finitely generated module admits a surjection from a finite-rank free
module `R^n` (a basic presentation result used to test quasi-coherence). -/
theorem fg_module_quotient_of_free (R : Type*) [CommRing R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨n, (Finsupp.linearCombination R s).comp
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap, ?_⟩
  intro m
  have hm : m ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hm
  obtain ⟨c, rfl⟩ := hm
  exact ⟨Finsupp.linearEquivFunOnFinite R R (Fin n) c, by
    simp [LinearMap.comp_apply, LinearEquiv.symm_apply_apply,
      Finsupp.linearCombination_apply]⟩

/-- Torsion elements are killed by localization at any submonoid containing the
nonzero divisors: a torsion `m` admits an `s ∈ S` with `s • m = 0`. -/
theorem torsion_killed_by_localization {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (S : Submonoid R) (m : M)
    (hm : m ∈ Submodule.torsion R M)
    (hS : nonZeroDivisors R ≤ S) :
    ∃ (t : S), (t : R) • m = 0 := by
  rw [Submodule.mem_torsion_iff] at hm
  obtain ⟨⟨a, ha⟩, ham⟩ := hm
  exact ⟨⟨a, hS ha⟩, ham⟩

/-- For a totally torsion module over a domain, every element is annihilated by
a nonzero scalar. -/
theorem torsion_module_localization_trivial {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (htors : ∀ m : M, m ∈ Submodule.torsion R M)
    (m : M) :
    ∃ (r : R), r ≠ 0 ∧ r • m = 0 := by
  exact (torsion_module_iff_all_torsion.mp htors) m

/-- Component-wise additivity of twists: `M(d₁)(d₂)` and `M(d₁ + d₂)` agree on
every degree component. -/
theorem double_twist_eq_twist_add {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d₁ d₂ : ℤ) (i : ℤ) :
    ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i := by
  simp [GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

/-- Deprecated alias for `double_twist_eq_twist_add`, formerly motivated by
the tensor product identity `𝒪(d₁) ⊗ 𝒪(d₂) ≅ 𝒪(d₁ + d₂)`. -/
@[deprecated double_twist_eq_twist_add (since := "2025-01-01")]
theorem twist_tensor_product_correspondence {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d₁ d₂ : ℤ) (i : ℤ) :
    ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i :=
  double_twist_eq_twist_add M d₁ d₂ i

/-- The zero twist is the identity on every degree component. -/
theorem twist_zero_structure_sheaf {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (i : ℤ) :
    (M.twist 0).component i = M.component i := by
  simp [GradedModuleData.twist]

/-- `Γ(ℙ^n, 𝒪(d)) = S_d`: degree-zero of the shifted module recovers the
degree-`d` piece (graded analog of global sections of a twisted structure sheaf). -/
theorem globalSections_twisted_structure_sheaf {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) :
    (M.twist d).component 0 = M.component d := by
  simp [GradedModuleData.twist]

/-- Dimension formula for `Γ(ℙ^n, 𝒪(d))`, packaged via the `gradedComponent` abbreviation. -/
theorem globalSections_Od_dimension (k : Type*) [Field k] (n d : ℕ) :
    Module.finrank k (gradedComponent k n d) = (n + d).choose n := by
  unfold gradedComponent
  exact globalSections_Od_finrank k n d

/-- The Hilbert function of the homogeneous coordinate ring of `ℙ^n` equals
`binom(n+d, d)`, recovered from `Γ(ℙ^n, 𝒪(d))` via Pascal's symmetry. -/
theorem hilbert_function_via_Od (k : Type*) [Field k] (n d : ℕ) :
    Module.finrank k (gradedComponent k n d) = (n + d).choose d := by
  rw [globalSections_Od_dimension]
  exact Nat.choose_symm_add

/-- The dimensions of the graded components of `k[X_0, …, X_n]` are
nondecreasing in degree. -/
theorem gradedComponent_mono (k : Type*) [Field k] (n d : ℕ) :
    Module.finrank k (gradedComponent k n d) ≤
    Module.finrank k (gradedComponent k n (d + 1)) := by
  simp only [globalSections_Od_dimension]
  exact Nat.choose_le_choose n (by omega)

end QCohProjective

end
