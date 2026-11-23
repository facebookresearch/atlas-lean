/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.NumberTheory.NumberField.Basic
import Atlas.NumberTheoryI.code.Pairings

open Module

noncomputable section


section DualModule

variable {A : Type*} [CommRing A]
variable {M N P : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

theorem dual_map_apply (φ : M →ₗ[A] N) (g : Module.Dual A N) (m : M) :
    φ.dualMap g m = g (φ m) :=
  LinearMap.dualMap_apply φ g m

end DualModule


section DualDirectSum

variable (A : Type*) [CommRing A]
variable (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def dualDirectSumEquiv :
    Module.Dual A (M × N) ≃ₗ[A] Module.Dual A M × Module.Dual A N :=
  (Module.dualProdDualEquivDual A M N).symm

end DualDirectSum


section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def colonSubmodule (M : Submodule A K) : Submodule A K where
  carrier := {x : K | ∀ m : K, m ∈ M → x * m ∈ (algebraMap A K).range}
  add_mem' := by
    intro x y hx hy m hm; rw [add_mul]
    exact (algebraMap A K).range.add_mem (hx m hm) (hy m hm)
  zero_mem' := by intro m _; rw [zero_mul]; exact (algebraMap A K).range.zero_mem
  smul_mem' := by
    intro c x hx m hm; rw [Algebra.smul_def, mul_assoc]
    exact (algebraMap A K).range.mul_mem ⟨c, rfl⟩ (hx m hm)


noncomputable def colonToA (M : Submodule A K) (x : colonSubmodule A K M) (m : M) : A :=
  (x.2 (m : K) m.2).choose

omit [IsDomain A] [IsFractionRing A K] in
theorem colonToA_spec (M : Submodule A K) (x : colonSubmodule A K M) (m : M) :
    algebraMap A K (colonToA A K M x m) = (x : K) * (m : K) :=
  (x.2 (m : K) m.2).choose_spec

noncomputable def colonToDualMap (M : Submodule A K) :
    colonSubmodule A K M →ₗ[A] Module.Dual A M where
  toFun x :=
    { toFun := fun m => colonToA A K M x m
      map_add' := by
        intro m₁ m₂
        apply IsFractionRing.injective A K
        simp only [map_add, colonToA_spec]
        push_cast; ring
      map_smul' := by
        intro c m
        apply IsFractionRing.injective A K
        simp only [colonToA_spec, smul_eq_mul, map_mul, RingHom.id_apply]
        push_cast; rw [Algebra.smul_def]; ring }
  map_add' := by
    intro x₁ x₂; ext m
    apply IsFractionRing.injective A K
    simp only [LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec, LinearMap.add_apply, map_add]
    push_cast; ring
  map_smul' := by
    intro c x; ext m
    apply IsFractionRing.injective A K
    simp only [LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec, LinearMap.smul_apply,
               smul_eq_mul, map_mul, RingHom.id_apply]
    push_cast; rw [Algebra.smul_def]; ring

theorem dual_symmetric_relation (M : Submodule A K) (f : Module.Dual A M) (m₁ m₂ : M) :
    (m₁ : K) * algebraMap A K (f m₂) = (m₂ : K) * algebraMap A K (f m₁) := by
  obtain ⟨a₁, b₁, hb₁, hm₁⟩ := IsFractionRing.div_surjective A (m₁ : K)
  obtain ⟨a₂, b₂, hb₂, hm₂⟩ := IsFractionRing.div_surjective A (m₂ : K)
  have hb₁' := map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) hb₁
  have hb₂' := map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) hb₂
  have key₁ : algebraMap A K b₁ * (m₁ : K) = algebraMap A K a₁ := by rw [← hm₁]; field_simp
  have key₂ : algebraMap A K b₂ * (m₂ : K) = algebraMap A K a₂ := by rw [← hm₂]; field_simp
  have hm₁_mem : algebraMap A K a₁ ∈ M := by
    rw [← key₁, ← Algebra.smul_def]; exact M.smul_mem b₁ m₁.2
  have hm₂_mem : algebraMap A K a₂ ∈ M := by
    rw [← key₂, ← Algebra.smul_def]; exact M.smul_mem b₂ m₂.2
  have eq₁ : f ⟨algebraMap A K a₁, hm₁_mem⟩ = b₁ * f m₁ := by
    have : (⟨algebraMap A K a₁, hm₁_mem⟩ : M) = b₁ • m₁ := by
      ext; simp [Algebra.smul_def, key₁]
    rw [this, map_smul, smul_eq_mul]
  have eq₂ : f ⟨algebraMap A K a₂, hm₂_mem⟩ = b₂ * f m₂ := by
    have : (⟨algebraMap A K a₂, hm₂_mem⟩ : M) = b₂ • m₂ := by
      ext; simp [Algebra.smul_def, key₂]
    rw [this, map_smul, smul_eq_mul]
  rw [show (m₁ : K) = algebraMap A K a₁ / algebraMap A K b₁ from hm₁.symm,
      show (m₂ : K) = algebraMap A K a₂ / algebraMap A K b₂ from hm₂.symm,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hb₁' hb₂']
  simp only [← map_mul]; congr 1
  calc a₁ * f m₂ * b₂
      = a₁ * (b₂ * f m₂) := by ring
    _ = a₁ * f ⟨algebraMap A K a₂, hm₂_mem⟩ := by rw [← eq₂]
    _ = f (a₁ • ⟨algebraMap A K a₂, hm₂_mem⟩) := by rw [map_smul, smul_eq_mul]
    _ = f (a₂ • ⟨algebraMap A K a₁, hm₁_mem⟩) := by
        congr 1; ext; simp [Algebra.smul_def, mul_comm]
    _ = a₂ * f ⟨algebraMap A K a₁, hm₁_mem⟩ := by rw [map_smul, smul_eq_mul]
    _ = a₂ * (b₁ * f m₁) := by rw [eq₁]
    _ = a₂ * f m₁ * b₁ := by ring

theorem dual_apply_via_element (M : Submodule A K) (f : Module.Dual A M)
    (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) (m : M) :
    algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (m : K) = algebraMap A K (f m) := by
  rw [← mul_right_inj' hm₀]
  calc (m₀ : K) * (algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (m : K))
      = (m₀ : K) * (m₀ : K)⁻¹ * (algebraMap A K (f m₀) * (m : K)) := by ring
    _ = 1 * (algebraMap A K (f m₀) * (m : K)) := by rw [mul_inv_cancel₀ hm₀]
    _ = (m : K) * algebraMap A K (f m₀) := by ring
    _ = (m₀ : K) * algebraMap A K (f m) := dual_symmetric_relation A K M f m m₀

noncomputable def dualToColonMap (M : Submodule A K) (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) :
    Module.Dual A M →ₗ[A] colonSubmodule A K M where
  toFun f := ⟨algebraMap A K (f m₀) * (m₀ : K)⁻¹, by
    intro m hm
    rw [show algebraMap A K (f m₀) * (m₀ : K)⁻¹ * m =
          algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (⟨m, hm⟩ : M) from rfl]
    rw [dual_apply_via_element A K M f m₀ hm₀ ⟨m, hm⟩]
    exact ⟨f ⟨m, hm⟩, rfl⟩⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    show algebraMap A K ((f + g) m₀) * (↑m₀)⁻¹ =
      algebraMap A K (f m₀) * (↑m₀)⁻¹ + algebraMap A K (g m₀) * (↑m₀)⁻¹
    simp only [LinearMap.add_apply, map_add, add_mul]
  map_smul' := by
    intro c f
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]

noncomputable def dualEquivColonSubmodule (M : Submodule A K) (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) :
    Module.Dual A M ≃ₗ[A] colonSubmodule A K M :=
  LinearEquiv.ofLinear
    (dualToColonMap A K M m₀ hm₀)
    (colonToDualMap A K M)
    (by
      ext ⟨x, hx⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      show (dualToColonMap A K M m₀ hm₀ (colonToDualMap A K M ⟨x, hx⟩) : K) = x
      simp only [dualToColonMap, colonToDualMap, LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec]
      rw [mul_assoc]
      rw [mul_inv_cancel₀ hm₀, mul_one])
    (by
      ext f m
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      simp only [dualToColonMap, colonToDualMap, LinearMap.coe_mk, AddHom.coe_mk]
      apply IsFractionRing.injective A K
      rw [colonToA_spec]
      exact dual_apply_via_element A K M f m₀ hm₀ m)

end DualColonSubmodule


section DualInvertibleFractionalIdeal

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

theorem colonSubmodule_eq_coe_inv (M : FractionalIdeal A⁰ K) (hM : M ≠ 0) :
    colonSubmodule A K (↑M : Submodule A K) = (↑(M⁻¹) : Submodule A K) := by
  ext x
  simp only [colonSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk]
  constructor
  · intro hx
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hM]
    intro y hy
    rw [FractionalIdeal.mem_one_iff]
    exact hx y (FractionalIdeal.mem_coe.mp hy)
  · intro hx m hm
    have hx' := FractionalIdeal.mem_coe.mp hx
    rw [FractionalIdeal.mem_inv_iff hM] at hx'
    have := hx' m (FractionalIdeal.mem_coe.mpr hm)
    rw [FractionalIdeal.mem_one_iff] at this
    exact this

def nonzeroElemOfFractionalIdeal (M : FractionalIdeal A⁰ K) (hM : M ≠ 0) :
    {m : (↑M : Submodule A K) // (m : K) ≠ 0} :=
  let h := FractionalIdeal.exists_ne_zero_mem_isInteger hM
  let x := h.choose
  let hx := h.choose_spec
  ⟨⟨algebraMap A K x, hx.2⟩,
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hx.1⟩

def dualEquivInverse
    (M : FractionalIdeal A⁰ K) (hM : IsUnit M) :
    Module.Dual A (↑M : Submodule A K) ≃ₗ[A] (↑(M⁻¹) : Submodule A K) :=
  let hMne : M ≠ 0 := by intro h; rw [h] at hM; exact not_isUnit_zero hM
  let ⟨m₀, hm₀⟩ := nonzeroElemOfFractionalIdeal A K M hMne
  (dualEquivColonSubmodule A K (↑M) m₀ hm₀).trans
    (LinearEquiv.ofEq _ _ (colonSubmodule_eq_coe_inv A K M hMne))

def doubleDualEquiv
    (M : FractionalIdeal A⁰ K) (hM : IsUnit M) :
    Module.Dual A (Module.Dual A (↑M : Submodule A K)) ≃ₗ[A] (↑M : Submodule A K) :=
  let hMinvU : IsUnit M⁻¹ := by
    rw [isUnit_iff_exists_inv]
    exact ⟨M, by rw [mul_comm]; exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hM⟩
  let hMinv_inv_eq : M⁻¹⁻¹ = M := by
    rw [← FractionalIdeal.right_inverse_eq K M⁻¹ M]
    rw [mul_comm]
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hM

  let e₁ := dualEquivInverse A K M hM

  let e₂ := e₁.dualMap.symm

  let e₃ := dualEquivInverse A K M⁻¹ hMinvU

  let e₄ := LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule hMinv_inv_eq)
  e₂.trans (e₃.trans e₄)

end DualInvertibleFractionalIdeal


section DualBasis

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {n : ℕ}

theorem dualBasisProperty {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Basis ι A M) (i j : ι) :
    b.dualBasis i (b j) = if j = i then 1 else 0 :=
  b.dualBasis_apply_self i j

end DualBasis


section PerfectPairingDualBasis

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {ι : Type*} [DecidableEq ι] [Finite ι]

def perfPairingDualBasis (p : M →ₗ[A] M →ₗ[A] A) [p.IsPerfPair] (b : Basis ι A M) :
    Basis ι A M :=
  b.dualBasis.map p.toPerfPair.symm

end PerfectPairingDualBasis


section DualLattice

end DualLattice


section DualLatticeDirectSum

variable (A : Type*) [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (V₁ V₂ : Type*) [AddCommGroup V₁] [Module K V₁] [Module A V₁] [IsScalarTower A K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module A V₂] [IsScalarTower A K V₂]

end DualLatticeDirectSum


section PrimeChainContraction

theorem prime_chain_contracts_of_integral
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B]
    {q₀ q₁ : Ideal B} [q₀.IsPrime] (hlt : q₀ < q₁) :
    q₀.comap (algebraMap A B) < q₁.comap (algebraMap A B) := by
  obtain ⟨hle, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxJ, hxI⟩
    (Algebra.IsIntegral.isIntegral x)

end PrimeChainContraction


section IntegralClosureDedekind

theorem integral_closure_isDedekindDomain
    (A : Type*) (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L]
    (C : Type*) [CommRing C]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
    [FiniteDimensional K L] [IsDomain A] [Algebra.IsSeparable K L]
    [IsDomain C] [IsDedekindDomain A] :
    IsDedekindDomain C :=
  IsIntegralClosure.isDedekindDomain A K L C

end IntegralClosureDedekind


section RingOfIntegersDedekind

open NumberField

theorem ringOfIntegers_isDedekindDomain
    (K : Type*) [Field K] [NumberField K] :
    IsDedekindDomain (𝓞 K) :=
  inferInstance

end RingOfIntegersDedekind

end
