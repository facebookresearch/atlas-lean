/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DegreeAdditivity
import Atlas.AlgebraicGeometryI.code.GrothendieckGroup
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization

open scoped TensorProduct

section TorsionDecomposition

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The torsion submodule of `M`: the submodule of elements killed by some non-zero-divisor of `R`.
This realizes Definition 39 (torsion subsheaf) on curves. -/
def torsionSubmodule (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R M :=
  Submodule.torsion R M

end TorsionDecomposition

section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The saturation of a submodule `N ⊆ M`: the preimage under `M → M/N` of the torsion
submodule of `M/N`. Realizes Definition 40 (saturation) on curves. -/
def Submodule.saturation (N : Submodule R M) : Submodule R M :=
  Submodule.comap N.mkQ (Submodule.torsion R (M ⧸ N))

omit [IsDomain R] in
/-- A submodule is contained in its saturation. -/
theorem Submodule.le_saturation (N : Submodule R M) : N ≤ N.saturation := by
  intro x hx
  simp only [saturation, Submodule.mem_comap]
  have : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
  rw [this]; exact zero_mem _

omit [IsDomain R] in
/-- The image of the saturation `N.saturation` in `M/N` equals the torsion submodule of `M/N`. -/
theorem Submodule.saturation_map_mkQ (N : Submodule R M) :
    Submodule.map N.mkQ N.saturation = Submodule.torsion R (M ⧸ N) := by
  simp only [saturation, Submodule.map_comap_eq, Submodule.range_mkQ, top_inf_eq]

/-- Being torsion-free is preserved under linear isomorphism. -/
theorem isTorsionFree_of_linearEquiv {N P : Type*} [AddCommGroup N] [AddCommGroup P]
    [Module R N] [Module R P] (e : N ≃ₗ[R] P)
    (h : Module.IsTorsionFree R N) : Module.IsTorsionFree R P := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot] at h ⊢
  ext x
  simp only [Submodule.mem_bot, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    have hmem : e.symm x ∈ Submodule.torsion R N := by
      rw [Submodule.mem_torsion_iff]
      refine ⟨⟨a, ha⟩, ?_⟩
      show a • e.symm x = 0
      have hax' : a • x = 0 := hax
      simp [← e.symm.map_smul, hax']
    rw [h, Submodule.mem_bot] at hmem
    exact e.symm.injective (by rw [hmem, map_zero])
  · rintro rfl
    exact ⟨⟨1, Submonoid.one_mem _⟩, by simp⟩

/-- The quotient `M / N.saturation` is torsion-free, by construction of the saturation. -/
theorem Submodule.quotient_saturation_isTorsionFree (N : Submodule R M) :
    Module.IsTorsionFree R (M ⧸ N.saturation) := by
  have h_le : N ≤ N.saturation := N.le_saturation
  let e₁ := Submodule.quotientQuotientEquivQuotient N N.saturation h_le
  have hmap : Submodule.map N.mkQ N.saturation = Submodule.torsion R (M ⧸ N) :=
    N.saturation_map_mkQ
  let e₂ := Submodule.Quotient.equiv (Submodule.torsion R (M ⧸ N))
    (Submodule.map N.mkQ N.saturation)
    (LinearEquiv.refl R (M ⧸ N))
    (by simp [hmap])
  exact isTorsionFree_of_linearEquiv (e₂ ≪≫ₗ e₁) Submodule.QuotientTorsion.instIsTorsionFree

end Saturation

section Rank

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

/-- The rank of an `R`-module `M` (Definition 41): the `K`-dimension of `K ⊗_R M`, where `K` is
a field over `R` (typically the fraction field). -/
noncomputable def CoherentSheavesCurves.sheafRank
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ :=
  Module.finrank K (K ⊗[R] M)

/-- The rank is additive on short exact sequences (when `K` is `R`-flat and the middle term has
finite dimensional base-change). -/
theorem CoherentSheavesCurves.sheafRank_additive
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    [Module.Flat R K] [FiniteDimensional K (K ⊗[R] B)] :
    CoherentSheavesCurves.sheafRank R K B =
      CoherentSheavesCurves.sheafRank R K A + CoherentSheavesCurves.sheafRank R K C := by
  unfold CoherentSheavesCurves.sheafRank

  let f' : K ⊗[R] A →ₗ[K] K ⊗[R] B := f.baseChange K
  let g' : K ⊗[R] B →ₗ[K] K ⊗[R] C := g.baseChange K
  have hf'_fun : ⇑f' = ⇑(f.lTensor K) := (LinearMap.baseChange_eq_ltensor f).symm
  have hg'_fun : ⇑g' = ⇑(g.lTensor K) := (LinearMap.baseChange_eq_ltensor g).symm

  have hinj : Function.Injective f' := by
    rw [Function.Injective, hf'_fun]
    exact fun _ _ h => Module.Flat.lTensor_preserves_injective_linearMap f hf h

  have hsurj : Function.Surjective g' := by
    intro x; rw [hg'_fun]; exact (LinearMap.lTensor_surjective K hg) x

  have hexact : Function.Exact f' g' := by
    intro x; rw [hf'_fun, hg'_fun]; exact (Module.Flat.lTensor_exact K H) x

  haveI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_injective f' hinj
  haveI : Module.Finite K (K ⊗[R] C) := Module.Finite.of_surjective g' hsurj

  have hlen := Module.length_eq_add_of_exact f' g' hinj hsurj hexact
  rw [Module.length_eq_finrank K, Module.length_eq_finrank K, Module.length_eq_finrank K] at hlen
  have : (Module.finrank K (K ⊗[R] B) : ℕ∞) =
      ↑(Module.finrank K (K ⊗[R] A) + Module.finrank K (K ⊗[R] C)) := by
    rw [hlen, Nat.cast_add]
  exact WithTop.coe_injective this

/-- Specialization of `sheafRank_additive` to the case where `K` is the fraction field of an
integral domain `R`, automatically supplying flatness. -/
theorem CoherentSheavesCurves.sheafRank_additive_fractionRing
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    [FiniteDimensional K (K ⊗[R] B)] :
    CoherentSheavesCurves.sheafRank R K B =
      CoherentSheavesCurves.sheafRank R K A + CoherentSheavesCurves.sheafRank R K C := by
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  exact CoherentSheavesCurves.sheafRank_additive R K f g hf hg H

end Rank

section GrothendieckGroup

open DegreeAdditivity in
/-- The Grothendieck group `K_0` of coherent sheaves on a curve, abbreviated through the abstract
construction `GrothendieckGroupK0`. -/
abbrev CoherentSheavesCurves.K0 (R : Type*) [Ring R] := GrothendieckGroupK0 R

open DegreeAdditivity in
/-- The class of an `R`-module `M` in the Grothendieck group `K_0(R)`. -/
abbrev CoherentSheavesCurves.K0.classOf (R : Type*) [Ring R] (M : ModuleCat R) :
    CoherentSheavesCurves.K0 R :=
  GrothendieckGroupK0.classOf R M

/-- A short exact sequence `0 → A → B → C → 0` induces the additivity relation
`[B] = [A] + [C]` in `K_0`. -/
theorem CoherentSheavesCurves.K0.ses_relation (R : Type*) [Ring R]
    {A B C : ModuleCat R} (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    CoherentSheavesCurves.K0.classOf R B =
      CoherentSheavesCurves.K0.classOf R A + CoherentSheavesCurves.K0.classOf R C :=
  DegreeAdditivity.GrothendieckGroupK0.ses_relation R f g hf hg hex

/-- Isomorphic modules have equal classes in the Grothendieck group. -/
theorem CoherentSheavesCurves.K0.classOf_iso (R : Type*) [Ring R]
    (M N : ModuleCat R) (e : M ≃ₗ[R] N) :
    CoherentSheavesCurves.K0.classOf R M = CoherentSheavesCurves.K0.classOf R N :=
  DegreeAdditivity.GrothendieckGroupK0.classOf_iso R M N e

/-- The class of a direct product equals the sum of the classes of the factors in `K_0`. -/
theorem CoherentSheavesCurves.K0.classOf_prod (R : Type*) [Ring R]
    (M N : ModuleCat R) :
    CoherentSheavesCurves.K0.classOf R (ModuleCat.of R (M × N)) =
      CoherentSheavesCurves.K0.classOf R M + CoherentSheavesCurves.K0.classOf R N :=
  DegreeAdditivity.GrothendieckGroupK0.classOf_prod R M N

/-- Universal property of `K_0`: any short-exact-sequence-additive function `ModuleCat R → G`
lifts uniquely to a group homomorphism `K_0(R) →+ G`. -/
noncomputable def CoherentSheavesCurves.K0.lift (R : Type*) [Ring R]
    {G : Type*} [AddCommGroup G]
    (φ : ModuleCat R → G) (hφ : DegreeAdditivity.IsSESAdditive R φ) :
    CoherentSheavesCurves.K0 R →+ G :=
  DegreeAdditivity.GrothendieckGroupK0.lift R φ hφ

/-- The universal lift agrees with the original additive function on each class. -/
theorem CoherentSheavesCurves.K0.lift_classOf (R : Type*) [Ring R]
    {G : Type*} [AddCommGroup G]
    (φ : ModuleCat R → G) (hφ : DegreeAdditivity.IsSESAdditive R φ)
    (M : ModuleCat R) :
    CoherentSheavesCurves.K0.lift R φ hφ (CoherentSheavesCurves.K0.classOf R M) = φ M :=
  DegreeAdditivity.GrothendieckGroupK0.lift_classOf R φ hφ M

/-- Uniqueness of the universal lift: two group homomorphisms from `K_0(R)` agreeing on all
generators `[M]` are equal. -/
theorem CoherentSheavesCurves.K0.lift_unique (R : Type*) [Ring R]
    {G : Type*} [AddCommGroup G]
    (ψ₁ ψ₂ : CoherentSheavesCurves.K0 R →+ G)
    (h : ∀ M : ModuleCat R, ψ₁ (CoherentSheavesCurves.K0.classOf R M) =
      ψ₂ (CoherentSheavesCurves.K0.classOf R M)) :
    ψ₁ = ψ₂ :=
  DegreeAdditivity.GrothendieckGroupK0.lift_unique R ψ₁ ψ₂ h

/-- Deprecated alias for `DegreeAdditivity.K0SESRelation`. -/
@[deprecated DegreeAdditivity.K0SESRelation (since := "2025-06-01")]
def CoherentSheavesCurves.SESRelation (R : Type*) [CommRing R] :=
  DegreeAdditivity.K0SESRelation R

end GrothendieckGroup

section Degree

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The degree of a module `M` over `R`, defined as the `R`-module length of `M` (a value in
`ℕ∞`). On curves this realizes the degree of a torsion coherent sheaf. -/
noncomputable def CoherentSheavesCurves.degree (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R M

/-- Degree is additive on short exact sequences. -/
theorem CoherentSheavesCurves.degree_additive_ses
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    CoherentSheavesCurves.degree R B =
      CoherentSheavesCurves.degree R A + CoherentSheavesCurves.degree R C := by
  exact Module.length_eq_add_of_exact f g hf hg H

/-- Lemma 34: degree additivity on short exact sequences `0 → E → E' → T → 0`. -/
theorem CoherentSheavesCurves.lemma34
    {E E' T : Type*} [AddCommGroup E] [AddCommGroup E'] [AddCommGroup T]
    [Module R E] [Module R E'] [Module R T]
    (f : E →ₗ[R] E') (g : E' →ₗ[R] T)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    CoherentSheavesCurves.degree R E' =
      CoherentSheavesCurves.degree R E + CoherentSheavesCurves.degree R T :=
  Module.length_eq_add_of_exact f g hf hg H

/-- Degree is monotone under injective linear maps. -/
theorem CoherentSheavesCurves.degree_le_of_injective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    CoherentSheavesCurves.degree R A ≤ CoherentSheavesCurves.degree R B :=
  Module.length_le_of_injective f hf

/-- A surjective linear map can only decrease degree. -/
theorem CoherentSheavesCurves.degree_le_of_surjective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    CoherentSheavesCurves.degree R B ≤ CoherentSheavesCurves.degree R A :=
  Module.length_le_of_surjective f hf

/-- For finite-dimensional vector spaces over a division ring, the degree equals the dimension. -/
theorem CoherentSheavesCurves.degree_eq_finrank
    (K : Type*) [DivisionRing K] (V : Type*) [AddCommGroup V] [Module K V]
    [Module.Finite K V] :
    CoherentSheavesCurves.degree K V = Module.finrank K V :=
  Module.length_eq_finrank K V

/-- Degree is additive on direct products of modules. -/
theorem CoherentSheavesCurves.degree_prod
    (R : Type*) [Ring R]
    (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    CoherentSheavesCurves.degree R (M × N) =
      CoherentSheavesCurves.degree R M + CoherentSheavesCurves.degree R N := by
  exact Module.length_prod R M N

end Degree

section TorsionRank

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A torsion module has rank zero (its base-change to the fraction field vanishes). -/
theorem CoherentSheavesCurves.sheafRank_of_torsion
    {M : Type*} [AddCommGroup M] [Module R M]
    (hM : Module.IsTorsion R M) :
    CoherentSheavesCurves.sheafRank R K M = 0 := by
  unfold CoherentSheavesCurves.sheafRank


  have hsub : Subsingleton (K ⊗[R] M) := by
    constructor
    intro x y
    suffices h : ∀ z : K ⊗[R] M, z = 0 by rw [h x, h y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul k m =>
      obtain ⟨⟨r, hr⟩, hrm⟩ := @hM m
      have hr_ne : r ≠ 0 := nonZeroDivisors.ne_zero hr
      have hrm' : r • m = 0 := by simpa using hrm

      have h1 : (r • k) ⊗ₜ[R] m = k ⊗ₜ[R] (r • m) := TensorProduct.smul_tmul r k m

      rw [show r • k = algebraMap R K r * k from Algebra.smul_def r k] at h1
      have h2 : (algebraMap R K r * k) ⊗ₜ[R] m = (0 : K ⊗[R] M) := by
        rw [h1, hrm', TensorProduct.tmul_zero]
      have halg_ne : algebraMap R K r ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
      calc k ⊗ₜ[R] m
          = ((algebraMap R K r)⁻¹ * (algebraMap R K r)) • k ⊗ₜ[R] m := by
              rw [inv_mul_cancel₀ halg_ne, one_smul]
        _ = ((algebraMap R K r)⁻¹ * (algebraMap R K r * k)) ⊗ₜ[R] m := by
              rw [mul_smul]; rfl
        _ = (algebraMap R K r)⁻¹ • ((algebraMap R K r * k) ⊗ₜ[R] m) := by
              rw [TensorProduct.smul_tmul']; simp
        _ = 0 := by rw [h2, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact @Module.finrank_zero_of_subsingleton K (K ⊗[R] M) _ _ _ _ hsub

end TorsionRank

section DegreeViaDeterminant

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- A linear isomorphism transports the `NoZeroSMulDivisors` property along its inverse direction. -/
theorem noZeroSMulDivisors_of_linearEquiv
    {R' : Type*} [CommRing R'] [IsDomain R']
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [AddCommGroup M₂] [Module R' M₂] [NoZeroSMulDivisors R' M₂]
    (e : M₁ ≃ₗ[R'] M₂) : NoZeroSMulDivisors R' M₁ where
  eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
    have h' : r • e x = 0 := by rw [← e.map_smul, h, map_zero]
    rcases smul_eq_zero.mp h' with hr | hx
    · left; exact hr
    · right; exact e.injective (by rw [hx, map_zero])








end DegreeViaDeterminant
