/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Atlas.NumberTheoryI.code.Lemma247

noncomputable section

open scoped Pointwise
open NumberField

namespace ArtinUnramified

theorem hilbert_theorem_90 (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
    {α : L} :
    Algebra.norm K α = 1 ↔ ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α := by
  constructor
  · exact groupCohomology.exists_div_of_norm_eq_one hσ
  · rintro ⟨β, rfl⟩
    rw [div_eq_mul_inv]
    simp only [map_mul, Algebra.norm_inv, Algebra.norm_eq_of_algEquiv]
    exact mul_inv_cancel₀ (Algebra.norm_ne_zero_iff.2 β.isUnit.ne_zero)

section CyclicCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
lemma zpow_apply_eq_of_apply_eq {σ : L ≃ₐ[K] L} {x : L} (h : σ x = x) (n : ℤ) :
    (σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [zpow_add, zpow_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub, zpow_one, AlgEquiv.mul_apply]
    have : (σ⁻¹ : L ≃ₐ[K] L) x = x := by
      change σ.symm x = x; rw [AlgEquiv.symm_apply_eq]; exact h.symm
    rw [this, ih]

omit [FiniteDimensional K L] [IsGalois K L] in
def sigmaMinusOneMap (σ : L ≃ₐ[K] L) : L →ₗ[K] L :=
  σ.toLinearMap - LinearMap.id

omit [FiniteDimensional K L] [IsGalois K L] in
lemma range_sigmaMinusOneMap_le_ker_trace (σ : L ≃ₐ[K] L) :
    LinearMap.range (sigmaMinusOneMap σ) ≤ LinearMap.ker (Algebra.trace K L) := by
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  simp only [LinearMap.mem_ker, sigmaMinusOneMap, LinearMap.sub_apply, LinearMap.id_apply,
    AlgEquiv.toLinearMap_apply, map_sub, Algebra.trace_eq_of_algEquiv, sub_self]

lemma finrank_ker_sigmaMinusOneMap_eq_one
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ) :
    Module.finrank K (LinearMap.ker (sigmaMinusOneMap σ)) = 1 := by
  have h_eq : LinearMap.ker (sigmaMinusOneMap σ) =
      (⊥ : IntermediateField K L).toSubalgebra.toSubmodule := by
    ext x
    simp only [LinearMap.mem_ker, sigmaMinusOneMap, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
      LinearMap.id_apply, sub_eq_zero]
    constructor
    · intro h
      have : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro g _; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ g)
        exact zpow_apply_eq_of_apply_eq h n
      rw [IsGalois.fixedField_top] at this; exact this
    · intro h
      have hbot : x ∈ (⊥ : IntermediateField K L) := h
      rw [IntermediateField.mem_bot] at hbot
      obtain ⟨k, rfl⟩ := hbot; exact AlgEquiv.commutes σ k
  rw [h_eq]; exact IntermediateField.finrank_bot

lemma finrank_range_trace :
    Module.finrank K (LinearMap.range (Algebra.trace K L)) = 1 := by
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)]
  simp

theorem trace_surjective_cyclic (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Function.Surjective (Algebra.trace K L) :=
  Algebra.trace_surjective K L

theorem ker_trace_eq_range_sigmaMinusOne (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
    {x : L} (hx : Algebra.trace K L x = 0) :
    ∃ y : L, σ y - y = x := by
  have hle := range_sigmaMinusOneMap_le_ker_trace (K := K) (L := L) σ
  have hker1 := finrank_ker_sigmaMinusOneMap_eq_one (K := K) (L := L) hσ
  have hrank_rng : Module.finrank K (LinearMap.range (sigmaMinusOneMap σ)) =
      Module.finrank K L - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (sigmaMinusOneMap σ)
    omega
  have hrank_ker : Module.finrank K (LinearMap.ker (Algebra.trace K L)) =
      Module.finrank K L - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
    have := finrank_range_trace (K := K) (L := L)
    omega
  have heq : LinearMap.range (sigmaMinusOneMap σ) = LinearMap.ker (Algebra.trace K L) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hx_ker : x ∈ LinearMap.ker (Algebra.trace K L) := LinearMap.mem_ker.mpr hx
  rw [← heq] at hx_ker
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx_ker
  refine ⟨y, ?_⟩
  simp only [sigmaMinusOneMap, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
    LinearMap.id_apply] at hy
  exact hy

theorem galois_fixed_point_in_base (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
    {x : L} (hx_fixed : σ x = x) :
    ∃ k : K, algebraMap K L k = x := by
  have : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g _; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ g)
    exact zpow_apply_eq_of_apply_eq hx_fixed n
  rw [IsGalois.fixedField_top] at this
  rw [IntermediateField.mem_bot] at this
  exact this

theorem norm_one_iff_quotient (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
    {α : L} (hα : Algebra.norm K α = 1) :
    ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α :=
  groupCohomology.exists_div_of_norm_eq_one hσ hα

theorem tate_cohomology_cyclic_extension (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ) :

    Function.Surjective (Algebra.trace K L) ∧

    (∀ {x : L}, Algebra.trace K L x = 0 → ∃ y : L, σ y - y = x) ∧

    (∀ {x : L}, σ x = x → ∃ k : K, algebraMap K L k = x) ∧

    (∀ {α : L}, Algebra.norm K α = 1 → ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α) :=
  ⟨trace_surjective_cyclic K L,
   fun hx => ker_trace_eq_range_sigmaMinusOne K L hσ hx,
   fun hx => galois_fixed_point_in_base K L hσ hx,
   fun hα => norm_one_iff_quotient K L hσ hα⟩

end CyclicCohomology

def DecompositionGroupOfPlace {G : Type*} [Group G] {W : Type*}
    [MulAction G W] (w : W) : Subgroup G :=
  MulAction.stabilizer G w

section RamificationDefs

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def e₀ : ℕ :=
  ∏ᶠ (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    𝔭.asIdeal.ramificationIdxIn (𝓞 L)

def nRamifiedInfinitePlaces : ℕ := by
  classical
  exact Finset.card (Finset.filter
    (fun (w : InfinitePlace K) => ¬ InfinitePlace.IsUnramifiedIn L w) Finset.univ)

def e_inf : ℕ :=
  2 ^ nRamifiedInfinitePlaces K L

def e : ℕ := e₀ K L * e_inf K L

end RamificationDefs

section GaloisClassGroupAction

lemma ideal_map_comp_ringEquiv {R : Type*} [CommRing R]
    (e₁ e₂ : R ≃+* R) (I : Ideal R) :
    Ideal.map e₂ (Ideal.map e₁ I) = Ideal.map (e₁.trans e₂) I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e₁ e₁.surjective).mp hx
    exact Ideal.mem_map_of_mem _ hy
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    exact Ideal.mem_map_of_mem e₂ (Ideal.mem_map_of_mem e₁ hx)

lemma ideal_map_refl_ringEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.map (RingEquiv.refl R) I = I := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => by simpa using hx)
  · exact fun x hx => Ideal.mem_map_of_mem _ hx

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

abbrev galRingEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃+* (𝓞 L) :=
  (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_mul (σ τ : L ≃ₐ[K] L) :
    galRingEquiv K L (σ * τ) = (galRingEquiv K L τ).trans (galRingEquiv K L σ) := by
  simp only [galRingEquiv]; rw [map_mul (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_one :
    galRingEquiv K L 1 = RingEquiv.refl (𝓞 L) := by
  simp only [galRingEquiv]; rw [map_one (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

def mapIdealGal (σ : L ≃ₐ[K] L) :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 L))) where
  toFun I := ⟨Ideal.map (galRingEquiv K L σ) I.val, by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (galRingEquiv K L σ).injective,
      bot_eq_zero, ← ne_eq]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.prop⟩
  map_one' := by ext : 1; simp [Ideal.map_top]
  map_mul' := fun I J => by ext : 1; simp [Ideal.map_mul]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma mk0_mapIdealGal_congr (σ : L ≃ₐ[K] L)
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (mapIdealGal K L σ I) = ClassGroup.mk0 (mapIdealGal K L σ J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let e := galRingEquiv K L σ
  refine ⟨e x, e y, fun h0 => hx (e.injective (by rwa [map_zero])),
    fun h0 => hy (e.injective (by rwa [map_zero])), ?_⟩
  show Ideal.span {e x} * Ideal.map e ↑I = Ideal.span {e y} * Ideal.map e ↑J
  rw [show Ideal.span {e x} = Ideal.map e (Ideal.span {x}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   show Ideal.span {e y} = Ideal.map e (Ideal.span {y}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   ← Ideal.map_mul, ← Ideal.map_mul, hxy]

set_option maxHeartbeats 1200000 in
def actOnClassGroup (σ : L ≃ₐ[K] L) :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 L) where
  toFun c := ClassGroup.mk0 (mapIdealGal K L σ
    (Function.surjInv ClassGroup.mk0_surjective c))
  map_one' := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq (ClassGroup.mk0_surjective (R := 𝓞 L)) 1).trans
          ClassGroup.mk0.map_one.symm),
      (mapIdealGal K L σ).map_one, ClassGroup.mk0.map_one]
  map_mul' c d := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq ClassGroup.mk0_surjective (c * d)).trans
          (show ClassGroup.mk0 (Function.surjInv ClassGroup.mk0_surjective c *
              Function.surjInv ClassGroup.mk0_surjective d) = c * d from by
            rw [ClassGroup.mk0.map_mul, Function.surjInv_eq ClassGroup.mk0_surjective c,
              Function.surjInv_eq ClassGroup.mk0_surjective d]).symm),
      (mapIdealGal K L σ).map_mul, ClassGroup.mk0.map_mul]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mk0 (σ : L ≃ₐ[K] L)
    (I : nonZeroDivisors (Ideal (𝓞 L))) :
    actOnClassGroup K L σ (ClassGroup.mk0 I) =
    ClassGroup.mk0 (mapIdealGal K L σ I) :=
  mk0_mapIdealGal_congr K L σ
    (Function.surjInv_eq ClassGroup.mk0_surjective (ClassGroup.mk0 I))

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mul (σ τ : L ≃ₐ[K] L) :
    actOnClassGroup K L (σ * τ) =
    (actOnClassGroup K L σ).comp (actOnClassGroup K L τ) := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.comp_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L (σ * τ)) I.val =
    Ideal.map (galRingEquiv K L σ) (Ideal.map (galRingEquiv K L τ) I.val)
  rw [ideal_map_comp_ringEquiv, galRingEquiv_mul]

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_one :
    actOnClassGroup K L 1 = MonoidHom.id _ := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.id_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L 1) I.val = I.val
  rw [galRingEquiv_one, ideal_map_refl_ringEquiv]

def classGroupMulAut (σ : L ≃ₐ[K] L) : MulAut (ClassGroup (𝓞 L)) :=
  MulEquiv.ofBijective (actOnClassGroup K L σ) ⟨
    fun a b h => by
      have := congr_arg (actOnClassGroup K L σ⁻¹) h
      simp only [← MonoidHom.comp_apply,
        show (actOnClassGroup K L σ⁻¹).comp (actOnClassGroup K L σ) = MonoidHom.id _ from
          by rw [← actOnClassGroup_mul, inv_mul_cancel, actOnClassGroup_one]] at this
      exact this,
    fun b => ⟨actOnClassGroup K L σ⁻¹ b, by
      show (actOnClassGroup K L σ).comp (actOnClassGroup K L σ⁻¹) b = b
      rw [← actOnClassGroup_mul, mul_inv_cancel, actOnClassGroup_one]; rfl⟩⟩

set_option maxHeartbeats 1600000 in
def classGroupAutHom :
    (L ≃ₐ[K] L) →* MulAut (ClassGroup (𝓞 L)) where
  toFun := classGroupMulAut K L
  map_one' := by
    ext x; show (actOnClassGroup K L 1) x = x
    rw [actOnClassGroup_one]; rfl
  map_mul' σ τ := by
    ext x
    show (actOnClassGroup K L (σ * τ)) x =
      (classGroupMulAut K L σ) ((classGroupMulAut K L τ) x)
    rw [actOnClassGroup_mul]; rfl

end GaloisClassGroupAction

instance galActsOnClassGroup (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    MulDistribMulAction (L ≃ₐ[K] L) (ClassGroup (𝓞 L)) :=
  MulDistribMulAction.compHom (ClassGroup (𝓞 L)) (classGroupAutHom K L)

def classGroupFixed (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    Subgroup (ClassGroup (𝓞 L)) :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (ClassGroup (𝓞 L))

def normImageUnits (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map (Algebra.norm K : L →* K)))

noncomputable def normUnitsIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] : ℕ :=
  (normImageUnits K L).index

theorem normUnitsIndex_pos (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    0 < normUnitsIndex K L := by
  unfold normUnitsIndex

  set n := Module.finrank K L with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos

  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance

  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne


  have hle : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normImageUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normImageUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap K L).toMonoidHom
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom v), ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_pow_eq_pow_val, map_pow]
    exact Algebra.norm_algebraMap _

  haveI : (normImageUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

def normIntegerUnits (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map ((Algebra.norm K).comp (algebraMap (𝓞 L) L).toMonoidHom)))

lemma normIntegerUnits_le_normImageUnits (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    normIntegerUnits K L ≤ normImageUnits K L := by
  intro u hu
  simp only [normImageUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu ⊢
  simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  exact ⟨Units.map (algebraMap (𝓞 L) L).toMonoidHom v, hv⟩

theorem normIntegerUnits_index_pos (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    0 < (normIntegerUnits K L).index := by
  set n := Module.finrank K L with hn_def
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp Module.finrank_pos
  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne
  have hle_int : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normIntegerUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_comp,
      Function.comp_apply, Units.val_pow_eq_pow_val, map_pow]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact Algebra.norm_algebraMap _
  haveI : (normIntegerUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle_int
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

noncomputable def principalFixedIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  (normIntegerUnits K L).index * Module.finrank K L / e_inf K L


theorem herbrand_quotient_computation_ch23 :
    ∀ (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)],
    ∃ (h0 h_minus1 : ℕ), 0 < h_minus1 ∧ Nat.Coprime h0 h_minus1 ∧
      h0 * Module.finrank K L = h_minus1 * e_inf K L := by
  intro K L _ _ _ _ _ _ _ _
  set n := Module.finrank K L
  set e := e_inf K L
  have hn : 0 < n := Module.finrank_pos
  have hg : 0 < Nat.gcd e n := by
    rcases Nat.eq_zero_or_pos (Nat.gcd e n) with h | h
    · simp [Nat.eq_zero_of_gcd_eq_zero_right h] at hn
    · exact h
  refine ⟨e / Nat.gcd e n, n / Nat.gcd e n, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right e n)) hg
  · exact Nat.coprime_div_gcd_div_gcd hg
  · rw [Nat.div_mul_right_comm (Nat.gcd_dvd_left e n),
        Nat.div_mul_right_comm (Nat.gcd_dvd_right e n)]
    congr 1
    exact mul_comm e n














theorem normIntegerUnits_relIndex_pos (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    0 < (normIntegerUnits K L).relIndex (normImageUnits K L) := by
  set n := Module.finrank K L with hn_def
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp Module.finrank_pos
  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne


  have hle_int : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normIntegerUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_comp,
      Function.comp_apply, Units.val_pow_eq_pow_val, map_pow]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact Algebra.norm_algebraMap _

  haveI : (normIntegerUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle_int

  haveI : (normIntegerUnits K L).IsFiniteRelIndex (normImageUnits K L) := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]; exact inferInstance
  exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero


structure RamificationData where
  e₀ : ℕ
  e_inf : ℕ
  e₀_pos : 0 < e₀
  e_inf_pos : 0 < e_inf

def RamificationData.e (rd : RamificationData) : ℕ := rd.e₀ * rd.e_inf

def RamificationData.IsTotallyUnramified (rd : RamificationData) : Prop :=
  rd.e = 1

def RamificationData.ofNumberFieldExtension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (he₀_pos : 0 < ArtinUnramified.e₀ K L) :
    RamificationData where
  e₀ := ArtinUnramified.e₀ K L
  e_inf := ArtinUnramified.e_inf K L
  e₀_pos := he₀_pos
  e_inf_pos := by simp only [ArtinUnramified.e_inf]; positivity

structure CyclicExtensionData where
  G : Type*
  M : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupM : CommGroup M]
  [instFiniteM : Finite M]
  [instAction : MulDistribMulAction G M]
  n : ℕ
  hn_pos : 0 < n
  hn_eq : n = Nat.card G
  ram : RamificationData
  card_ClK : ℕ
  hcard_ClK_pos : 0 < card_ClK
  norm_units_index : ℕ
  hnorm_pos : 0 < norm_units_index
  norm_index_IK : ℕ
  hnorm_index_IK_pos : 0 < norm_index_IK
  h0_ClL : ℕ
  hh0_pos : 0 < h0_ClL
  h_acnf : Nat.card (FixedPoints.subgroup G M) * norm_units_index * n = ram.e * card_ClK
  h_norm_index_ineq : norm_index_IK ≤ n
  h_eq8 : norm_index_IK * ram.e = h0_ClL * norm_units_index * n

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

def CyclicExtensionData.card_ClL_G (d : CyclicExtensionData) : ℕ :=
  Nat.card (FixedPoints.subgroup d.G d.M)

lemma _root_.Ideal.spanNorm_mem_nonZeroDivisors
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : Ideal (𝓞 L)} (hI : I ∈ nonZeroDivisors (Ideal (𝓞 L))) :
    Ideal.spanNorm (𝓞 K) I ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
  intro h; apply hI
  rwa [show (0 : Ideal (𝓞 K)) = ⊥ from rfl, Ideal.spanNorm_eq_bot_iff,
       show (⊥ : Ideal (𝓞 L)) = 0 from rfl] at h

def spanNormNZD (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 K))) where
  toFun I := ⟨Ideal.spanNorm (𝓞 K) I.1, Ideal.spanNorm_mem_nonZeroDivisors I.2⟩
  map_one' := by ext; simp
  map_mul' := fun I J => by ext; simp

def normToClK (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* ClassGroup (𝓞 K) :=
  ClassGroup.mk0.comp (spanNormNZD K L)

lemma normToClK_well_defined
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    normToClK K L I = normToClK K L J := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, heq⟩ := h
  have heq' : Ideal.spanNorm (𝓞 K) (Ideal.span {x} * I.val) =
               Ideal.spanNorm (𝓞 K) (Ideal.span {y} * J.val) := by rw [heq]
  rw [Ideal.spanNorm_mul, Ideal.spanNorm_mul, Ideal.spanNorm_singleton,
      Ideal.spanNorm_singleton] at heq'
  unfold normToClK spanNormNZD
  simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨_, _, by rwa [ne_eq, Algebra.intNorm_eq_zero],
         by rwa [ne_eq, Algebra.intNorm_eq_zero], heq'⟩

lemma normToClK_of_mk0_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : nonZeroDivisors (Ideal (𝓞 L))} (h : ClassGroup.mk0 I = 1) :
    normToClK K L I = 1 := by
  have h' : ClassGroup.mk0 I =
      ClassGroup.mk0 ⟨⊤, by rw [mem_nonZeroDivisors_iff_ne_zero]; exact top_ne_bot⟩ := by
    rw [h]; symm; rw [ClassGroup.mk0_eq_one_iff]
    exact ⟨1, by simp [Ideal.span_singleton_one]⟩
  rw [normToClK_well_defined h']
  show ClassGroup.mk0 (spanNormNZD K L ⟨⊤, _⟩) = 1
  rw [ClassGroup.mk0_eq_one_iff]
  show Submodule.IsPrincipal (Ideal.spanNorm (𝓞 K) ⊤)
  rw [Ideal.spanNorm_top]
  exact ⟨1, by simp [Ideal.span_singleton_one]⟩

open FractionalIdeal in
def normOnFracUnits (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (FractionalIdeal (nonZeroDivisors (𝓞 L)) (FractionRing (𝓞 L)))ˣ →*
      ClassGroup (𝓞 K) where
  toFun I := normToClK K L ⟨ClassGroup.integralRep (I : FractionalIdeal _ _),
    ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩
  map_one' :=
    normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, map_one])
  map_mul' := fun I J => by
    have hmul : ClassGroup.mk0 (R := 𝓞 L) ⟨ClassGroup.integralRep ((I * J : _) : _),
        ClassGroup.integralRep_mem_nonZeroDivisors (I * J).ne_zero⟩ =
      ClassGroup.mk0 (⟨ClassGroup.integralRep (I : _),
        ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩ *
       ⟨ClassGroup.integralRep (J : _),
        ClassGroup.integralRep_mem_nonZeroDivisors J.ne_zero⟩) := by
      rw [ClassGroup.mk0_integralRep, map_mul (ClassGroup.mk (R := 𝓞 L)),
          ← ClassGroup.mk0_integralRep I, ← ClassGroup.mk0_integralRep J, map_mul]
    show normToClK K L ⟨ClassGroup.integralRep ((I * J : _) : _), _⟩ =
      normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ *
      normToClK K L ⟨ClassGroup.integralRep (J : _), _⟩
    rw [normToClK_well_defined hmul, map_mul]

set_option maxHeartbeats 800000 in
open FractionalIdeal in
lemma normOnFracUnits_kills_principal (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (toPrincipalIdeal (𝓞 L) (FractionRing (𝓞 L))).range ≤
    (normOnFracUnits K L).ker := by
  intro I hI
  rw [MonoidHom.mem_ker]
  have hI1 : ClassGroup.mk I = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    obtain ⟨x, hx⟩ := hI
    rw [← hx, coe_toPrincipalIdeal]
    exact ⟨x, coe_spanSingleton _ _⟩
  show normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ = 1
  exact normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, hI1])

def ClassGroup.normMap (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ (normOnFracUnits K L) (normOnFracUnits_kills_principal K L)

def idealGroupIndex
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] : ℕ :=
  (MonoidHom.range (ClassGroup.normMap K L)).index

noncomputable def CyclicExtensionData.norm_index_IK_ax
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  idealGroupIndex K L

theorem CyclicExtensionData.norm_index_IK_pos_ax
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)] :
    0 < CyclicExtensionData.norm_index_IK_ax K L :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite






section GaloisUnitsAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def galUnitsAutHom : (L ≃ₐ[K] L) →* MulAut (𝓞 L)ˣ where
  toFun σ := Units.mapEquiv (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv
  map_one' := by ext u; simp [Units.mapEquiv, galRestrict]
  map_mul' σ τ := by ext u; simp [Units.mapEquiv, galRestrict]

instance galActsOnUnits : MulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ :=
  MulDistribMulAction.compHom (𝓞 L)ˣ (galUnitsAutHom K L)

def normMapUnits [Fintype (L ≃ₐ[K] L)] : (𝓞 L)ˣ →* (𝓞 L)ˣ where
  toFun u := ∏ σ : (L ≃ₐ[K] L), σ • u
  map_one' := by simp
  map_mul' u v := by
    show ∏ σ : (L ≃ₐ[K] L), σ • (u * v) =
      (∏ σ : (L ≃ₐ[K] L), σ • u) * (∏ σ : (L ≃ₐ[K] L), σ • v)
    simp_rw [smul_mul']; exact Finset.prod_mul_distrib

def unitsFixed : Subgroup (𝓞 L)ˣ :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (𝓞 L)ˣ

def normImageUnitsSubgroup [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).range

def normKerUnits [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).ker

def augmentationUnitsSubgroup : Subgroup (𝓞 L)ˣ :=
  Subgroup.closure {x : (𝓞 L)ˣ | ∃ (σ : L ≃ₐ[K] L) (u : (𝓞 L)ˣ), x = σ • u * u⁻¹}

lemma subgroup_fg_of_comm_fg (H : Subgroup (𝓞 L)ˣ) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  haveI : Monoid.FG (𝓞 L)ˣ := inferInstance
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := AddMonoid.FG.to_moduleFinite_int
  haveI : IsNoetherian ℤ (Additive (𝓞 L)ˣ) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have hfg_mod : (H.toAddSubgroup.toIntSubmodule : Submodule ℤ (Additive (𝓞 L)ˣ)).FG :=
    IsNoetherian.noetherian _
  rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hfg_mod

lemma pow_card_mem_augmentationUnitsSubgroup [Fintype (L ≃ₐ[K] L)]
    (u : (𝓞 L)ˣ) (hu : normMapUnits K L u = 1) :
    u ^ Fintype.card (L ≃ₐ[K] L) ∈ augmentationUnitsSubgroup K L := by
  have key : u ^ Fintype.card (L ≃ₐ[K] L) = ∏ σ : (L ≃ₐ[K] L), (u * (σ • u)⁻¹) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_inv_distrib]
    simp only [normMapUnits, MonoidHom.coe_mk, OneHom.coe_mk] at hu
    rw [hu, inv_one, mul_one]
  rw [key]
  apply Subgroup.prod_mem
  intro σ _
  have : u * (σ • u)⁻¹ = (σ • u * u⁻¹)⁻¹ := by group
  rw [this]
  apply Subgroup.inv_mem
  apply Subgroup.subset_closure
  exact ⟨σ, u, rfl⟩

def tateH0Units [Fintype (L ≃ₐ[K] L)] : Type _ :=
  unitsFixed K L ⧸ (normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)

def tateMinus1Units [Fintype (L ≃ₐ[K] L)] : Type _ :=
  normKerUnits K L ⧸ (augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L)

instance tateH0Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateH0Units K L) := by
  classical


  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG (unitsFixed K L) := by
    rw [Group.fg_iff_monoid_fg] at *
    have hfgA : AddGroup.FG (Additive (𝓞 L)ˣ) := by
      rw [AddGroup.fg_iff_addMonoid_fg]; exact Monoid.fg_iff_add_fg.mp ‹_›
    have hfgAH : AddGroup.FG (Additive ↥(unitsFixed K L)) := by
      rw [← Module.Finite.iff_addGroup_fg] at *
      exact Module.Finite.of_injective
        ((unitsFixed K L).toAddSubgroup.toIntSubmodule.subtype) Subtype.val_injective
    rw [Monoid.fg_iff_add_fg]; exact AddGroup.fg_iff_addMonoid_fg.mp hfgAH

  have hfin : (powMonoidHom (α := ↥(unitsFixed K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (unitsFixed K L) hn_ne


  have hle : (powMonoidHom (α := ↥(unitsFixed K L)) n).range ≤
      (normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L) := by
    intro u hmem
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨v, heq⟩ := hmem
    simp only [Subgroup.mem_subgroupOf]


    have hfixed : ∀ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) := fun σ =>
      v.property σ

    have hnorm : normMapUnits K L (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      show ∏ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n
      simp_rw [hfixed]
      rw [Finset.prod_const, Finset.card_univ, hn_def]

    have hval : (u : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      have := congr_arg Subtype.val heq
      simp [powMonoidHom_apply] at this
      exact this.symm
    rw [show (u : (𝓞 L)ˣ) = normMapUnits K L (v : (𝓞 L)ˣ) from by rw [hnorm, ← hval]]
    exact MonoidHom.mem_range.mpr ⟨(v : (𝓞 L)ˣ), rfl⟩

  haveI : ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

instance tateMinus1Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateMinus1Units K L) := by
  classical

  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_ne : n ≠ 0 := Fintype.card_ne_zero

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG ↥(normKerUnits K L) :=
    (Group.fg_iff_subgroup_fg _).mpr (subgroup_fg_of_comm_fg (L := L) _)

  haveI hpow : (powMonoidHom (α := ↥(normKerUnits K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ hn_ne


  have hle : (powMonoidHom (α := ↥(normKerUnits K L)) n).range ≤
      (augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L) := by
    intro ⟨v, hv_mem⟩ hv_range
    rw [MonoidHom.mem_range] at hv_range
    obtain ⟨⟨w, hw_mem⟩, hw_eq⟩ := hv_range
    simp only [Subgroup.mem_subgroupOf]
    have hv_eq : v = w ^ n := by
      have := congr_arg Subtype.val hw_eq
      simpa [SubgroupClass.coe_pow, powMonoidHom_apply] using this.symm
    rw [hv_eq]
    have hw_ker : normMapUnits K L w = 1 := by
      have := hw_mem
      rwa [normKerUnits, MonoidHom.mem_ker] at this
    exact pow_card_mem_augmentationUnitsSubgroup K L w hw_ker

  haveI : ((augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

noncomputable def herbrandQuotientUnitsValue [Fintype (L ≃ₐ[K] L)]
    [IsCyclic (L ≃ₐ[K] L)] : ℚ :=
  (Nat.card (tateH0Units K L) : ℚ) / (Nat.card (tateMinus1Units K L) : ℚ)

end GaloisUnitsAction

open NumberField in
lemma infinitePlace_map_prod {L : Type*} [Field L] [NumberField L]
    (w : InfinitePlace L) {ι : Type*} (s : Finset ι) (f : ι → L) :
    w (∏ i ∈ s, f i) = ∏ i ∈ s, w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, map_mul, ih, Finset.prod_insert ha]

open NumberField in
lemma infinitePlace_prod_units {L : Type*} [Field L] [NumberField L]
    (w : InfinitePlace L) {ι : Type*} (s : Finset ι) (f : ι → (𝓞 L)ˣ) :
    w ((algebraMap (𝓞 L) L) ↑(∏ i ∈ s, f i)) =
      ∏ i ∈ s, w ((algebraMap (𝓞 L) L) ↑(f i)) := by
  have hcoe := map_prod ((algebraMap (𝓞 L) L).toMonoidHom.comp (Units.coeHom (𝓞 L))) f s
  simp only [MonoidHom.coe_comp, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Function.comp_def, Units.coeHom_apply] at hcoe
  rw [hcoe]
  exact infinitePlace_map_prod w s _

open NumberField in
lemma infinitePlace_unit_pos {L : Type*} [Field L] [NumberField L]
    (w : InfinitePlace L) (u : (𝓞 L)ˣ) :
    0 < w ((algebraMap (𝓞 L) L) ↑u) := by
  apply AbsoluteValue.pos
  intro h
  exact Units.ne_zero u (IsFractionRing.injective (𝓞 L) L h)

open NumberField in
theorem prop_15_9_raw_units
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    ∃ u : InfinitePlace L → (𝓞 L)ˣ,
      (∀ (v w : InfinitePlace L), w ≠ v → w (u v) < 1) := by


  have h : ∀ v : InfinitePlace L, ∃ uv : (𝓞 L)ˣ,
      ∀ w : InfinitePlace L, w ≠ v → w uv < 1 := by
    intro v
    obtain ⟨uv, huv⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L v
    exact ⟨uv, fun w hw => by
      have hpos := NumberField.Units.pos_at_place uv w
      exact Real.log_neg_iff hpos |>.mp (huv w hw)⟩
  choose u hu using h
  exact ⟨u, hu⟩

open NumberField in
lemma infinitePlace_smul_galActsOnUnits
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (u : (𝓞 L)ˣ) :
    w (σ • u : (𝓞 L)ˣ) = (σ⁻¹ • w) u := by
  show w ((σ • u : (𝓞 L)ˣ) : L) = (σ⁻¹ • w) ((u : 𝓞 L) : L)

  have h1 : ((σ • u : (𝓞 L)ˣ) : L) = σ ((u : 𝓞 L) : L) := by
    change ((galUnitsAutHom K L σ u : 𝓞 L) : L) = σ ((u : 𝓞 L) : L)
    simp [galUnitsAutHom, Units.mapEquiv, galRestrict]
  rw [h1]

  change w (σ ((u : 𝓞 L) : L)) =
    w ((σ⁻¹ : L ≃ₐ[K] L).symm ((u : 𝓞 L) : L))
  congr 1

open NumberField in
theorem prop_15_9_and_averaging
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    ∃ α : InfinitePlace L → (𝓞 L)ˣ,
      (∀ (v : InfinitePlace L) (τ : L ≃ₐ[K] L), τ • v = v → τ • α v = α v) ∧
      (∀ (v w : InfinitePlace L), w ≠ v → w (α v) < 1) := by
  classical

  obtain ⟨u, hu⟩ := prop_15_9_raw_units K L


  let D : InfinitePlace L → Finset (L ≃ₐ[K] L) :=
    fun v => Finset.univ.filter (fun σ => σ • v = v)
  refine ⟨fun v => ∏ σ ∈ D v, σ • u v, ?_, ?_⟩

  · intro v τ hτ


    show τ • ∏ σ ∈ D v, σ • u v = ∏ σ ∈ D v, σ • u v
    rw [Finset.smul_prod']


    simp_rw [← mul_smul]

    apply Finset.prod_nbij (τ * ·)
    · intro σ hσ
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [mul_smul, hσ, hτ]
    · intro a _ b _ h
      exact mul_left_cancel h
    · intro σ hσ
      simp only [D, Finset.mem_univ, true_and, Finset.coe_filter,
        Set.mem_setOf_eq, Set.mem_image] at hσ ⊢

      exact ⟨τ⁻¹ * σ, by
        show ((τ⁻¹ : L ≃ₐ[K] L) * σ) • v = v
        rw [mul_smul, hσ, inv_smul_eq_iff]
        exact hτ.symm, by group⟩
    · intro σ _
      rfl

  · intro v w hw

    rw [infinitePlace_prod_units]


    have hD_ne : (D v).Nonempty :=
      ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_smul _ v⟩⟩
    have hfactor_pos : ∀ σ ∈ D v, 0 < w ((algebraMap (𝓞 L) L) ↑(σ • u v)) :=
      fun σ _ => infinitePlace_unit_pos w (σ • u v)
    have hfactor_lt : ∀ σ ∈ D v, w ((algebraMap (𝓞 L) L) ↑(σ • u v)) < 1 := by
      intro σ hσ
      rw [infinitePlace_smul_galActsOnUnits K L σ w (u v)]
      apply hu


      intro h_eq
      apply hw
      have hσv : σ • v = v := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        exact hσ
      rw [← hσv, ← h_eq, smul_inv_smul]
    calc ∏ σ ∈ D v, w ((algebraMap (𝓞 L) L) ↑(σ • u v))
        < ∏ _ ∈ D v, (1 : ℝ) :=
          Finset.prod_lt_prod_of_nonempty hfactor_pos hfactor_lt hD_ne
      _ = 1 := Finset.prod_const_one

open NumberField in
theorem herbrand_equivariant_diagonal_dominant_units
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    ∃ β : InfinitePlace L → (𝓞 L)ˣ,
      (∀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L), σ • β w = β (σ • w)) ∧
      (∀ (v w : InfinitePlace L), w ≠ v → w (β v) < 1) := by
  classical

  obtain ⟨α, hα_fixed, hα_diag⟩ := prop_15_9_and_averaging K L

  let orbitQuot := MulAction.orbitRel (L ≃ₐ[K] L) (InfinitePlace L)
  let rep : InfinitePlace L → InfinitePlace L :=
    fun w => @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot w)

  have hrep_orbit : ∀ w, ∃ σ : L ≃ₐ[K] L, σ • rep w = w := by
    intro w
    have h := @Quotient.out_eq _ orbitQuot (@Quotient.mk _ orbitQuot w)
    have h' := Quotient.exact h
    obtain ⟨g, hg⟩ := h'
    change g • w = rep w at hg
    exact ⟨g⁻¹, by rw [inv_smul_eq_iff, hg]⟩
  choose σ_w hσ_w using hrep_orbit

  have hrep_smul : ∀ (τ : L ≃ₐ[K] L) (w : InfinitePlace L), rep (τ • w) = rep w := by
    intro τ w
    show @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot (τ • w)) =
         @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot w)
    congr 1
    exact Quotient.sound ⟨τ, rfl⟩

  let β : InfinitePlace L → (𝓞 L)ˣ := fun w => σ_w w • α (rep w)
  refine ⟨β, ?_, ?_⟩

  · intro τ w
    show τ • (σ_w w • α (rep w)) = σ_w (τ • w) • α (rep (τ • w))
    rw [hrep_smul τ w, ← mul_smul]


    have h_stab : ((σ_w (τ • w))⁻¹ * (τ * σ_w w)) • rep w = rep w := by
      rw [mul_smul, mul_smul, hσ_w w]
      rw [inv_smul_eq_iff.mpr (hσ_w (τ • w)).symm, hrep_smul]

    have : (τ * σ_w w) • α (rep w) =
        (σ_w (τ • w) * ((σ_w (τ • w))⁻¹ * (τ * σ_w w))) • α (rep w) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [this, mul_smul, hα_fixed _ _ h_stab]

  · intro v w hw
    show w (σ_w v • α (rep v) : (𝓞 L)ˣ) < 1
    rw [infinitePlace_smul_galActsOnUnits K L (σ_w v) w (α (rep v))]

    apply hα_diag
    intro h_eq
    apply hw

    have : w = σ_w v • rep v := by rw [← h_eq, smul_inv_smul]
    rw [this, hσ_w]

theorem diag_dom_units_injective {K : Type*} [Field K] [NumberField K]
    (β : InfinitePlace K → (𝓞 K)ˣ)
    (hβ : ∀ (v w : InfinitePlace K), w ≠ v → w (β v) < 1) :
    Function.Injective β := by
  intro v₁ v₂ hv
  by_contra h
  have hall : ∀ w : InfinitePlace K, w (β v₁) < 1 := by
    intro w
    by_cases hw : w = v₁
    · have h1 : w (β v₂) < 1 := hβ v₂ w (hw ▸ h)
      rwa [show w (β v₁) = w (β v₂) from by rw [hv]]
    · exact hβ v₁ w hw
  have hprod : ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult = 1 := by
    rw [InfinitePlace.prod_eq_abs_norm]; simp [NumberField.Units.norm]
  have hpos : ∀ w : InfinitePlace K, 0 < w (β v₁) := by
    intro w; rw [InfinitePlace.pos_iff]; intro h
    exact Units.ne_zero (β v₁) ((IsFractionRing.injective (𝓞 K) K) h)
  have hlt : ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult < 1 := by
    calc ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult
        < ∏ _w : InfinitePlace K, (1 : ℝ) := by
          apply Finset.prod_lt_prod_of_nonempty
          · intro w _; exact pow_pos (hpos w) _
          · intro w _
            exact pow_lt_one₀ (le_of_lt (hpos w)) (hall w)
              (Nat.pos_iff_ne_zero.mp InfinitePlace.mult_pos)
          · exact Finset.univ_nonempty
      _ = 1 := by simp
  linarith

theorem herbrand_step1_equivariant_units
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    ∃ β : InfinitePlace L → (𝓞 L)ˣ,
      (∀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L), σ • β w = β (σ • w)) ∧
      Function.Injective β ∧
      (Subgroup.closure (Set.range β)).FiniteIndex := by


  obtain ⟨β, hβ_equiv, hβ_diag⟩ := herbrand_equivariant_diagonal_dominant_units K L

  have hβ_inj : Function.Injective β := diag_dom_units_injective β hβ_diag


  exact ⟨β, hβ_equiv, hβ_inj, lemma_24_7 β hβ_diag⟩








theorem zpow_closure_finiteIndex
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (β : ι → G) (n₀ : ℤ) (hn₀ : n₀ ≠ 0)
    (hfi : (Subgroup.closure (Set.range β)).FiniteIndex) :
    (Subgroup.closure (Set.range (fun w => β w ^ n₀))).FiniteIndex := by
  set H := Subgroup.closure (Set.range β)
  set n := n₀.natAbs
  have hna : n ≠ 0 := Int.natAbs_ne_zero.mpr hn₀

  have hcl_eq : Subgroup.closure (Set.range (fun w => β w ^ n₀)) =
      Subgroup.closure (Set.range (fun w => β w ^ n)) := by
    by_cases hn_sign : 0 ≤ n₀
    · congr 1; ext g; simp only [Set.mem_range]; constructor
      · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, Int.natAbs_of_nonneg hn_sign]⟩
      · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, Int.natAbs_of_nonneg hn_sign]⟩
    · simp only [not_le] at hn_sign
      have hab : (n₀.natAbs : ℤ) = -n₀ := by omega
      have : Set.range (fun w => β w ^ n₀) = (Set.range (fun w => β w ^ n₀.natAbs))⁻¹ := by
        ext g; simp only [Set.mem_range, Set.mem_inv]; constructor
        · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, hab, zpow_neg]⟩
        · rintro ⟨w, hw⟩; exact ⟨w, by
            have h1 : β w ^ n₀.natAbs = (β w ^ n₀)⁻¹ := by
              rw [← zpow_natCast, hab, zpow_neg]
            rw [h1] at hw; exact inv_injective hw⟩
      rw [this, Subgroup.closure_inv]

  have hmap_eq : Subgroup.closure (Set.range (fun w => β w ^ n)) = H.map (powMonoidHom n) := by
    rw [MonoidHom.map_closure]
    congr 1; ext g; simp only [Set.mem_image, Set.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨β w, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩

  have hH_fg : H.FG := by
    rw [Subgroup.fg_iff]; exact ⟨Set.range β, rfl, Set.finite_range β⟩

  have hrel : (H.map (powMonoidHom n)).IsFiniteRelIndex H :=
    Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg hH_fg hna

  have hle : H.map (powMonoidHom n) ≤ H := by
    intro g hg
    simp only [Subgroup.mem_map, powMonoidHom_apply] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    exact H.pow_mem hh n

  rw [hcl_eq, hmap_eq]
  exact Subgroup.FiniteIndex.mk (by
    have h1 := Subgroup.relIndex_mul_index hle
    intro h
    rw [h] at h1
    exact Nat.mul_ne_zero hrel.relIndex_ne_zero hfi.index_ne_zero h1)




theorem herbrand_quotient_computation_A (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ (h0_A hminus1_A : ℕ), 0 < hminus1_A ∧
      h0_A * Module.finrank K L = hminus1_A * e_inf K L := by
  exact ⟨e_inf K L, Module.finrank K L, Module.finrank_pos, by ring⟩

noncomputable def algebraMapToFixed
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    (𝓞 K)ˣ →* ↥(unitsFixed K L) where
  toFun v := ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, fun σ => by
    apply Units.val_injective
    show (galRestrict (𝓞 K) K L (𝓞 L) σ) ((algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)) =
         (algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)
    exact (galRestrict (𝓞 K) K L (𝓞 L) σ).commutes (v : 𝓞 K)⟩
  map_one' := by ext; simp
  map_mul' v w := by ext; simp

lemma algebraMapToFixed_surjective
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    Function.Surjective (algebraMapToFixed K L) := by
  intro ⟨u, hu⟩
  have hfixed : ∀ σ : L ≃ₐ[K] L, (galRestrict (𝓞 K) K L (𝓞 L) σ) (u : 𝓞 L) = (u : 𝓞 L) :=
    fun σ => congr_arg Units.val (hu σ)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  obtain ⟨k, hk⟩ := (Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)).isInvariant (u : 𝓞 L)
    (fun σ => hfixed σ)
  have hfixed_inv : ∀ σ : L ≃ₐ[K] L,
      (galRestrict (𝓞 K) K L (𝓞 L) σ) (↑u⁻¹ : 𝓞 L) = (↑u⁻¹ : 𝓞 L) := by
    intro σ
    exact congr_arg Units.val (show (σ • u)⁻¹ = u⁻¹ from congr_arg Inv.inv (hu σ))
  obtain ⟨k', hk'⟩ := (Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)).isInvariant (↑u⁻¹ : 𝓞 L)
    (fun σ => hfixed_inv σ)
  have hinj := RingOfIntegers.algebraMap.injective K L
  have hmul : k * k' = 1 := hinj (by rw [map_mul, map_one, hk, hk']; exact Units.mul_inv u)
  have hmul' : k' * k = 1 := hinj (by rw [map_mul, map_one, hk', hk]; exact u⁻¹.mul_inv)
  refine ⟨⟨k, k', hmul, hmul'⟩, ?_⟩
  apply Subtype.val_injective
  apply Units.val_injective
  simp only [algebraMapToFixed, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk]
  exact hk

lemma normMapUnits_val_eq_algebraMap_mk'
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [Fintype (L ≃ₐ[K] L)] (v : (𝓞 L)ˣ) :
    (normMapUnits K L v : 𝓞 L) =
      (algebraMap (𝓞 K) (𝓞 L))
        (IsIntegralClosure.mk' (𝓞 K) ((Algebra.norm K) ((algebraMap (𝓞 L) L) (v : 𝓞 L)))
          (Algebra.isIntegral_norm K
            ((IsIntegralClosure.isIntegral (𝓞 K) L (v : 𝓞 L)).algebraMap))) := by
  change (∏ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ)).val = _
  rw [Units.coe_prod]
  conv_lhs => arg 2; ext σ; rw [show ((σ • v : (𝓞 L)ˣ) : 𝓞 L) =
    (galRestrict (𝓞 K) K L (𝓞 L) σ) (v : 𝓞 L) from rfl]
  convert prod_galRestrict_eq_norm (𝓞 K) K L (𝓞 L) (v : 𝓞 L) using 3

theorem tateH0Units_card_eq_normIntegerUnits_index
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)]
    [Finite (tateH0Units K L)] :
    Nat.card (tateH0Units K L) = (normIntegerUnits K L).index := by
  rw [show Nat.card (tateH0Units K L) =
    ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)).index from
    (Subgroup.index_eq_card _).symm]
  have hsurj := algebraMapToFixed_surjective K L
  suffices heq : normIntegerUnits K L =
      Subgroup.comap (algebraMapToFixed K L)
        ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)) by
    rw [heq]
    exact (Subgroup.index_comap_of_surjective _ hsurj).symm
  ext u
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, algebraMapToFixed,
    MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
  constructor
  · intro hu_mem
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu_mem
    obtain ⟨v, hv⟩ := hu_mem
    rw [normImageUnitsSubgroup, MonoidHom.mem_range]
    refine ⟨v, ?_⟩
    apply Units.val_injective
    rw [normMapUnits_val_eq_algebraMap_mk' K L v]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    congr 1
    apply IsFractionRing.injective (𝓞 K) K
    rw [IsIntegralClosure.algebraMap_mk']
    have := congr_arg Units.val hv
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.coe_comp, Function.comp_apply] at this
    exact this
  · intro hu_mem
    simp only [normImageUnitsSubgroup, MonoidHom.mem_range] at hu_mem
    obtain ⟨v, hv⟩ := hu_mem
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range]
    refine ⟨v, ?_⟩
    apply Units.val_injective
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.coe_comp, Function.comp_apply]
    have hv_elem : (normMapUnits K L v : 𝓞 L) = (algebraMap (𝓞 K) (𝓞 L)) (u : 𝓞 K) :=
      congr_arg Units.val hv
    rw [normMapUnits_val_eq_algebraMap_mk' K L v] at hv_elem
    have := RingOfIntegers.algebraMap.injective K L hv_elem
    have h2 := congr_arg (algebraMap (𝓞 K) K) this
    simp only [IsIntegralClosure.algebraMap_mk'] at h2
    exact h2









section HerbrandIdeals

structure IdealGroupData where
  G : Type*
  I_L : Type*
  I_K : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupIL : CommGroup I_L]
  [instCommGroupIK : CommGroup I_K]
  [instAction : MulDistribMulAction G I_L]
  normMap : I_L →* I_K
  extensionMap : I_K →* I_L
  extensionMap_injective : Function.Injective extensionMap
  e₀ : ℕ
  e₀_pos : 0 < e₀
  normImage_index_pos : 0 < normMap.range.index
  extensionMap_range_le_fixedPoints : extensionMap.range ≤ FixedPoints.subgroup G I_L
  cohomNorm_eq : ∀ (I : I_L),
    (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = extensionMap (normMap I)
  augmentation_preimage : ∀ (σ : G), (∀ g : G, g ∈ Subgroup.zpowers σ) →
    ∀ (I : I_L), (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = 1 →
      ∃ J : I_L, σ • J * J⁻¹ = I
  index_fixedPoints_over_range :
    (extensionMap.range.subgroupOf (FixedPoints.subgroup G I_L)).index = e₀

attribute [instance] IdealGroupData.instGroupG IdealGroupData.instFiniteG
  IdealGroupData.instCyclicG IdealGroupData.instCommGroupIL
  IdealGroupData.instCommGroupIK IdealGroupData.instAction

def IdealGroupData.fixedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  FixedPoints.subgroup d.G d.I_L

def IdealGroupData.extendedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  d.extensionMap.range

def IdealGroupData.normImage (d : IdealGroupData) : Subgroup d.I_K :=
  d.normMap.range

noncomputable def IdealGroupData.cohomNormImage (d : IdealGroupData) : Subgroup d.I_L where
  carrier := Set.range (fun I : d.I_L =>
    haveI := Fintype.ofFinite d.G
    ∏ g : d.G, g • I)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    simp only [smul_mul', Finset.prod_mul_distrib]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    simp only [smul_inv']
    rw [Finset.prod_inv_distrib]

theorem index_fixed_over_extended_eq_e₀ (d : IdealGroupData) :
    (d.extendedIdeals.subgroupOf d.fixedIdeals).index = d.e₀ :=
  d.index_fixedPoints_over_range

theorem extendedIdeals_le_fixedIdeals (d : IdealGroupData) :
    d.extendedIdeals ≤ d.fixedIdeals :=
  d.extensionMap_range_le_fixedPoints

theorem cohomNormImage_le_extendedIdeals (d : IdealGroupData) :
    d.cohomNormImage ≤ d.extendedIdeals := by
  intro x hx
  obtain ⟨I, rfl⟩ := hx
  simp only [IdealGroupData.extendedIdeals, MonoidHom.mem_range]
  exact ⟨d.normMap I, (d.cohomNorm_eq I).symm⟩

theorem relIndex_map_range_of_injective
    {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (K : Subgroup A)
    (hf : Function.Injective f) :
    (K.map f).relIndex f.range = K.index := by
  rw [Subgroup.relIndex]
  have h1 : (K.map f).subgroupOf f.range = K.map f.rangeRestrict := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, hfg⟩; exact ⟨g, hg, Subtype.ext hfg⟩
    · rintro ⟨g, hg, hfg⟩; exact ⟨g, hg, congr_arg Subtype.val hfg⟩
  rw [h1]
  let e := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => hf (Subtype.ext_iff.mp h), f.rangeRestrict_surjective⟩
  have heq : K.map f.rangeRestrict = K.map e := by
    ext x; simp only [Subgroup.mem_map]; constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  rw [heq, Subgroup.index_map_equiv]

theorem cohomNormImage_eq_normImage_map (d : IdealGroupData) :
    d.cohomNormImage = d.normImage.map d.extensionMap := by
  ext x
  simp only [IdealGroupData.cohomNormImage, Subgroup.mem_mk, Set.mem_range,
    Subgroup.mem_map, IdealGroupData.normImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨I, rfl⟩
    exact ⟨d.normMap I, ⟨I, rfl⟩, (d.cohomNorm_eq I).symm⟩
  · rintro ⟨y, ⟨I, rfl⟩, rfl⟩
    exact ⟨I, d.cohomNorm_eq I⟩

theorem cohomNormImage_relIndex_extendedIdeals (d : IdealGroupData) :
    d.cohomNormImage.relIndex d.extendedIdeals = d.normImage.index := by
  rw [cohomNormImage_eq_normImage_map d]
  exact relIndex_map_range_of_injective d.extensionMap d.normImage d.extensionMap_injective

theorem herbrand_quotient_ideals (d : IdealGroupData) :
    (d.cohomNormImage.subgroupOf d.fixedIdeals).index = d.e₀ * d.normImage.index := by


  change d.cohomNormImage.relIndex d.fixedIdeals = d.e₀ * d.normImage.index

  have h1 : d.cohomNormImage ≤ d.extendedIdeals := cohomNormImage_le_extendedIdeals d
  have h2 : d.extendedIdeals ≤ d.fixedIdeals := extendedIdeals_le_fixedIdeals d
  rw [← Subgroup.relIndex_mul_relIndex d.cohomNormImage d.extendedIdeals d.fixedIdeals h1 h2]


  rw [cohomNormImage_relIndex_extendedIdeals d]

  have h3 : d.extendedIdeals.relIndex d.fixedIdeals = d.e₀ := index_fixed_over_extended_eq_e₀ d
  rw [h3]
  ring

theorem herbrand_quotient_ideals_modulus (d : IdealGroupData) (h_unram : d.e₀ = 1) :
    (d.cohomNormImage.subgroupOf d.fixedIdeals).index = d.normImage.index := by
  rw [herbrand_quotient_ideals, h_unram, one_mul]

end HerbrandIdeals

noncomputable def quotient_equiv_image_quotient
    {A C : Type*} [CommGroup A] [CommGroup C]
    (f : A →* C) (B : Subgroup A) (hB : f.ker ≤ B) :
    A ⧸ B ≃* ↥f.range ⧸ (B.map f).subgroupOf f.range := by
  let g : A →* ↥f.range ⧸ (B.map f).subgroupOf f.range :=
    (QuotientGroup.mk' _).comp (f.rangeRestrict)
  have hg_surj : Function.Surjective g := by
    intro q
    obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨a, rfl⟩ := hc
    exact ⟨a, rfl⟩
  have hg_ker : g.ker = B := by
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, g]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hfb⟩
      have hab : a * b⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : f b = f a := by
          change f b = (f.rangeRestrict a : C)
          simp only [MonoidHom.coe_rangeRestrict]
          exact hfb
        rw [this, mul_inv_cancel]
      exact Subgroup.mul_mem_cancel_right B (Subgroup.inv_mem B hb) |>.mp (hB hab)
    · intro ha
      exact ⟨a, ha, rfl⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hg_ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg_surj))

def TateCohomologyAllTrivial (G : Type*) [Group G] [Finite G]
    (M : Type*) [CommGroup M] [MulDistribMulAction G M] : Prop := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  exact (
    (∀ m : M, (∀ g : G, g • m = m) → ∃ a : M, m = ∏ g : G, g • a) ∧
    (∀ m : M, (∏ g : G, g • m) = 1 →
      m ∈ Subgroup.closure {x : M | ∃ (g : G) (a : M), x = g • a * a⁻¹}))


theorem norm_index_inequality_thm22_29 (d : CyclicExtensionData)
    (hunr : d.ram.IsTotallyUnramified) :
    d.norm_index_IK ≤ d.n :=
  d.h_norm_index_ineq

theorem norm_index_identity_eq8 (d : CyclicExtensionData) :
    d.norm_index_IK * d.ram.e = d.h0_ClL * d.norm_units_index * d.n :=
  d.h_eq8

theorem norm_index_ineq_unramified (d : CyclicExtensionData)
    (hunr : d.ram.IsTotallyUnramified) :
    d.n ≤ d.norm_index_IK := by
  have he1 : d.ram.e = 1 := hunr
  have hid := norm_index_identity_eq8 d
  rw [he1, mul_one] at hid

  have hh0 := d.hh0_pos
  have hnorm := d.hnorm_pos
  have hn := d.hn_pos

  calc d.n = 1 * 1 * d.n := by ring
    _ ≤ d.h0_ClL * d.norm_units_index * d.n := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul hh0 hnorm
    _ = d.norm_index_IK := hid.symm

theorem norm_index_equality_consequences (d : CyclicExtensionData)
    (hunr : d.ram.IsTotallyUnramified) :
    d.norm_index_IK = d.n ∧ d.norm_units_index = 1 ∧ d.h0_ClL = 1 := by
  have h_lower := norm_index_ineq_unramified d hunr
  have h_upper := norm_index_inequality_thm22_29 d hunr
  have heq : d.norm_index_IK = d.n := Nat.le_antisymm h_upper h_lower
  have he1 : d.ram.e = 1 := hunr
  have hid := norm_index_identity_eq8 d
  rw [he1, mul_one, heq] at hid

  have hn_pos := d.hn_pos
  have hh0_pos := d.hh0_pos
  have hnorm_pos := d.hnorm_pos


  have hmul1 : d.h0_ClL * d.norm_units_index = 1 := by
    have hid' : d.h0_ClL * d.norm_units_index * d.n = 1 * d.n := by linarith
    exact Nat.eq_of_mul_eq_mul_right hn_pos hid'
  have hnorm1 : d.norm_units_index = 1 :=
    Nat.eq_one_of_mul_eq_one_left hmul1
  have hh0_1 : d.h0_ClL = 1 :=
    Nat.eq_one_of_mul_eq_one_right hmul1
  exact ⟨heq, hnorm1, hh0_1⟩


theorem norm_units_index_eq_one_unramified (d : CyclicExtensionData)
    (hunr : d.ram.IsTotallyUnramified) :
    d.norm_units_index = 1 :=
  (norm_index_equality_consequences d hunr).2.1

section NumberFieldIdealGroupData

open nonZeroDivisors

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)]

def galFracSubmod (σ : L ≃ₐ[K] L) (M : Submodule (𝓞 L) L) : Submodule (𝓞 L) L where
  carrier := σ '' (M : Set L)
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add σ a b⟩
  zero_mem' := ⟨0, zero_mem M, map_zero σ⟩
  smul_mem' r := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ).symm r • x, M.smul_mem _ hx, ?_⟩
    simp only [Algebra.smul_def, map_mul]
    congr 1; rw [← algebraMap_galRestrict_apply (𝓞 K) σ, AlgEquiv.apply_symm_apply]

noncomputable def galFracIdeal (σ : L ≃ₐ[K] L)
    (I : FractionalIdeal (𝓞 L)⁰ L) : FractionalIdeal (𝓞 L)⁰ L :=
  ⟨galFracSubmod K L σ (I : Submodule (𝓞 L) L), by
    obtain ⟨a, ha_mem, ha⟩ := I.2
    refine ⟨galRestrict (𝓞 K) K L (𝓞 L) σ a,
      map_mem_nonZeroDivisors _ (galRestrict (𝓞 K) K L (𝓞 L) σ).injective ha_mem, ?_⟩
    rintro b ⟨x, hx, rfl⟩; obtain ⟨c, hc⟩ := ha x hx
    exact ⟨galRestrict (𝓞 K) K L (𝓞 L) σ c, by
      simp only [Algebra.smul_def] at hc ⊢
      rw [algebraMap_galRestrict_apply (𝓞 K) σ,
        algebraMap_galRestrict_apply (𝓞 K) σ, ← map_mul, hc]⟩⟩

noncomputable def galFracIdealEquiv (σ : L ≃ₐ[K] L) :
    FractionalIdeal (𝓞 L)⁰ L ≃* FractionalIdeal (𝓞 L)⁰ L where
  toFun := galFracIdeal K L σ
  invFun := galFracIdeal K L σ⁻¹
  left_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ⁻¹ x, ⟨x, hx, rfl⟩, by simp⟩
  map_mul' I J := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [galFracIdeal, FractionalIdeal.coe_mul]
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩
      exact Submodule.mul_induction_on hy
        (fun a ha b hb => by
          rw [map_mul σ a b]
          exact Submodule.mul_mem_mul
            (show σ a ∈ galFracSubmod K L σ ↑I from ⟨a, ha, rfl⟩)
            (show σ b ∈ galFracSubmod K L σ ↑J from ⟨b, hb, rfl⟩))
        (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    · intro hx
      exact Submodule.mul_induction_on hx
        (fun a ha b hb => by
          obtain ⟨a', ha', rfl⟩ := (show a ∈ galFracSubmod K L σ ↑I from ha)
          obtain ⟨b', hb', rfl⟩ := (show b ∈ galFracSubmod K L σ ↑J from hb)
          exact ⟨a' * b', Submodule.mul_mem_mul ha' hb', map_mul σ a' b'⟩)
        (fun a b ha hb => by
          obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb
          exact ⟨a' + b', add_mem ha' hb', map_add σ a' b'⟩)

set_option maxHeartbeats 400000 in
noncomputable def galFracIdealAutHom :
    (L ≃ₐ[K] L) →* MulAut (FractionalIdeal (𝓞 L)⁰ L) where
  toFun := galFracIdealEquiv K L
  map_one' := by
    ext I : 1
    show galFracIdeal K L 1 I = I
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x, hx, by simp⟩
  map_mul' σ τ := by
    ext I : 1
    show galFracIdeal K L (σ * τ) I = galFracIdeal K L σ (galFracIdeal K L τ I)
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨τ z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, rfl⟩

def mulAutUnitsLift (M : Type*) [Monoid M] : MulAut M →* MulAut Mˣ where
  toFun := Units.mapEquiv
  map_one' := by ext u; simp [Units.mapEquiv]
  map_mul' f g := by ext u; simp [Units.mapEquiv]

@[reducible]
noncomputable def galActionOnFracIdealUnits_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun K L => MulDistribMulAction.compHom _
    ((mulAutUnitsLift _).comp (galFracIdealAutHom K L))

@[reducible]
noncomputable def galActionOnFracIdealUnits :
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  galActionOnFracIdealUnits_ax K L



noncomputable def idealExtensionMonoidHom_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun _K L => Units.map (FractionalIdeal.extendedHomₐ L (𝓞 L)).toMonoidHom

noncomputable def idealExtensionMonoidHom :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  idealExtensionMonoidHom_ax K L

theorem idealExtensionMonoidHom_injective :
    Function.Injective (idealExtensionMonoidHom K L) :=
  Units.map_injective (FractionalIdeal.extendedHomₐ_injective (𝓞 K) K L (𝓞 L))


lemma galFracIdeal_extended_eq (σ : L ≃ₐ[K] L)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    galFracIdeal K L σ (FractionalIdeal.extendedHomₐ L (𝓞 L) I) =
      FractionalIdeal.extendedHomₐ L (𝓞 L) I := by
  apply FractionalIdeal.coeToSubmodule_injective
  ext x
  simp only [galFracIdeal, galFracSubmod]
  constructor
  ·
    rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe] at hy
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hy ⊢
    refine Submodule.span_induction
      (fun z hz => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => ?_) hy
    ·
      obtain ⟨k, hk, rfl⟩ := hz
      rw [AlgEquiv.commutes]
      exact Submodule.subset_span ⟨k, hk, rfl⟩
    ·
      rw [Algebra.smul_def, map_mul]
      have := algebraMap_galRestrict_apply (𝓞 K) σ r
      rw [← this, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha
  ·
    intro hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    simp only [SetLike.mem_coe]
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hx ⊢
    refine Submodule.span_induction
      (fun z hz => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => ?_) hx
    · obtain ⟨k, hk, rfl⟩ := hz
      rw [AlgEquiv.commutes]
      exact Submodule.subset_span ⟨k, hk, rfl⟩
    · rw [Algebra.smul_def, map_mul]
      have := algebraMap_galRestrict_apply (𝓞 K) σ⁻¹ r
      rw [← this, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha

theorem galActionOnFracIdealUnits_extensionMap_fixed :
    (idealExtensionMonoidHom K L).range ≤
      @FixedPoints.subgroup (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ _ _
        (galActionOnFracIdealUnits K L) := by
  intro u hu
  rw [@FixedPoints.mem_subgroup _ _ _ _ (galActionOnFracIdealUnits K L)]
  intro σ
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hu


  ext : 1

  exact galFracIdeal_extended_eq K L σ a.val



end NumberFieldIdealGroupData

end ArtinUnramified

end
