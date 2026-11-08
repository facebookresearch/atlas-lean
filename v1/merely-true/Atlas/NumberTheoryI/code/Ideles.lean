/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

import Atlas.NumberTheoryI.code.Adeles

noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

abbrev IdeleGroup := (NumberField.AdeleRing (𝓞 K) K)ˣ

def principalIdeleEmb : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom

def principalIdeles : Subgroup (IdeleGroup K) :=
  (principalIdeleEmb K).range

abbrev IdeleClassGroup := (IdeleGroup K) ⧸ (principalIdeles K)

instance ideleGroup_locallyCompact :
    LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

theorem principalIdeles_discrete :
    DiscreteTopology (principalIdeles K) := by
  haveI : DiscreteTopology (NumberField.Adeles.principalSubgroup (K := K)) :=
    NumberField.Adeles.principalAdeles_discrete
  apply DiscreteTopology.of_continuous_injective
    (f := fun u => (⟨u.val.val, by
      obtain ⟨u, ⟨x, rfl⟩⟩ := u
      simp only [principalIdeleEmb, Units.map]
      exact ⟨x.val, rfl⟩⟩ : NumberField.Adeles.principalSubgroup (K := K)))
  · exact Continuous.subtype_mk (Units.continuous_val.comp continuous_subtype_val) _
  · intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Units.val_injective h)

end IdeleGroup

section OneIdeles

variable (K : Type*) [Field K] [NumberField K]

lemma adeleRing_unit_fin_norm_finMulSupport (a : IdeleGroup K) :
    (Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖)).Finite := by
  have ha := (a : NumberField.AdeleRing (𝓞 K) K).2.2
  have hai := (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2.2
  rw [Filter.eventually_cofinite] at ha hai
  apply Set.Finite.subset (ha.union hai)
  intro v hv
  rw [Function.mem_mulSupport] at hv
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra h
  push Not at h
  obtain ⟨hv1, hv2⟩ := h
  have h1 : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv1
  have h2 : ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv2
  have hmul : (↑a : NumberField.AdeleRing (𝓞 K) K).2 v *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v = 1 := by
    change ((↑a : NumberField.AdeleRing (𝓞 K) K).2 *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2) v =
      (1 : NumberField.AdeleRing (𝓞 K) K).2 v
    congr 1; exact congr_arg Prod.snd (Units.mul_inv a)
  have hnm : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
      ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hge : 1 ≤ ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
    by_contra hlt; push Not at hlt
    linarith [mul_le_mul_of_nonneg_left h2
      (norm_nonneg ((a : NumberField.AdeleRing (𝓞 K) K).2 v))]
  exact hv (le_antisymm h1 hge)

def adelicNorm : IdeleGroup K →* ℝ where
  toFun a := NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K)
  map_one' := by
    show NumberField.Adeles.adelicAbsVal
      ((1 : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K) = 1
    rw [Units.val_one]
    unfold NumberField.Adeles.adelicAbsVal
    have h1 : ∀ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ = 1 := by
      intro w
      show ‖(1 : InfiniteAdeleRing K) w‖ = 1
      have : (1 : InfiniteAdeleRing K) w = 1 := Pi.one_apply w
      rw [this]; exact IsAbsoluteValue.abv_one' norm
    have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
      intro v
      show ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
      have : (1 : FiniteAdeleRing (𝓞 K) K) v = 1 := RestrictedProduct.one_apply _ v
      rw [this, norm_one]
    have hinf : (∏ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) = 1 := by
      apply Finset.prod_eq_one; intro w _; rw [h1 w, one_pow]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) = 1 := by
      rw [show (fun v => ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (fun _ => (1 : ℝ)) from funext h2]
      exact finprod_one
    rw [hinf, hfin, mul_one]

  map_mul' a b := by
    show NumberField.Adeles.adelicAbsVal _ = NumberField.Adeles.adelicAbsVal _ *
      NumberField.Adeles.adelicAbsVal _
    unfold NumberField.Adeles.adelicAbsVal
    have hinf : (∏ w : InfinitePlace K,
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) =
        (∏ w, ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
        (∏ w, ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro w _
      have hmul : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w =
                  (a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).1 w = _; rfl
      rw [hmul]
      have hn : ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w‖ =
                ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ *
                ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ :=
        NormedField.norm_mul _ _
      erw [hn, mul_pow]
    have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖ =
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
        ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
      intro v
      have : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v =
             (a : NumberField.AdeleRing (𝓞 K) K).2 v *
             (b : NumberField.AdeleRing (𝓞 K) K).2 v := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).2 v = _; rfl
      rw [this, norm_mul]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (∏ᶠ v, ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖) *
        (∏ᶠ v, ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) := by
      rw [show (fun v => ‖((a * b : IdeleGroup K) :
            NumberField.AdeleRing (𝓞 K) K).2 v‖) =
          (fun v => ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
            ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) from funext hfmul]
      exact finprod_mul_distrib
        (adeleRing_unit_fin_norm_finMulSupport K a)
        (adeleRing_unit_fin_norm_finMulSupport K b)
    rw [hinf, hfin]; ring

lemma adelicNorm_eq (a : IdeleGroup K) :
    adelicNorm K a = NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K) :=
  rfl

def OneIdeleGroup : Subgroup (IdeleGroup K) :=
  (adelicNorm K).ker

lemma mem_OneIdeleGroup (a : IdeleGroup K) :
    a ∈ OneIdeleGroup K ↔ adelicNorm K a = 1 :=
  MonoidHom.mem_ker

lemma mem_OneIdeleGroup_iff (a : IdeleGroup K) :
    a ∈ OneIdeleGroup K ↔
      NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K) = 1 := by
  rw [mem_OneIdeleGroup, adelicNorm_eq]

set_option maxHeartbeats 400000 in
lemma adelicAbsVal_algebraMap (x : K) :
    NumberField.Adeles.adelicAbsVal (algebraMap K (NumberField.AdeleRing (𝓞 K) K) x) =
      (∏ w : InfinitePlace K, w x ^ w.mult) *
      ∏ᶠ (w : FinitePlace K), w x := by
  unfold NumberField.Adeles.adelicAbsVal
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    congr 1
    show ‖algebraMap K (w.Completion) x‖ = w x
    rw [show (algebraMap K w.Completion x) =
      (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
    rw [NumberField.InfinitePlace.Completion.norm_coe]
    simp
  · have h_comp : ∀ v : HeightOneSpectrum (𝓞 K),
        ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) x).2 v‖ =
          (FinitePlace.equivHeightOneSpectrum.symm v) x := by
      intro v
      show ‖algebraMap K (v.adicCompletion K) x‖ = _
      rw [FinitePlace.equivHeightOneSpectrum_symm_apply]; rfl
    rw [show (fun v => ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) x).2 v‖) =
      (fun v => (FinitePlace.equivHeightOneSpectrum.symm v) x) from funext h_comp]
    exact @finprod_comp_equiv (HeightOneSpectrum (𝓞 K)) (FinitePlace K) ℝ _
      FinitePlace.equivHeightOneSpectrum.symm (f := fun w => w x)

theorem principalIdeles_le_oneIdeleGroup :
    principalIdeles K ≤ OneIdeleGroup K := by
  intro a ha
  rw [mem_OneIdeleGroup_iff]
  obtain ⟨u, rfl⟩ := ha
  show NumberField.Adeles.adelicAbsVal
    ((principalIdeleEmb K u : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K) = 1
  have hval : ((principalIdeleEmb K u : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K) u.val := by
    simp [principalIdeleEmb, Units.map]
  rw [hval, adelicAbsVal_algebraMap]
  exact NumberField.prod_abs_eq_one (Units.ne_zero u)

lemma finAdeleRing_openSet (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) :
    IsOpen ({x : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S,
      x v ∈ (HeightOneSpectrum.adicCompletionIntegers K v : Set _)} :
        Set (FiniteAdeleRing (𝓞 K) K)) := by
  have hle : Filter.cofinite ≤ Filter.principal Sᶜ := by
    rw [Filter.le_principal_iff]
    exact Filter.eventually_cofinite.mpr (by simp; exact hS)
  have hopen := (RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => Valued.isOpen_valuationSubring
      (HeightOneSpectrum.adicCompletion K v)) hle).isOpen_range
  convert hopen using 1
  rw [RestrictedProduct.range_inclusion]
  ext x
  simp only [Set.mem_setOf_eq, Filter.eventually_principal, Set.mem_compl_iff,
    HeightOneSpectrum.adicCompletionIntegers]; rfl

lemma locallyFinite_finNorm :
    LocallyFinite (fun (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) =>
      Function.mulSupport
        (fun (a : IdeleGroup K) =>
          ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖)) := by
  intro a
  set S := {v : HeightOneSpectrum (𝓞 K) |
    (a : NumberField.AdeleRing (𝓞 K) K).2 v ∉
      (HeightOneSpectrum.adicCompletionIntegers K v : Set _)} ∪
    {v | (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v ∉
      (HeightOneSpectrum.adicCompletionIntegers K v : Set _)}
  have hSfin : S.Finite := by
    apply Set.Finite.union
    · exact Filter.eventually_cofinite.mp
        (a : NumberField.AdeleRing (𝓞 K) K).2.2
    · exact Filter.eventually_cofinite.mp
        (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2.2
  set W := {x : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S,
    x v ∈ (HeightOneSpectrum.adicCompletionIntegers K v : Set _)}
  set U := (fun b : IdeleGroup K =>
      (b : NumberField.AdeleRing (𝓞 K) K).2) ⁻¹' W ∩
    (fun b : IdeleGroup K =>
      (↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2) ⁻¹' W
  have hUopen : IsOpen U :=
    ((finAdeleRing_openSet K S hSfin).preimage
      (continuous_snd.comp Units.continuous_val)).inter
    ((finAdeleRing_openSet K S hSfin).preimage
      (continuous_snd.comp Units.continuous_coe_inv))
  have haU : a ∈ U :=
    ⟨fun v hv => by_contra (fun h => hv (Set.mem_union_left _ h)),
     fun v hv => by_contra (fun h => hv (Set.mem_union_right _ h))⟩
  refine ⟨U, hUopen.mem_nhds haU, hSfin.subset fun v ⟨b, hb_ms, hb_U⟩ => ?_⟩
  rw [Function.mem_mulSupport] at hb_ms
  by_contra hv_notS
  have hb1_mem : (b : NumberField.AdeleRing (𝓞 K) K).2 v ∈
      (HeightOneSpectrum.adicCompletionIntegers K v : Set _) :=
    hb_U.1 v hv_notS
  have hb2_mem : (↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v ∈
      (HeightOneSpectrum.adicCompletionIntegers K v : Set _) :=
    hb_U.2 v hv_notS
  have hn1 : ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hb1_mem
  have hn2 : ‖(↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hb2_mem
  have hmul : (↑b : NumberField.AdeleRing (𝓞 K) K).2 v *
      (↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v = 1 := by
    change ((↑b : NumberField.AdeleRing (𝓞 K) K).2 *
      (↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2) v =
      (1 : NumberField.AdeleRing (𝓞 K) K).2 v
    congr 1; exact congr_arg Prod.snd (Units.mul_inv b)
  have hnm : ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
      ‖(↑b⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hge : 1 ≤ ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
    by_contra hlt; push Not at hlt
    linarith [mul_le_mul_of_nonneg_left hn2
      (norm_nonneg ((b : NumberField.AdeleRing (𝓞 K) K).2 v))]
  exact hb_ms (le_antisymm hn1 hge)

theorem continuous_adelicNorm : Continuous (adelicNorm K) := by
  show Continuous (fun a : IdeleGroup K =>
    NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K))
  unfold NumberField.Adeles.adelicAbsVal
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w _
    apply Continuous.pow
    apply continuous_norm.comp
    exact (continuous_apply w).comp
      (continuous_fst.comp Units.continuous_val)
  · apply continuous_finprod
    · intro v
      apply continuous_norm.comp
      exact (RestrictedProduct.continuous_eval v).comp
        (continuous_snd.comp Units.continuous_val)
    · exact locallyFinite_finNorm K

theorem oneIdeles_isClosed_in_ideles :
    IsClosed (OneIdeleGroup K : Set (IdeleGroup K)) := by
  have h : (OneIdeleGroup K : Set (IdeleGroup K)) = adelicNorm K ⁻¹' {1} := by
    ext x; simp [OneIdeleGroup, MonoidHom.mem_ker]
  rw [h]
  exact isClosed_singleton.preimage (continuous_adelicNorm K)

theorem infiniteAdeleRing_units_isOpen :
    IsOpen {x : InfiniteAdeleRing K | IsUnit x} := by
  have heq : {x : InfiniteAdeleRing K | IsUnit x} =
      ⋂ w : InfinitePlace K, (fun x : InfiniteAdeleRing K => x w) ⁻¹' {a | IsUnit a} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact Pi.isUnit_iff
  rw [heq]
  apply isOpen_iInter_of_finite
  intro w
  exact (Units.isOpen (R := w.Completion)).preimage (continuous_apply w)






lemma ring_inverse_prod_eq_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (x : A × B) (hx : IsUnit x) :
    Ring.inverse x = (Ring.inverse x.1, Ring.inverse x.2) := by
  have h1 : IsUnit x.1 := (Prod.isUnit_iff.mp hx).1
  have h2 : IsUnit x.2 := (Prod.isUnit_iff.mp hx).2
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit u]
  conv_rhs => rw [← h1.unit_spec, ← h2.unit_spec, Ring.inverse_unit, Ring.inverse_unit]
  ext
  · change (↑u⁻¹ : A × B).1 = ↑(h1.unit⁻¹ : Aˣ)
    have : h1.unit = (MulEquiv.prodUnits u).1 := by
      apply Units.val_injective; simp [IsUnit.unit_spec, MulEquiv.prodUnits]
    rw [this]; simp [MulEquiv.prodUnits]
  · change (↑u⁻¹ : A × B).2 = ↑(h2.unit⁻¹ : Bˣ)
    have : h2.unit = (MulEquiv.prodUnits u).2 := by
      apply Units.val_injective; simp [IsUnit.unit_spec, MulEquiv.prodUnits]
    rw [this]; simp [MulEquiv.prodUnits]

omit [NumberField K] in
lemma infiniteAdeleRing_inverse_apply (x : InfiniteAdeleRing K) (hx : IsUnit x)
    (w : InfinitePlace K) :
    (Ring.inverse x) w = Ring.inverse (x w) := by
  rw [← hx.unit_spec, Ring.inverse_unit hx.unit]
  have hw : IsUnit ((↑hx.unit : InfiniteAdeleRing K) w) := hx.apply w
  conv_rhs => rw [← hw.unit_spec, Ring.inverse_unit]
  exact IsUnit.val_inv_apply hx w

omit [NumberField K] in
lemma infiniteAdeleRing_continuousOn_ringInverse :
    ContinuousOn Ring.inverse
      {x : InfiniteAdeleRing K | IsUnit x} := by
  have hcongr : ∀ x ∈ {x : InfiniteAdeleRing K | IsUnit x},
      Ring.inverse x = (fun y : InfiniteAdeleRing K => fun w => Ring.inverse (y w)) x := by
    intro x hx; funext w; exact infiniteAdeleRing_inverse_apply K x hx w
  refine ContinuousOn.congr ?_ hcongr
  apply continuousOn_pi.mpr
  intro w
  have : (fun (y : InfiniteAdeleRing K) => Ring.inverse (y w)) =
      (fun a : w.Completion => Ring.inverse a) ∘ (fun y : InfiniteAdeleRing K => y w) := rfl
  rw [this]
  refine ContinuousOn.comp (t := {a : w.Completion | IsUnit a})
    ?_ (continuous_apply w).continuousOn ?_
  · intro a (ha : IsUnit a)
    exact (NormedRing.inverse_continuousAt ha.unit).continuousWithinAt
  · intro x (hx : IsUnit x); exact hx.apply w

set_option maxHeartbeats 800000 in
lemma finiteAdeleRing_inverse_apply (x : FiniteAdeleRing (𝓞 K) K) (hx : IsUnit x)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (Ring.inverse x) v = Ring.inverse (x v) := by
  obtain ⟨u, rfl⟩ := hx
  have hv : IsUnit ((↑u : FiniteAdeleRing (𝓞 K) K) v) :=
    ⟨⟨(↑u : FiniteAdeleRing (𝓞 K) K) v, (↑(u⁻¹ : _ˣ) : FiniteAdeleRing (𝓞 K) K) v,
      DFunLike.congr_fun u.val_inv v, DFunLike.congr_fun u.inv_val v⟩, rfl⟩
  rw [Ring.inverse_unit u, ← hv.unit_spec, Ring.inverse_unit]
  have hue : hv.unit = ⟨(↑u : FiniteAdeleRing _ K) v, (↑(u⁻¹ : _ˣ) : FiniteAdeleRing _ K) v,
      DFunLike.congr_fun u.val_inv v, DFunLike.congr_fun u.inv_val v⟩ :=
    Units.val_injective hv.unit_spec
  rw [hue]; rfl









theorem oneIdeles_isClosed :
    IsClosed (OneIdeleGroup K : Set (IdeleGroup K)) :=
  oneIdeles_isClosed_in_ideles K

theorem adelic_box_isCompact (a : NumberField.AdeleRing (𝓞 K) K) :
    IsCompact {x : NumberField.AdeleRing (𝓞 K) K |
      ∀ v : NumberField.Adeles.Place K,
        NumberField.Adeles.placeNormAdele v x ≤
          NumberField.Adeles.placeNormAdele v a} := by


  have heq : {x : NumberField.AdeleRing (𝓞 K) K |
      ∀ v : NumberField.Adeles.Place K,
        NumberField.Adeles.placeNormAdele v x ≤
          NumberField.Adeles.placeNormAdele v a} =
    {y : InfiniteAdeleRing K | ∀ w : InfinitePlace K, ‖y w‖ ≤ ‖a.1 w‖} ×ˢ
    {z : FiniteAdeleRing (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), ‖z v‖ ≤ ‖a.2 v‖} := by
    ext ⟨x_inf, x_fin⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun w => h (.infinite w), fun v => h (.finite v)⟩
    · intro ⟨h_inf, h_fin⟩ v
      match v with
      | .infinite w => exact h_inf w
      | .finite vi => exact h_fin vi
  rw [heq]

  have h_inf : IsCompact {y : InfiniteAdeleRing K | ∀ w : InfinitePlace K, ‖y w‖ ≤ ‖a.1 w‖} := by
    have : {y : InfiniteAdeleRing K | ∀ w : InfinitePlace K, ‖y w‖ ≤ ‖a.1 w‖} =
        Set.univ.pi (fun w => Metric.closedBall (0 : (InfinitePlace.Completion w)) ‖a.1 w‖) := by
      ext y
      simp only [Set.mem_setOf_eq]
      show (∀ (w : InfinitePlace K), ‖y w‖ ≤ ‖a.1 w‖) ↔
        ∀ (i : InfinitePlace K), i ∈ Set.univ → y i ∈ Metric.closedBall 0 ‖a.1 i‖
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [this]
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 ‖a.1 w‖

  have h_fin : IsCompact {z : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K), ‖z v‖ ≤ ‖a.2 v‖} := by
    open RestrictedProduct Set Filter in

    set S : Set (HeightOneSpectrum (𝓞 K)) :=
      {v | (a.2 : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K))} with S_def

    have hS_cofin : cofinite ≤ 𝓟 S := by
      rw [le_principal_iff, Filter.mem_cofinite]
      have hmem := a.2.property
      simp only [Filter.Eventually, Filter.mem_cofinite] at hmem
      exact hmem

    set piBox : Set ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :=
      univ.pi (fun v => Metric.closedBall 0 ‖a.2 v‖) with piBox_def

    have piBox_compact : IsCompact piBox :=
      isCompact_univ_pi fun v => isCompact_closedBall 0 ‖a.2 v‖

    have mem_integers_iff : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
        x ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ↔
        Valued.v x ≤ 1 := by
      intro v x
      exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

    have norm_le_val : ∀ (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K),
        ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := by
      intro v x y
      exact Valued.toNormedField.norm_le_iff

    have piBox_sub_range : piBox ⊆ range (DFunLike.coe :
        (Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K),
          ↑(v.adicCompletionIntegers K)]_[𝓟 S]) → _) := by
      rw [range_coe_principal]
      intro f hf v hv
      simp only [piBox_def, mem_univ_pi, Metric.mem_closedBall, dist_zero_right] at hf


      change Valued.v (f v) ≤ 1
      have hav : Valued.v ((a.2 : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v) ≤ 1 := by
        have := hv
        change (a.2 : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v ∈
          (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) at this
        rwa [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact le_trans ((norm_le_val v _ _).mp (hf v)) hav

    have h_compact_principal : IsCompact ((DFunLike.coe :
        (Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K),
          ↑(v.adicCompletionIntegers K)]_[𝓟 S]) → _) ⁻¹' piBox) :=
      (isEmbedding_coe_of_principal.isCompact_preimage_iff piBox_sub_range).mpr piBox_compact

    have h_box_eq : {z : FiniteAdeleRing (𝓞 K) K |
        ∀ v : HeightOneSpectrum (𝓞 K), ‖z v‖ ≤ ‖a.2 v‖} =
      (inclusion _ _ hS_cofin) '' ((DFunLike.coe :
        (Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K),
          ↑(v.adicCompletionIntegers K)]_[𝓟 S]) → _) ⁻¹' piBox) := by
      ext z
      constructor
      · intro hz
        simp only [mem_setOf_eq] at hz

        have hz_mem : ∀ v ∈ S, (z : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v ∈
            (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
          intro v hv
          rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
          have hav : Valued.v ((a.2 : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v) ≤ 1 := by
            rw [← HeightOneSpectrum.mem_adicCompletionIntegers, ← SetLike.mem_coe]
            exact hv
          exact le_trans ((norm_le_val v _ _).mp (hz v)) hav
        have hz_principal : ∀ᶠ v in 𝓟 S,
            (z : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v ∈
            (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
          Filter.eventually_principal.mpr hz_mem

        let z' : Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K),
            ↑(v.adicCompletionIntegers K)]_[𝓟 S] :=
          ⟨(z : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), hz_principal⟩
        refine ⟨z', ?_, ?_⟩
        ·
          simp only [mem_preimage, piBox_def, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
          intro v
          show ‖(z : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v‖ ≤ ‖a.2 v‖
          exact hz v
        ·
          rfl
      · intro ⟨w, hw, hwz⟩
        simp only [mem_setOf_eq]
        intro v
        simp only [mem_preimage, piBox_def, mem_univ_pi, Metric.mem_closedBall, dist_zero_right] at hw
        rw [show (z : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v =
            (w : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) v from by
          have := congr_fun (congr_arg Subtype.val hwz) v
          simp only [inclusion_apply] at this
          exact this.symm]
        exact hw v
    rw [h_box_eq]
    exact h_compact_principal.image (continuous_inclusion hS_cofin)

  exact h_inf.prod h_fin


theorem adelicAbsVal_mul (a b : NumberField.AdeleRing (𝓞 K) K)
    (ha : (Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => ‖a.2 v‖)).Finite)
    (hb : (Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => ‖b.2 v‖)).Finite) :
    NumberField.Adeles.adelicAbsVal (a * b) =
      NumberField.Adeles.adelicAbsVal a * NumberField.Adeles.adelicAbsVal b := by
  unfold NumberField.Adeles.adelicAbsVal
  have hinf : (∏ w : InfinitePlace K,
      ‖(a * b).1 w‖ ^ w.mult) =
      (∏ w, ‖a.1 w‖ ^ w.mult) *
      (∏ w, ‖b.1 w‖ ^ w.mult) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro w _
    have hmul : (a * b).1 w = a.1 w * b.1 w := rfl
    rw [hmul]
    have hn : ‖a.1 w * b.1 w‖ = ‖a.1 w‖ * ‖b.1 w‖ :=
      NormedField.norm_mul _ _
    erw [hn, mul_pow]
  have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(a * b).2 v‖ = ‖a.2 v‖ * ‖b.2 v‖ := by
    intro v
    have : (a * b).2 v = a.2 v * b.2 v := rfl
    rw [this, norm_mul]
  have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(a * b).2 v‖) =
      (∏ᶠ v, ‖a.2 v‖) * (∏ᶠ v, ‖b.2 v‖) := by
    rw [show (fun v => ‖(a * b).2 v‖) =
        (fun v => ‖a.2 v‖ * ‖b.2 v‖) from funext hfmul]
    exact finprod_mul_distrib ha hb
  rw [hinf, hfin]; ring

theorem placeNormAdele_mul (v : NumberField.Adeles.Place K)
    (a b : NumberField.AdeleRing (𝓞 K) K) :
    NumberField.Adeles.placeNormAdele v (a * b) =
      NumberField.Adeles.placeNormAdele v a * NumberField.Adeles.placeNormAdele v b := by
  cases v with
  | finite vi =>
    show ‖(a * b).2 vi‖ = ‖a.2 vi‖ * ‖b.2 vi‖
    have : (a * b).2 vi = a.2 vi * b.2 vi := rfl
    rw [this]
    exact NormedField.norm_mul (a.2 vi) (b.2 vi)
  | infinite w =>
    show ‖(a * b).1 w‖ = ‖a.1 w‖ * ‖b.1 w‖
    have : (a * b).1 w = a.1 w * b.1 w := rfl
    rw [this]
    exact NormedField.norm_mul (a.1 w) (b.1 w)




theorem fujisaki_lemma_discrete :
    DiscreteTopology ((principalIdeles K).subgroupOf (OneIdeleGroup K)) := by
  haveI := principalIdeles_discrete K
  apply DiscreteTopology.of_continuous_injective
    (f := fun (x : (principalIdeles K).subgroupOf (OneIdeleGroup K)) =>
      (⟨x.val.val, x.prop⟩ : (principalIdeles K)))
  · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  · intro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)


abbrev NormOneIdeleClassGroup :=
    (OneIdeleGroup K) ⧸ (principalIdeles K).subgroupOf (OneIdeleGroup K)

end OneIdeles

section ProfiniteGroups

open CategoryTheory in
class IsProfiniteGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  isInverseLimitOfFiniteGroups :
    ∃ (J : Type) (_ : SmallCategory J) (F : Functor J FiniteGrp.{0}),
      Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp))

open CategoryTheory in
theorem compact_totally_disconnected_is_profinite
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    IsProfiniteGroup G := by
  let P := ProfiniteGrp.of G
  have e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  exact ⟨OpenNormalSubgroup G, inferInstance, P.toFiniteQuotientFunctor, ⟨e⟩⟩

open CategoryTheory in
theorem profinite_iff_totallyDisconnected_compact
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    IsProfiniteGroup G ↔ (CompactSpace G ∧ TotallyDisconnectedSpace G) where
  mp h := by
    refine ⟨?_, ?_⟩
    · obtain ⟨J, hJ, F, ⟨e⟩⟩ := h.isInverseLimitOfFiniteGroups
      exact e.toHomeomorph.symm.compactSpace
    · obtain ⟨J, hJ, F, ⟨e⟩⟩ := h.isInverseLimitOfFiniteGroups
      exact e.toHomeomorph.symm.totallyDisconnectedSpace
  mpr h := by
    haveI := h.1
    haveI := h.2
    exact compact_totally_disconnected_is_profinite G

def profiniteTransitionMap {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N₁ N₂ : OpenNormalSubgroup G) (h : N₁ ≤ N₂) :
    G ⧸ (N₁ : Subgroup G) →* G ⧸ (N₂ : Subgroup G) :=
  QuotientGroup.map (N₁ : Subgroup G) (N₂ : Subgroup G) (MonoidHom.id G)
    (by simpa using h)

def profiniteCompletionSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    Subgroup ((N : OpenNormalSubgroup G) → G ⧸ (N : Subgroup G)) where
  carrier := { f | ∀ (N₁ N₂ : OpenNormalSubgroup G) (h : N₁ ≤ N₂),
    profiniteTransitionMap N₁ N₂ h (f N₁) = f N₂ }
  mul_mem' := by
    intro a b ha hb N₁ N₂ h
    simp only [Pi.mul_apply, map_mul, ha N₁ N₂ h, hb N₁ N₂ h]
  one_mem' := by
    intro N₁ N₂ h
    simp only [Pi.one_apply, map_one]
  inv_mem' := by
    intro a ha N₁ N₂ h
    simp only [Pi.inv_apply, map_inv, ha N₁ N₂ h]

def toProfiniteCompletion (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : G →* profiniteCompletionSubgroup G where
  toFun g := ⟨fun N => QuotientGroup.mk' _ g,
    fun N₁ N₂ h => by simp [profiniteTransitionMap]⟩
  map_one' := by
    ext N
    simp [QuotientGroup.mk'_apply]
  map_mul' x y := by
    ext N
    simp [QuotientGroup.mk'_apply]

theorem profiniteCompletion_denseRange
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    DenseRange (toProfiniteCompletion G) := by
  intro x
  rw [mem_closure_iff]
  intro O hO hxO
  rw [isOpen_induced_iff] at hO
  obtain ⟨U, hUopen, hU⟩ := hO
  have hxU : x.val ∈ U := by rw [← hU] at hxO; exact hxO
  rw [isOpen_pi_iff] at hUopen
  obtain ⟨I, u, hIu, hpiU⟩ := hUopen x.val hxU
  by_cases hI : I.Nonempty
  · let N₀ := I.inf' hI id
    have hN₀_le : ∀ N ∈ I, N₀ ≤ N := fun N hN => Finset.inf'_le id hN
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N₀ : Subgroup G) (x.val N₀)
    refine ⟨toProfiniteCompletion G g, ?_, ⟨g, rfl⟩⟩
    rw [← hU]
    show (toProfiniteCompletion G g).val ∈ U
    apply hpiU
    intro N hN
    suffices h : (toProfiniteCompletion G g).val N = x.val N by
      rw [h]; exact (hIu N (Finset.mem_coe.mp hN)).2
    show QuotientGroup.mk' _ g = x.val N
    have hcompat := x.prop N₀ N (hN₀_le N (Finset.mem_coe.mp hN))
    have htrans : profiniteTransitionMap N₀ N (hN₀_le N (Finset.mem_coe.mp hN))
        (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ g := by
      simp [profiniteTransitionMap]
    rw [← hcompat, ← hg, htrans]
  · rw [Finset.not_nonempty_iff_eq_empty] at hI
    refine ⟨toProfiniteCompletion G 1, ?_, ⟨1, rfl⟩⟩
    rw [← hU]
    show (toProfiniteCompletion G 1).val ∈ U
    apply hpiU
    rw [hI]
    simp [Set.pi]

def IsStronglyComplete (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

noncomputable def abstractTransitionMap {G : Type*} [Group G]
    (N₁ N₂ : _root_.FiniteIndexNormalSubgroup G) (h : N₁ ≤ N₂) :
    G ⧸ (N₁ : Subgroup G) →* G ⧸ (N₂ : Subgroup G) := by
  haveI : (N₁ : Subgroup G).Normal := N₁.isNormal'
  haveI : (N₂ : Subgroup G).Normal := N₂.isNormal'
  exact QuotientGroup.map (N₁ : Subgroup G) (N₂ : Subgroup G) (MonoidHom.id G) (by simpa using h)

noncomputable def abstractProfiniteCompletionSubgroup (G : Type*) [Group G] :
    Subgroup ((N : _root_.FiniteIndexNormalSubgroup G) → G ⧸ (N : Subgroup G)) where
  carrier := { f | ∀ (N₁ N₂ : _root_.FiniteIndexNormalSubgroup G) (h : N₁ ≤ N₂),
    abstractTransitionMap N₁ N₂ h (f N₁) = f N₂ }
  mul_mem' := by
    intro a b ha hb N₁ N₂ h
    simp only [Pi.mul_apply, map_mul, ha N₁ N₂ h, hb N₁ N₂ h]
  one_mem' := by
    intro N₁ N₂ h
    simp only [Pi.one_apply, map_one]
  inv_mem' := by
    intro a ha N₁ N₂ h
    simp only [Pi.inv_apply, map_inv, ha N₁ N₂ h]

noncomputable def toAbstractProfiniteCompletion (G : Type*) [Group G] :
    G →* abstractProfiniteCompletionSubgroup G where
  toFun g := ⟨fun N => by
    haveI := N.isNormal'
    exact QuotientGroup.mk' _ g,
    fun N₁ N₂ h => by simp [abstractTransitionMap]⟩
  map_one' := by ext N; simp [QuotientGroup.mk'_apply]
  map_mul' x y := by ext N; simp [QuotientGroup.mk'_apply]

noncomputable def OpenNormalSubgroup.comapContinuousMulEquiv
    {G : Type*} {H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : OpenNormalSubgroup H) : OpenNormalSubgroup G where
  toOpenSubgroup := {
    toSubgroup := (N : Subgroup H).comap e.toMonoidHom
    isOpen' := by
      show IsOpen ((N : Subgroup H).comap e.toMonoidHom : Set G)
      rw [Subgroup.coe_comap]
      exact e.toHomeomorph.isOpen_preimage.mpr N.toOpenSubgroup.isOpen'
  }
  isNormal' := by
    show ((N : Subgroup H).comap e.toMonoidHom).Normal
    exact N.isNormal'.comap e.toMonoidHom

open CategoryTheory in
noncomputable def quotientMulEquivOfContinuousMulEquiv
    {G : Type*} {H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : OpenNormalSubgroup H) :
    H ⧸ (N : Subgroup H) ≃*
      G ⧸ (OpenNormalSubgroup.comapContinuousMulEquiv e N : Subgroup G) := by
  haveI : ((N : Subgroup H).comap e.toMonoidHom).Normal := N.isNormal'.comap e.toMonoidHom
  haveI : (N : Subgroup H).Normal := N.isNormal'
  exact (QuotientGroup.congr _ _ e.toMulEquiv
    (Subgroup.map_comap_eq_self_of_surjective e.toMulEquiv.surjective _)).symm

open CategoryTheory in
theorem profiniteGroup_iso_invLim_quotients
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [IsProfiniteGroup G] :
    ∃ (J : Type) (_ : SmallCategory J) (F : Functor J FiniteGrp.{0}),
      Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)) ∧

      ∀ j : J, ∃ U : OpenNormalSubgroup G,
        Nonempty ((F.obj j : Type _) ≃* G ⧸ (U : Subgroup G)) := by
  obtain ⟨J₀, hJ₀, F₀, ⟨e₀⟩⟩ := IsProfiniteGroup.isInverseLimitOfFiniteGroups (G := G)
  let L := ProfiniteGrp.limit (F₀ ⋙ forget₂ FiniteGrp ProfiniteGrp)
  have e_L := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor L
  refine ⟨OpenNormalSubgroup L, inferInstance, L.toFiniteQuotientFunctor,
    ⟨e₀.trans e_L⟩, fun j => ?_⟩
  exact ⟨OpenNormalSubgroup.comapContinuousMulEquiv e₀ j,
    ⟨quotientMulEquivOfContinuousMulEquiv e₀ j⟩⟩

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem isClosed_finiteIndexNormal_of_bijective_abstractCompletion
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hbij : Function.Bijective (toAbstractProfiniteCompletion G))
    (N : _root_.FiniteIndexNormalSubgroup G) :
    IsClosed (N.toSubgroup : Set G) := by
  haveI := N.isNormal'
  haveI := N.isFiniteIndex'
  apply Subgroup.isClosed_of_isOpen

  haveI : N.toSubgroup.topologicalClosure.Normal :=
    Subgroup.is_normal_topologicalClosure N.toSubgroup
  haveI : N.toSubgroup.topologicalClosure.FiniteIndex :=
    Subgroup.finiteIndex_of_le N.toSubgroup.le_topologicalClosure
  have hNcl_open : IsOpen (N.toSubgroup.topologicalClosure : Set G) :=
    N.toSubgroup.topologicalClosure.isOpen_of_isClosed_of_finiteIndex
      N.toSubgroup.isClosed_topologicalClosure

  suffices hcl : N.toSubgroup.topologicalClosure = N.toSubgroup by rw [← hcl]; exact hNcl_open
  refine le_antisymm ?_ N.toSubgroup.le_topologicalClosure

  let ψ := lift (GrpCat.ofHom (MonoidHom.id G) :
    GrpCat.of G ⟶ GrpCat.of (ProfiniteGrp.of G))

  have hψη : ∀ g : G, ψ.hom (etaFn (GrpCat.of G) g) = g := by
    intro g
    have h := lift_eta (GrpCat.ofHom (MonoidHom.id G) :
        GrpCat.of G ⟶ GrpCat.of (of G))
    exact congrFun (congrArg (fun f => f.hom) h) g

  have hη_surj : Function.Surjective (etaFn (GrpCat.of G)) := by
    intro ⟨f, hf⟩
    have hf' : ∀ (N₁ N₂ : _root_.FiniteIndexNormalSubgroup G) (h : N₁ ≤ N₂),
        abstractTransitionMap N₁ N₂ h (f N₁) = f N₂ := by
      intro N₁ N₂ h
      exact hf (homOfLE h)
    obtain ⟨g, hg⟩ := hbij.2 ⟨f, hf'⟩
    refine ⟨g, Subtype.ext (funext fun M => ?_)⟩
    have := congr_arg (fun x => x.val M) hg
    simp only [toAbstractProfiniteCompletion, MonoidHom.coe_mk, OneHom.coe_mk] at this
    exact this

  have hN_eq : (N.toSubgroup : Set G) = ψ.hom '' {x | (x : _).val N = 1} := by
    ext g; constructor
    · intro hg
      refine ⟨etaFn _ g, ?_, hψη g⟩
      simp only [Set.mem_setOf_eq, etaFn]
      exact (QuotientGroup.eq_one_iff g).mpr hg
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g', rfl⟩ := hη_surj x
      rw [hψη]
      exact (QuotientGroup.eq_one_iff g').mp hx

  have hN_closed : IsClosed (N.toSubgroup : Set G) := by
    rw [hN_eq]
    exact (isClosed_singleton.preimage
      ((limitCone (diagram (GrpCat.of G))).π.app N).hom.continuous_toFun).isCompact.image
      ψ.hom.continuous_toFun |>.isClosed
  exact Subgroup.topologicalClosure_minimal N.toSubgroup le_rfl hN_closed
open CategoryTheory in
theorem profiniteGroup_stronglyComplete_iff
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [IsProfiniteGroup G] :
    IsStronglyComplete G ↔


      Function.Bijective (toAbstractProfiniteCompletion G) := by

  obtain ⟨J₀, hJ₀, F₀, ⟨eG⟩⟩ := IsProfiniteGroup.isInverseLimitOfFiniteGroups (G := G)
  haveI : CompactSpace G := eG.toHomeomorph.symm.compactSpace
  haveI : TotallyDisconnectedSpace G := eG.toHomeomorph.symm.totallyDisconnectedSpace
  constructor
  ·
    intro hsc
    constructor
    ·
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hne

      obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        isOpen_compl_singleton
        (Set.mem_compl_singleton_iff.mpr (fun h : (1 : G) = x => hne h.symm))

      haveI : Finite (G ⧸ (U : Subgroup G)) :=
        (U : Subgroup G).quotient_finite_of_isOpen U.toOpenSubgroup.isOpen'
      haveI : (U : Subgroup G).Normal := U.isNormal'
      haveI : (U : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      let N : _root_.FiniteIndexNormalSubgroup G := { toSubgroup := (U : Subgroup G) }

      have hxN : x ∈ (N : Subgroup G) := by
        rw [MonoidHom.mem_ker] at hx
        have hcomp : (toAbstractProfiniteCompletion G x).val N = 1 := by rw [hx]; rfl
        simp only [toAbstractProfiniteCompletion, MonoidHom.coe_mk, OneHom.coe_mk] at hcomp
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomp

      exact absurd (hU hxN) (by simp)
    ·
      intro ⟨f, hf⟩


      have hC_nonempty : ∀ N : _root_.FiniteIndexNormalSubgroup G,
          (QuotientGroup.mk' (N : Subgroup G) ⁻¹' {f N}).Nonempty := by
        intro N
        haveI := N.isNormal'
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N.toSubgroup (f N)
        exact ⟨g, Set.mem_preimage.mpr (by simp [hg])⟩
      have hC_closed : ∀ N : _root_.FiniteIndexNormalSubgroup G,
          IsClosed (QuotientGroup.mk' (N : Subgroup G) ⁻¹' {f N}) := by
        intro N
        haveI := N.isNormal'

        have hNopen : IsOpen (N.toSubgroup : Set G) := hsc N.toSubgroup N.isFiniteIndex'
        haveI : DiscreteTopology (G ⧸ N.toSubgroup) := QuotientGroup.discreteTopology hNopen
        exact IsClosed.preimage continuous_quotient_mk' isClosed_singleton

      have hC_directed : Directed (· ⊇ ·) (fun N : _root_.FiniteIndexNormalSubgroup G =>
          QuotientGroup.mk' (N : Subgroup G) ⁻¹' {f N}) := by
        intro N₁ N₂
        haveI := N₁.isNormal'
        haveI := N₂.isNormal'
        haveI := N₁.isFiniteIndex'
        haveI := N₂.isFiniteIndex'
        let N₃ : _root_.FiniteIndexNormalSubgroup G :=
          { toSubgroup := N₁.toSubgroup ⊓ N₂.toSubgroup }
        refine ⟨N₃, ?_, ?_⟩
        · intro g hg
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
          haveI := N₃.isNormal'
          have h13 : N₃.toSubgroup ≤ N₁.toSubgroup := inf_le_left
          rw [← hf N₃ N₁ h13, ← hg]
          simp [abstractTransitionMap]
        · intro g hg
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
          haveI := N₃.isNormal'
          have h23 : N₃.toSubgroup ≤ N₂.toSubgroup := inf_le_right
          rw [← hf N₃ N₂ h23, ← hg]
          simp [abstractTransitionMap]

      haveI : Nonempty (_root_.FiniteIndexNormalSubgroup G) := ⟨{ toSubgroup := ⊤ }⟩
      obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        _ hC_directed hC_nonempty (fun N => (hC_closed N).isCompact) hC_closed

      refine ⟨g, Subtype.ext (funext fun N => ?_)⟩
      have hgN := Set.mem_iInter.mp hg N
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hgN
      simp only [toAbstractProfiniteCompletion, MonoidHom.coe_mk, OneHom.coe_mk]
      haveI := N.isNormal'
      exact hgN
  ·


    intro ⟨hinj, hsurj⟩ H hH_fi


    haveI : H.FiniteIndex := hH_fi
    haveI : H.normalCore.FiniteIndex := Subgroup.finiteIndex_normalCore H
    suffices hopen : IsOpen (H.normalCore : Set G) from
      Subgroup.isOpen_mono H.normalCore_le hopen

    haveI : H.normalCore.Normal := Subgroup.normalCore_normal H


    apply Subgroup.isOpen_of_isClosed_of_finiteIndex


    let N₀ : _root_.FiniteIndexNormalSubgroup G :=
      { toSubgroup := H.normalCore }
    exact isClosed_finiteIndexNormal_of_bijective_abstractCompletion G ⟨hinj, hsurj⟩ N₀

theorem profiniteGroup_closed_finiteIndex_isOpen
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [IsProfiniteGroup G]
    (H : Subgroup G) [H.FiniteIndex] (hcl : IsClosed (H : Set G)) :
    IsOpen (H : Set G) :=
  H.isOpen_of_isClosed_of_finiteIndex hcl

open CategoryTheory in
theorem profiniteGroup_isCompletion_of_denseSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [IsProfiniteGroup G]
    (Γ : Subgroup G) (hΓ : Dense (Γ : Set G)) :


    ∃ (Ĝ : Type) (_ : Group Ĝ) (_ : TopologicalSpace Ĝ) (_ : IsProfiniteGroup Ĝ)
      (φ : Γ →* Ĝ) (_ : Dense (Set.range φ)),
      Nonempty (G ≃* Ĝ) := by
  obtain ⟨J, hJ, F, ⟨e⟩⟩ := IsProfiniteGroup.isInverseLimitOfFiniteGroups (G := G)
  let L := ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)
  refine ⟨L, inferInstance, inferInstance, ⟨⟨J, hJ, F, ⟨ContinuousMulEquiv.refl L⟩⟩⟩,
    e.toMulEquiv.toMonoidHom.comp Γ.subtype, ?_, ⟨e.toMulEquiv⟩⟩
  have : Set.range (e.toMulEquiv.toMonoidHom.comp Γ.subtype) = e '' ↑Γ := by
    ext x
    simp only [Set.mem_range, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩; exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  rw [this]
  exact DenseRange.dense_image e.surjective.denseRange e.continuous hΓ

end ProfiniteGroups

section InfiniteGalois

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem restrictNormalHom_surjective [IsGalois k K]
    (F : IntermediateField k K) [Normal k F] :
    Function.Surjective
      (AlgEquiv.restrictNormalHom (↥F) : (K ≃ₐ[k] K) →* (↥F ≃ₐ[k] ↥F)) :=
  @AlgEquiv.restrictNormalHom_surjective k _ (↥F) _ _ K _ _ _ _ _ _

theorem fixedField_of_fixingSubgroup [IsGalois k K]
    (F : IntermediateField k K) :
    IntermediateField.fixedField F.fixingSubgroup = F :=
  InfiniteGalois.fixedField_fixingSubgroup F

theorem fixingSubgroup_normal_of_normal [IsGalois k K]
    (F : IntermediateField k K) [Normal k F] :
    F.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker]
  exact MonoidHom.normal_ker _

theorem krullTopology_nhds_one_iff [IsGalois k K]
    (A : Set (K ≃ₐ[k] K)) : A ∈ nhds (1 : K ≃ₐ[k] K) ↔
      ∃ (E : IntermediateField k K),
        FiniteDimensional k E ∧
          (E.fixingSubgroup : Set (K ≃ₐ[k] K)) ⊆ A :=
  krullTopology_mem_nhds_one_iff k K A

noncomputable def galoisGroup_continuousMulEquiv_limit [IsGalois k K] :
    Gal(K/k) ≃ₜ*
      (ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor k K)).toProfinite.toTop :=
  InfiniteGalois.continuousMulEquivToLimit k K

theorem galoisGroup_openNormalSubgroups [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    (IsOpen (N : Set (K ≃ₐ[k] K)) ∧ N.Normal) ↔
    ∃ (F : IntermediateField k K), FiniteDimensional k F ∧ Normal k F ∧
      N = F.fixingSubgroup := by
  constructor
  ·
    intro ⟨hopen, hnormal⟩

    have hclosed : IsClosed (N : Set (K ≃ₐ[k] K)) := Subgroup.isClosed_of_isOpen N hopen
    let Ncl : ClosedSubgroup (K ≃ₐ[k] K) := ⟨N, hclosed⟩

    let F := IntermediateField.fixedField (N : Subgroup (K ≃ₐ[k] K))
    use F
    have hfix : F.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField Ncl

    have hFinDim : FiniteDimensional k F := by
      rw [← InfiniteGalois.isOpen_iff_finite F]; rw [hfix]; exact hopen

    have hIsGalois : IsGalois k F :=
      (InfiniteGalois.normal_iff_isGalois F).mp (hfix ▸ hnormal)
    exact ⟨hFinDim, hIsGalois.to_normal, hfix.symm⟩
  ·
    intro ⟨F, hfin, hnormal, hN⟩
    subst hN
    exact ⟨IntermediateField.fixingSubgroup_isOpen F,
      (InfiniteGalois.normal_iff_isGalois F).mpr IsGalois.mk⟩

theorem fundamentalTheoremInfiniteGalois [IsGalois k K] :
    Nonempty ((IntermediateField k K)ᵒᵈ ≃o ClosedSubgroup (K ≃ₐ[k] K)) :=
  ⟨InfiniteGalois.IntermediateFieldEquivClosedSubgroup.dual⟩

theorem fixedField_finrank_eq_index [IsGalois k K]
    (H : ClosedSubgroup (K ≃ₐ[k] K)) :
    Module.finrank k (IntermediateField.fixedField (H : Subgroup (K ≃ₐ[k] K))) =
      (H : Subgroup (K ≃ₐ[k] K)).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      InfiniteGalois.fixingSubgroup_fixedField]

@[deprecated (since := "2025-05-04")] alias theorem_26_24_degree_eq_index := fixedField_finrank_eq_index

theorem quotient_continuousMulEquiv_fixedField [IsGalois k K]
    (H : ClosedSubgroup (K ≃ₐ[k] K)) [(H : Subgroup (K ≃ₐ[k] K)).Normal] :
    Nonempty ((K ≃ₐ[k] K) ⧸ (H : Subgroup (K ≃ₐ[k] K)) ≃ₜ*
      ((IntermediateField.fixedField (H : Subgroup (K ≃ₐ[k] K))) ≃ₐ[k]
       (IntermediateField.fixedField (H : Subgroup (K ≃ₐ[k] K))))) := by
  haveI hGalois : IsGalois k (IntermediateField.fixedField (H : Subgroup (K ≃ₐ[k] K))) := by
    rw [← InfiniteGalois.normal_iff_isGalois,
        InfiniteGalois.fixingSubgroup_fixedField]; infer_instance
  haveI : IsClosed (H.1 : Set (K ≃ₐ[k] K)) := H.isClosed'
  let e := InfiniteGalois.normalAutEquivQuotient H
  have hfwd : Continuous e := by
    have hqm : Topology.IsQuotientMap
        (QuotientGroup.mk : (K ≃ₐ[k] K) → (K ≃ₐ[k] K) ⧸ H.1) :=
      isQuotientMap_quotient_mk'
    rw [hqm.continuous_iff]
    show Continuous (e ∘ QuotientGroup.mk)
    have : e ∘ (QuotientGroup.mk : (K ≃ₐ[k] K) → (K ≃ₐ[k] K) ⧸ H.1) =
        AlgEquiv.restrictNormalHom (IntermediateField.fixedField H.1) := by
      funext σ
      simp only [Function.comp_apply]
      exact InfiniteGalois.normalAutEquivQuotient_apply H σ
    rw [this]
    exact InfiniteGalois.restrictNormalHom_continuous _
  have hinv : Continuous e.symm :=
    Continuous.continuous_symm_of_equiv_compact_to_t2 hfwd
  exact ⟨{ toMulEquiv := e, continuous_toFun := hfwd, continuous_invFun := hinv }⟩

@[deprecated (since := "2025-05-04")] alias theorem_26_24_normal_quotient_iso := quotient_continuousMulEquiv_fixedField

theorem isOpen_iff_finiteDimensional [IsGalois k K]
    (L : IntermediateField k K) :
    IsOpen (L.fixingSubgroup : Set (K ≃ₐ[k] K)) ↔ FiniteDimensional k L :=
  InfiniteGalois.isOpen_iff_finite L

theorem normal_iff_isGalois [IsGalois k K]
    (L : IntermediateField k K) :
    L.fixingSubgroup.Normal ↔ IsGalois k L :=
  InfiniteGalois.normal_iff_isGalois L

theorem closure_eq_fixingSubgroup [IsGalois k K]
    (H : Subgroup (K ≃ₐ[k] K)) :
    H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup := by

  have h_ff_eq : IntermediateField.fixedField H.topologicalClosure =
      IntermediateField.fixedField H := by
    apply le_antisymm
    ·
      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      exact fun f hf => hx f (Subgroup.le_topologicalClosure H hf)
    ·

      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      intro σ hσ
      have hclosed : IsClosed {τ : K ≃ₐ[k] K | τ x = x} := by
        haveI : FiniteDimensional k (IntermediateField.adjoin k ({x} : Set K)) :=
          IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
        have hcl := Subgroup.isClosed_of_isOpen
          (IntermediateField.adjoin k ({x} : Set K)).fixingSubgroup
          (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin k ({x} : Set K)))
        suffices {τ : K ≃ₐ[k] K | τ x = x} =
            ((IntermediateField.adjoin k ({x} : Set K)).fixingSubgroup :
              Set (K ≃ₐ[k] K)) by
          rw [this]; exact hcl
        ext τ
        simp only [Set.mem_setOf_eq, SetLike.mem_coe,
          IntermediateField.mem_fixingSubgroup_iff]
        constructor
        · intro hτ y hy
          refine IntermediateField.adjoin_induction k
            (p := fun z _ => τ z = z) ?_ ?_ ?_ ?_ ?_ hy
          · intro z hz
            simp only [Set.mem_singleton_iff] at hz
            rw [hz, hτ]
          · intro c; exact τ.commutes c
          · intro a b _ _ ha hb; rw [map_add, ha, hb]
          · intro a _ ha; rw [map_inv₀, ha]
          · intro a b _ _ ha hb; rw [map_mul, ha, hb]
        · intro hτ
          exact hτ x (IntermediateField.subset_adjoin k _ (Set.mem_singleton x))
      exact closure_minimal (fun τ hτ => hx τ hτ) hclosed (hσ : σ ∈ closure (H : Set _))

  have hcl := H.isClosed_topologicalClosure
  let Hbar : ClosedSubgroup (K ≃ₐ[k] K) := ⟨H.topologicalClosure, hcl⟩

  have ftigt := InfiniteGalois.fixingSubgroup_fixedField Hbar

  show H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup
  rw [← h_ff_eq]
  exact ftigt.symm

noncomputable def absoluteGaloisGroup_profinite_iso
    (K₀ : Type*) [Field K₀] [CharZero K₀] :
    (AlgebraicClosure K₀ ≃ₐ[K₀] AlgebraicClosure K₀) ≃ₜ*
      (ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K₀
          (AlgebraicClosure K₀))).toProfinite.toTop :=
  InfiniteGalois.continuousMulEquivToLimit K₀ (AlgebraicClosure K₀)

theorem absoluteGaloisGroup_isProfiniteGroup
    (K₀ : Type) [Field K₀] [CharZero K₀] :
    IsProfiniteGroup (AlgebraicClosure K₀ ≃ₐ[K₀] AlgebraicClosure K₀) :=
  compact_totally_disconnected_is_profinite _


end InfiniteGalois

end Ideles
