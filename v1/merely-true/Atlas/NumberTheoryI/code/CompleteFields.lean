/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Over
import Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues

noncomputable section

open scoped Topology
open UniformSpace

def Converges {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) : Prop :=
  ∃ x : X, Filter.Tendsto u Filter.atTop (nhds x)

abbrev IsCompleteSpace (X : Type*) [UniformSpace X] : Prop :=
  CompleteSpace X

abbrev IsTopologicalAddGroupDef (G : Type*) [AddGroup G] [TopologicalSpace G] :=
  IsTopologicalAddGroup G

abbrev MetricCompletion (X : Type*) [UniformSpace X] := Completion X

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
set_option linter.unusedVariables false in
theorem completion_universal_property
    (K : Type*) [Field K] (v : AbsoluteValue K ℝ)
    (L : Type*) [Field L] [UniformSpace L] [CompleteSpace L] [T0Space L]
    [IsTopologicalRing L] [IsUniformAddGroup L]
    (f : WithAbs v →+* L) (hf : Continuous f) (hf_inj : Function.Injective f) :
    ∃ g : Completion (WithAbs v) →+* L,
      Continuous g ∧ (∀ x : WithAbs v, g x = f x) ∧
      (∀ g' : Completion (WithAbs v) →+* L,
        Continuous g' → (∀ x : WithAbs v, g' x = f x) →
        (g' : Completion (WithAbs v) → L) = (g : Completion (WithAbs v) → L)) := by


  clear hf_inj
  refine ⟨Completion.extensionHom f hf,
    Completion.continuous_extension,
    fun x => Completion.extensionHom_coe f hf x,
    fun g' hg'_cont hg'_coe => ?_⟩
  have hf_uc : UniformContinuous f :=
    uniformContinuous_addMonoidHom_of_continuous (show Continuous (f : WithAbs v →+ L) from hf)
  have h1 : Completion.extension (⇑f) = (⇑g') :=
    Completion.extension_unique hf_uc
      (uniformContinuous_addMonoidHom_of_continuous
        (show Continuous (g' : Completion (WithAbs v) →+ L) from hg'_cont))
      fun a => (hg'_coe a).symm
  have h2 : Completion.extension (⇑f) = ⇑(Completion.extensionHom f hf) :=
    Completion.extension_unique hf_uc
      (uniformContinuous_addMonoidHom_of_continuous
        (show Continuous (Completion.extensionHom f hf : Completion (WithAbs v) →+ L)
          from Completion.continuous_extension))
      fun a => (Completion.extensionHom_coe f hf a).symm
  rw [← h2, h1]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

theorem weak_approximation_theorem
    {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → AbsoluteValue K ℝ)
    (hv_nontrivial : ∀ i, (v i).IsNontrivial)
    (hv_ineq : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j))
    (a : ι → K) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ x : K, ∀ i, v i (x - a i) < ε i := by
  classical
  open Filter Topology Finset in
  have hpw : Pairwise fun i j => ¬(v i).IsEquiv (v j) := fun i j hij => hv_ineq i j hij
  choose xl hxl using
    AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hv_nontrivial hpw
  let y : ℕ → K := fun n => ∑ i, a i * (1 / (1 + (xl i)⁻¹ ^ n))
  suffices ∀ j, ∃ N, ∀ n, N ≤ n → (v j) (y n - a j) < ε j by
    choose N hN using this
    exact ⟨y (Finset.univ.sup N), fun j => hN j _ (Finset.le_sup (Finset.mem_univ j))⟩
  intro j
  have hconv : Tendsto (fun n => (WithAbs.equiv (v j)).symm (y n)) atTop
      (nhds ((WithAbs.equiv (v j)).symm (a j))) := by
    simp only [y, map_sum, map_mul]
    conv_rhs => rw [show (WithAbs.equiv (v j)).symm (a j) =
      ∑ i : ι, if i = j then (WithAbs.equiv (v j)).symm (a i) else 0 from by simp]
    apply tendsto_finset_sum
    intro i _
    by_cases hi : i = j
    · simp only [hi, ite_true]
      have hinv : (v j) (xl j)⁻¹ < 1 := by
        rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ (hxl j).1
      have h := (WithAbs.tendsto_one_div_one_add_pow_nhds_one hinv).const_mul
        ((WithAbs.equiv (v j)).symm (a j))
      rwa [show (WithAbs.equiv (v j)).symm (a j) * (1 : WithAbs (v j)) =
        (WithAbs.equiv (v j)).symm (a j) from mul_one _] at h
    · simp only [hi, ite_false]
      have hxl_ne : xl i ≠ 0 := by
        intro h; have := (hxl i).1; simp [h] at this; linarith
      have hinv : 1 < (v j) (xl i)⁻¹ := by
        rw [map_inv₀, one_lt_inv₀ ((v j).pos hxl_ne)]
        exact (hxl i).2 j (Ne.symm hi)
      have htend_real := (v j).tendsto_div_one_add_pow_nhds_zero hinv
      simp_rw [← WithAbs.norm_toAbs_eq] at htend_real
      have htend_zero := tendsto_zero_iff_norm_tendsto_zero.mpr htend_real
      have h := htend_zero.const_mul ((WithAbs.equiv (v j)).symm (a i))
      rwa [show (WithAbs.equiv (v j)).symm (a i) * (0 : WithAbs (v j)) =
        (0 : WithAbs (v j)) from mul_zero _] at h
  have hconv_norm : Tendsto (fun n => (v j) (y n - a j)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε' hε'
    obtain ⟨N, hN⟩ := hconv ε' hε'
    exact ⟨N, fun n hn => by
      specialize hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((v j).nonneg _)]
      rw [dist_eq_norm, show (WithAbs.equiv (v j)).symm (y n) - (WithAbs.equiv (v j)).symm (a j) =
        (WithAbs.equiv (v j)).symm (y n - a j) from by simp [map_sub]] at hN
      rw [WithAbs.norm_toAbs_eq] at hN
      exact hN⟩
  exact (Metric.tendsto_atTop.1 hconv_norm (ε j) (hε j)).imp fun N hN =>
    fun n hn => by
      specialize hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((v j).nonneg _)] at hN
      exact hN

@[reducible]
def AbsoluteValue.inducedTopology {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    TopologicalSpace K :=
  letI : NormedRing (WithAbs v) := WithAbs.normedRing v
  TopologicalSpace.induced (WithAbs.toAbs v) inferInstance

theorem absoluteValue_same_topology_iff_equiv
    {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) :
    v.inducedTopology = w.inducedTopology ↔ v.IsEquiv w := by

  have hcomp : (WithAbs.toAbs w : K → WithAbs w) =
      (WithAbs.congr v w (.refl K)) ∘ (WithAbs.toAbs v) := rfl
  simp only [AbsoluteValue.inducedTopology]
  rw [hcomp, ← induced_compose]

  have he_symm : ⇑(WithAbs.equiv v).toEquiv.symm = WithAbs.toAbs v := rfl
  rw [← he_symm]
  set e := (WithAbs.equiv v).toEquiv

  have cancel : ∀ t : TopologicalSpace (WithAbs v),
      TopologicalSpace.coinduced (⇑e.symm) (TopologicalSpace.induced (⇑e.symm) t) = t := by
    intro t
    rw [Equiv.induced_symm, coinduced_compose]
    have : (⇑e.symm) ∘ (⇑e) = id := funext (fun x => e.symm_apply_apply x)
    rw [this, coinduced_id]
  constructor
  ·
    intro h

    have heq : (inferInstance : TopologicalSpace (WithAbs v)) =
        TopologicalSpace.induced (⇑(WithAbs.congr v w (.refl K))) inferInstance := by
      have h1 := cancel (inferInstance : TopologicalSpace (WithAbs v))
      have h2 := cancel (TopologicalSpace.induced (⇑(WithAbs.congr v w (.refl K)))
        (inferInstance : TopologicalSpace (WithAbs w)))
      rw [h] at h1; rw [← h1, h2]

    rw [AbsoluteValue.isEquiv_iff_isHomeomorph, isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨⟨⟨heq⟩, (RingEquiv.bijective _).1⟩, (RingEquiv.bijective _).2⟩
  ·
    intro h
    rw [AbsoluteValue.isEquiv_iff_isHomeomorph] at h
    exact congrArg _ h.isInducing.eq_induced

open IsDedekindDomain

def DiscreteValuation.ExtendsWithIndex
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L (WithZero (Multiplicative ℤ)))
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ x : K, w (algebraMap K L x) = (v x) ^ e

set_option maxHeartbeats 800000 in
lemma intValuation_algebraMap_eq
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
    (P : HeightOneSpectrum R) (Q : HeightOneSpectrum S) [Q.asIdeal.LiesOver P.asIdeal]
    (r : R) :
    Q.intValuation (algebraMap R S r) =
      (P.intValuation r) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
  classical
  by_cases hr : r = 0
  · subst hr
    simp only [map_zero]
    have he : Ideal.ramificationIdx P.asIdeal Q.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal P.ne_bot
    exact (zero_pow he).symm
  have hsr : algebraMap R S r ≠ 0 := by
    intro h
    exact hr (FaithfulSMul.algebraMap_injective R S (h.trans (map_zero _).symm))
  rw [Q.intValuation_if_neg hsr, P.intValuation_if_neg hr]
  rw [show Ideal.span {algebraMap R S r} = Ideal.map (algebraMap R S) (Ideal.span {r}) from
    by rw [Ideal.map_span, Set.image_singleton]]
  have hspan_ne : (Ideal.span {r} : Ideal R) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  have hmap_ne : Ideal.map (algebraMap R S) (Ideal.span {r}) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot]
    exact Ideal.map_ne_bot_of_ne_bot (by rwa [ne_eq, Ideal.span_singleton_eq_bot])
  rw [count_associates_factors_eq hmap_ne Q.isPrime Q.ne_bot,
      count_associates_factors_eq hspan_ne P.isPrime P.ne_bot]
  have hPirr : Irreducible P.asIdeal := P.irreducible
  have hQirr : Irreducible Q.asIdeal := Q.irreducible
  set n := Multiset.count P.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {r}))
  set e := Ideal.ramificationIdx P.asIdeal Q.asIdeal
  have hcount : Multiset.count Q.asIdeal (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.map (algebraMap R S) (Ideal.span {r}))) = e * n := by
    have h1 : emultiplicity Q.asIdeal (Ideal.map (algebraMap R S) (Ideal.span {r})) =
        ↑e * emultiplicity P.asIdeal (Ideal.span {r}) :=
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
        (by rwa [ne_eq, ← Ideal.zero_eq_bot]) hPirr hQirr Q.ne_bot
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hQirr
          (by rwa [ne_eq, ← Ideal.zero_eq_bot] :
            Ideal.map (algebraMap R S) (Ideal.span {r}) ≠ ⊥),
        normalize_eq] at h1
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPirr
          (by rwa [ne_eq, ← Ideal.zero_eq_bot] : (Ideal.span {r} : Ideal R) ≠ ⊥),
        normalize_eq] at h1
    exact_mod_cast h1
  rw [hcount]
  rw [WithZero.exp, WithZero.exp, ← zpow_natCast, ← WithZero.coe_zpow, WithZero.coe_inj,
      ← ofAdd_zsmul]
  congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
theorem valuation_extends_with_ramificationIdx
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    (P : HeightOneSpectrum R) (Q : HeightOneSpectrum S) [Q.asIdeal.LiesOver P.asIdeal]
    (x : K) :
    Q.valuation L (algebraMap K L x) =
      (P.valuation K x) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  simp only
  rw [P.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, Valuation.map_div]
  have ha' : algebraMap K L (algebraMap R K a) = algebraMap R L a :=
    (IsScalarTower.algebraMap_apply R K L a).symm
  have hb' : algebraMap K L (algebraMap R K b) = algebraMap R L b :=
    (IsScalarTower.algebraMap_apply R K L b).symm
  rw [ha', hb']
  rw [show algebraMap R L a = algebraMap S L (algebraMap R S a) from
        IsScalarTower.algebraMap_apply R S L a,
      show algebraMap R L b = algebraMap S L (algebraMap R S b) from
        IsScalarTower.algebraMap_apply R S L b]
  rw [Q.valuation_of_algebraMap, Q.valuation_of_algebraMap]
  rw [intValuation_algebraMap_eq P Q, intValuation_algebraMap_eq P Q]
  show (P.intValuation a) ^ _ / (P.intValuation b) ^ _ = _
  rw [div_pow]

end
