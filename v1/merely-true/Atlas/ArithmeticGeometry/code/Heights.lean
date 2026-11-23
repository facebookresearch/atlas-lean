/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.GaloisPlaceHelper

noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

def absoluteHeight (P : Projectivization K (ι → K)) : ℝ :=
  Projectivization.mulHeight P

lemma absoluteHeight_mk {x : ι → K} (hx : x ≠ 0) :
    absoluteHeight (Projectivization.mk K x hx) = Height.mulHeight x := by
  simp [absoluteHeight, Projectivization.mulHeight_mk]


def logHeight (P : Projectivization K (ι → K)) : ℝ :=
  Real.log (absoluteHeight P)

lemma logHeight_eq (P : Projectivization K (ι → K)) :
    logHeight P = Projectivization.logHeight P := by
  simp [logHeight, absoluteHeight, Projectivization.logHeight_eq_log_mulHeight]


end AbsoluteHeight

section HeightProperties

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

theorem weil_height_ge_one (x : Fin (n + 1) → K) :
    1 ≤ mulHeight x :=
  one_le_mulHeight x


end HeightProperties

section Morphism

variable {K : Type*} [Field K] [NumberField K]
variable {n m d : ℕ}


theorem height_morphism_upper_bound
    {φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K}
    (hφ : ∀ i, (φ i).IsHomogeneous d) :
    ∃ (c : ℝ), ∀ (x : Fin (n + 1) → K),
      logHeight (fun j => MvPolynomial.eval x (φ j)) ≤ (d : ℝ) * logHeight x + c := by


  obtain ⟨C, hC⟩ := logHeight_eval_le' hφ
  exact ⟨C, fun x => by linarith [hC x]⟩

end Morphism

section Automorphism

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

theorem height_automorphism_bound
    {φ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K}
    {ψ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K}
    (hφ : ∀ i, (φ i).IsHomogeneous 1)
    (hψ : ∀ i, (ψ i).IsHomogeneous 1)
    (hinv : ∀ (x : Fin (n + 1) → K) (i : Fin (n + 1)),
      MvPolynomial.eval (fun j => MvPolynomial.eval x (φ j)) (ψ i) = x i) :
    ∃ (c : ℝ), ∀ (x : Fin (n + 1) → K),
      |logHeight (fun j => MvPolynomial.eval x (φ j)) - logHeight x| ≤ c := by

  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' hφ

  obtain ⟨C₂, hC₂⟩ := logHeight_eval_le' hψ
  refine ⟨max C₁ C₂, fun x => ?_⟩
  rw [abs_le]
  have hC₁x := hC₁ x
  have hC₂x := hC₂ (fun j => MvPolynomial.eval x (φ j))

  have heq : (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval x (φ j)) (ψ i)) = x := by
    ext i; exact hinv x i
  rw [heq] at hC₂x

  simp only [Nat.cast_one, one_mul] at hC₁x hC₂x
  constructor <;> linarith [le_max_left C₁ C₂, le_max_right C₁ C₂]

end Automorphism

end

theorem NumberField.FinitePlace.isFinitePlace_comp_galois {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) (v : NumberField.FinitePlace K) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      place (NumberField.FinitePlace.embedding w) =
        v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective := by
  let p := v.maximalIdeal
  let e : (NumberField.RingOfIntegers K) ≃+* (NumberField.RingOfIntegers K) :=
    NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let w := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p

  have habsN : Ideal.absNorm w.asIdeal = Ideal.absNorm p.asIdeal := by
    have hasideal : w.asIdeal =
        Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal := by
      show (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = _
      rw [IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_apply,
          IsDedekindDomain.HeightOneSpectrum.comap_asIdeal]
    rw [hasideal, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot]
    have h : p.asIdeal =
        (Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal).map
          (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) :=
      (Ideal.map_comap_of_surjective
        (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        e.symm.surjective p.asIdeal).symm
    exact Nat.card_congr (Ideal.quotientEquiv _ p.asIdeal e.symm h).toEquiv
  use w
  apply AbsoluteValue.ext; intro x
  show ‖NumberField.FinitePlace.embedding w x‖ = v.val (σ.symm x)
  have hv : v = NumberField.FinitePlace.mk p :=
    (NumberField.FinitePlace.mk_maximalIdeal v).symm
  conv_rhs => rw [hv]
  show ‖NumberField.FinitePlace.embedding w x‖ =
    ‖NumberField.FinitePlace.embedding p (σ.symm x)‖
  rw [NumberField.FinitePlace.norm_embedding', NumberField.FinitePlace.norm_embedding']

  have hval : w.valuation K x = p.valuation K (σ.symm x) := by
    obtain ⟨a, b, hb, rfl⟩ :=
      IsFractionRing.div_surjective (NumberField.RingOfIntegers K) x
    simp only [map_div₀]
    congr 1 <;> {
      rw [show σ.symm (algebraMap (NumberField.RingOfIntegers K) K _) =
            algebraMap (NumberField.RingOfIntegers K) K (e.symm _) from by
        change σ.symm (_ : K) =
          ((NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm _ : K)
        rw [NumberField.RingOfIntegers.mapRingEquiv_symm_apply]; rfl,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (intValuation_equivOfRingEquiv e p _).symm }
  rw [hval]
  simp only [habsN]

noncomputable def galoisEquivFinitePlace {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) : NumberField.FinitePlace K ≃ NumberField.FinitePlace K where
  toFun v := ⟨v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective,
    NumberField.FinitePlace.isFinitePlace_comp_galois σ v⟩
  invFun v := ⟨v.val.comp (f := (σ : K →+* K)) σ.injective, by
    have h := NumberField.FinitePlace.isFinitePlace_comp_galois σ⁻¹ v
    simp only [show (σ⁻¹ : K ≃ₐ[ℚ] K) = σ.symm from by ext; rfl,
      AlgEquiv.symm_symm] at h
    exact h⟩
  left_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ.symm (σ x)) = v x
    rw [AlgEquiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]

theorem galoisEquivFinitePlace_apply {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) (v : NumberField.FinitePlace K) (y : K) :
    (galoisEquivFinitePlace σ v) y = v (σ.symm y) := rfl

noncomputable section

open Height NumberField

section GaloisInvariance

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Finite ι]

omit [Finite ι] in
lemma prod_infinitePlace_galois_eq (σ : K ≃ₐ[ℚ] K) (x : ι → K) :
    ∏ v : InfinitePlace K, (⨆ i, v (σ (x i))) ^ v.mult =
    ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
  apply Fintype.prod_equiv (MulAction.toPerm σ⁻¹)
  intro v
  simp only [MulAction.toPerm_apply]
  have hval : ∀ i, v (σ (x i)) = (σ⁻¹ • v) (x i) := by
    intro i; rw [InfinitePlace.smul_apply]; congr 1
  simp_rw [hval]
  congr 1
  unfold InfinitePlace.mult
  rw [InfinitePlace.isReal_smul_iff]

omit [Finite ι] in
lemma finprod_finitePlace_galois_eq (σ : K ≃ₐ[ℚ] K) (x : ι → K) :
    ∏ᶠ v : FinitePlace K, ⨆ i, v (σ (x i)) =
    ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp_rw [show ∀ (v : FinitePlace K) (i : ι), v (σ (x i)) =
      (galoisEquivFinitePlace σ⁻¹ v) (x i)
    from fun v i => by rw [galoisEquivFinitePlace_apply]; congr 1]
  exact finprod_comp_equiv (galoisEquivFinitePlace σ⁻¹) (f := fun v => ⨆ i, v (x i))

omit [Finite ι] in
theorem mulHeight_galois_invariant (σ : K ≃ₐ[ℚ] K) (x : ι → K) :
    mulHeight (σ ∘ x) = mulHeight x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hσx : σ ∘ x ≠ 0 := by
      intro h; apply hx; funext i
      have := congr_fun h i
      simp [Function.comp] at this
      exact this
    rw [NumberField.mulHeight_eq hσx, NumberField.mulHeight_eq hx]
    simp only [Function.comp_apply]
    exact congr_arg₂ (· * ·)
      (prod_infinitePlace_galois_eq σ x) (finprod_finitePlace_galois_eq σ x)

omit [Finite ι] in
theorem logHeight_galois_invariant (σ : K ≃ₐ[ℚ] K) (x : ι → K) :
    logHeight (σ ∘ x) = logHeight x := by
  simp only [logHeight, mulHeight_galois_invariant σ x]

end GaloisInvariance

end

open WeierstrassCurve AddSubgroup

namespace EllipticCurve.WeakMordellWeil

structure TwoIsogenyData (W : WeierstrassCurve ℚ) [W.IsElliptic] where
  E'Points : Type
  instAddCommGroup : AddCommGroup E'Points
  phi : W.toAffine.Point →+ E'Points
  phi_hat : E'Points →+ W.toAffine.Point
  comp_eq : phi_hat.comp phi = zsmulAddGroupHom (2 : ℤ)
  descentTarget : Type
  instDescentTargetGroup : AddCommGroup descentTarget
  descentMap : E'Points →+ descentTarget
  descentMap_range_finite : Finite descentMap.range
  descentMap_ker_eq : descentMap.ker = phi.range
  descentTarget' : Type
  instDescentTarget'Group : AddCommGroup descentTarget'
  descentMap' : W.toAffine.Point →+ descentTarget'
  descentMap'_range_finite : Finite descentMap'.range
  descentMap'_ker_eq : descentMap'.ker = phi_hat.range
  phi_hat_ker_le_phi_range : phi_hat.ker ≤ phi.range

attribute [instance] TwoIsogenyData.instAddCommGroup
attribute [instance] TwoIsogenyData.instDescentTargetGroup
attribute [instance] TwoIsogenyData.instDescentTarget'Group
attribute [instance] TwoIsogenyData.descentMap_range_finite
attribute [instance] TwoIsogenyData.descentMap'_range_finite

def IsNonzeroSquare (q : ℚ) : Prop := ∃ r : ℚ, r ≠ 0 ∧ q = r ^ 2


theorem lemma_25_3_phi {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (data : TwoIsogenyData W) : data.descentMap.ker = data.phi.range :=
  data.descentMap_ker_eq

theorem lemma_25_3_phi_hat {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (data : TwoIsogenyData W) : data.descentMap'.ker = data.phi_hat.range :=
  data.descentMap'_ker_eq


def E'Curve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := -2 * a; a₃ := 0; a₄ := a ^ 2 - 4 * b; a₆ := 0

noncomputable def descentMapRaw (a b : ℚ) (hdisc : a ^ 2 - 4 * b ≠ 0) :
    (E'Curve a b).toAffine.Point → Additive (ℚˣ ⧸ Subgroup.square ℚˣ) :=
  fun P => match P with
  | .zero => Additive.ofMul 1
  | .some x _y _hxy =>
    if hx : x = 0 then
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (a ^ 2 - 4 * b) hdisc))
    else
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 x hx))

lemma square_class_self_add (g : ℚˣ ⧸ Subgroup.square ℚˣ) :
    Additive.ofMul g + Additive.ofMul g = 0 := by
  rw [← ofMul_mul, ofMul_eq_zero]
  induction g using Quotient.inductionOn' with
  | h g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩


lemma square_class_mk_mul (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x * y) (mul_ne_zero hx hy)) =
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 x hx) *
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 y hy) := by
  rw [← map_mul]; congr 1; ext; simp [Units.mk0]

lemma square_class_mul_eq_div (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x * y) (mul_ne_zero hx hy)) =
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x / y) (div_ne_zero hx hy)) := by
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square, isSquare_iff_exists_sq]
  refine ⟨Units.mk0 (y⁻¹) (inv_ne_zero hy), ?_⟩
  ext
  show ((Units.mk0 (x * y) _)⁻¹ * (Units.mk0 (x / y) _)).val = ((Units.mk0 (y⁻¹) _) ^ 2).val
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, sq]; field_simp







lemma sq_class_of_rat_unit (u : ℚˣ) :
    QuotientGroup.mk' (Subgroup.square ℚˣ) u =
    QuotientGroup.mk' (Subgroup.square ℚˣ)
      (Units.mk0 (↑((u : ℚ).num * ↑(u : ℚ).den) : ℚ)
        (by
          push_cast
          exact_mod_cast mul_ne_zero (Rat.num_ne_zero.mpr (Units.ne_zero u))
            (Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (u : ℚ).pos)))) := by
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square]
  have hden_ne : ((u : ℚ).den : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (u : ℚ).pos)
  refine ⟨Units.mk0 ((u : ℚ).den : ℚ) hden_ne, Units.ext ?_⟩
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [inv_mul_eq_div, div_eq_iff (Units.ne_zero u)]
  have key : (u : ℚ) * ((u : ℚ).den : ℚ) = ((u : ℚ).num : ℚ) := by
    have := Rat.num_div_den (u : ℚ)
    field_simp at this ⊢; linarith
  have cast_eq : (((u : ℚ).num * ((u : ℚ).den : ℤ) : ℤ) : ℚ) =
      ((u : ℚ).num : ℚ) * ((u : ℚ).den : ℚ) := by push_cast; ring
  rw [cast_eq, ← key]
  ring


lemma int_sq_mul_squarefree (n : ℤ) (hn : n ≠ 0) :
    ∃ r s : ℤ, n = r * s ^ 2 ∧ Squarefree r ∧ r ≠ 0 ∧ s ≠ 0 := by
  have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n.natAbs
  have ha_ne : a ≠ 0 := by intro h; subst h; simp at hab; exact hn' hab.symm
  have hb_ne : b ≠ 0 := by intro h; subst h; simp at hab; exact hn' hab.symm
  by_cases hn_pos : 0 ≤ n
  · exact ⟨(a : ℤ), (b : ℤ),
      by rw [← Int.natAbs_of_nonneg hn_pos, ← hab]; push_cast; ring,
      Int.squarefree_natCast.mpr ha,
      Int.natCast_ne_zero.mpr ha_ne,
      Int.natCast_ne_zero.mpr hb_ne⟩
  · push Not at hn_pos
    exact ⟨-(a : ℤ), (b : ℤ),
      by linarith [Int.ofNat_natAbs_of_nonpos (le_of_lt hn_pos),
        show (n.natAbs : ℤ) = (b : ℤ) ^ 2 * (a : ℤ) from by rw [← hab]; push_cast; ring],
      by rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs];
         exact Int.squarefree_natCast.mpr ha,
      neg_ne_zero.mpr (Int.natCast_ne_zero.mpr ha_ne),
      Int.natCast_ne_zero.mpr hb_ne⟩

lemma sq_class_of_sq_factor (n r s : ℤ) (hn : n ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (heq : n = r * s ^ 2) :
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)) =
    QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (r : ℚ) (Int.cast_ne_zero.mpr hr)) := by
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square]
  refine ⟨(Units.mk0 (s : ℚ) (Int.cast_ne_zero.mpr hs))⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hr' : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  field_simp
  push_cast [heq]
  ring






theorem corollary_25_6 (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (data : TwoIsogenyData W) :
    data.phi.range.FiniteIndex ∧ data.phi_hat.range.FiniteIndex := by
  constructor
  ·

    rw [← lemma_25_3_phi data]
    exact AddSubgroup.finiteIndex_ker data.descentMap
  ·
    rw [← lemma_25_3_phi_hat data]
    exact AddSubgroup.finiteIndex_ker data.descentMap'

theorem corollary_25_7_index (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (data : TwoIsogenyData W) :
    (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range.index =
      data.phi.range.index * data.phi_hat.range.index := by
  rw [← data.comp_eq, AddMonoidHom.range_comp, AddSubgroup.index_map,
    sup_eq_left.mpr data.phi_hat_ker_le_phi_range]

theorem corollary_25_7 (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (data : TwoIsogenyData W) :
    (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range.FiniteIndex := by
  obtain ⟨hphi, hphi_hat⟩ := corollary_25_6 W data
  rw [AddSubgroup.finiteIndex_iff, corollary_25_7_index W data]
  exact mul_ne_zero hphi.index_ne_zero hphi_hat.index_ne_zero

theorem corollary_25_7' (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (data : TwoIsogenyData W) :
    Finite (W.toAffine.Point ⧸
      (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range) := by
  haveI := corollary_25_7 W data
  infer_instance

end EllipticCurve.WeakMordellWeil

noncomputable section

open Filter Topology

namespace CanonicalHeight

variable {E : Type*} [AddCommGroup E]

def canonicalHeightSeq (h : E → ℝ) (P : E) (n : ℕ) : ℝ :=
  h ((2 ^ n : ℤ) • P) / (4 : ℝ) ^ n

def canonicalHeight (h : E → ℝ) (P : E) : ℝ :=
  limUnder atTop (canonicalHeightSeq h P)


lemma canonicalHeightSeq_double (h : E → ℝ) (P : E) (n : ℕ) :
    canonicalHeightSeq h ((2 : ℤ) • P) n = 4 * canonicalHeightSeq h P (n + 1) := by
  simp only [canonicalHeightSeq]
  have key : (2 ^ n : ℤ) • ((2 : ℤ) • P) = (2 ^ (n + 1) : ℤ) • P := by
    rw [smul_smul, pow_succ]
  rw [key, pow_succ]
  ring

theorem canonicalHeight_double (h : E → ℝ) (P : E)
    (hconv : Tendsto (canonicalHeightSeq h P) atTop (𝓝 (canonicalHeight h P))) :
    canonicalHeight h ((2 : ℤ) • P) = 4 * canonicalHeight h P := by

  have hseq : canonicalHeightSeq h ((2 : ℤ) • P) =
      fun n => 4 * canonicalHeightSeq h P (n + 1) :=
    funext (canonicalHeightSeq_double h P)

  have hshift : Tendsto (fun n => canonicalHeightSeq h P (n + 1)) atTop
      (𝓝 (canonicalHeight h P)) :=
    hconv.comp (tendsto_add_atTop_nat 1)

  have htend : Tendsto (canonicalHeightSeq h ((2 : ℤ) • P)) atTop
      (𝓝 (4 * canonicalHeight h P)) := by
    rw [hseq]; exact hshift.const_mul 4

  exact htend.limUnder_eq

end CanonicalHeight

section EllipticCurveCanonicalHeight

open CanonicalHeight

attribute [local instance] Classical.dec

variable {K : Type*} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

structure IsWeilHeightOnCurve (h : W.toAffine.Point → ℝ) : Prop where
  doubling_bound : ∃ C : ℝ, ∀ P : W.toAffine.Point,
    |h ((2 : ℤ) • P) - 4 * h P| ≤ C
  height_nonneg_zero : 0 ≤ h 0
  northcott : ∀ B : ℝ, {P : W.toAffine.Point | h P ≤ B}.Finite

def EllipticCurve.NeronTateHeight (h : W.toAffine.Point → ℝ)
    (_hWeil : IsWeilHeightOnCurve W h) (P : W.toAffine.Point) : ℝ :=
  canonicalHeight h P



end EllipticCurveCanonicalHeight

namespace TateTheorem

def tateSeq {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (x : S) (n : ℕ) : ℝ :=
  h (φ^[n] x) / r ^ n

@[simp]
lemma tateSeq_zero {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (x : S) :
    tateSeq φ h r x 0 = h x := by simp [tateSeq]

lemma tateSeq_dist {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) (x : S) (n : ℕ) :
    dist (tateSeq φ h r x n) (tateSeq φ h r x (n + 1)) ≤ C / r ^ (n + 1) := by
  rw [Real.dist_eq]
  have hr_pos : (0 : ℝ) < r := by linarith
  have hrn1_pos : (0 : ℝ) < r ^ (n + 1) := pow_pos hr_pos (n + 1)
  simp only [tateSeq, Function.iterate_succ', Function.comp_def]
  have key : h (φ^[n] x) / r ^ n - h (φ (φ^[n] x)) / r ^ (n + 1) =
      (r * h (φ^[n] x) - h (φ (φ^[n] x))) / r ^ (n + 1) := by
    rw [pow_succ']; field_simp
  rw [key, abs_div, abs_of_pos hrn1_pos, abs_sub_comm]
  exact div_le_div_of_nonneg_right (hbound (φ^[n] x)) hrn1_pos.le

lemma summable_tate_bound {r : ℝ} (hr : 1 < r) (C : ℝ) :
    Summable (fun n => C / r ^ (n + 1)) := by
  have hinv_nn : 0 ≤ r⁻¹ := by positivity
  have hinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have : (fun n => C / r ^ (n + 1)) = fun n => C / r * (r⁻¹) ^ n := by
    ext n; simp [pow_succ', div_mul_eq_mul_div]; ring
  rw [this]
  exact (summable_geometric_of_lt_one hinv_nn hinv).mul_left (C / r)

lemma tsum_tate_bound (r : ℝ) (hr : 1 < r) (C : ℝ) :
    ∑' (n : ℕ), C / r ^ (n + 1) = C / (r - 1) := by
  have hinv_nn : 0 ≤ r⁻¹ := by positivity
  have hinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have : (fun n => C / r ^ (n + 1)) = fun n => C / r * (r⁻¹) ^ n := by
    ext n; simp [pow_succ', div_mul_eq_mul_div]; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hinv_nn hinv]
  rw [show (1 : ℝ) - r⁻¹ = (r - 1) / r from by field_simp]
  field_simp

lemma tateSeq_cauchySeq {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) (x : S) :
    CauchySeq (tateSeq φ h r x) :=
  cauchySeq_of_dist_le_of_summable _ (tateSeq_dist φ h r hr C hbound x)
    (summable_tate_bound hr C)

lemma tateSeq_tendsto {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) (x : S) :
    Tendsto (tateSeq φ h r x) atTop (𝓝 (limUnder atTop (tateSeq φ h r x))) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (tateSeq_cauchySeq φ h r hr C hbound x)
  rwa [hL.limUnder_eq]

lemma tateSeq_comp {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (x : S) (n : ℕ) :
    tateSeq φ h r (φ x) n = r * tateSeq φ h r x (n + 1) := by
  simp only [tateSeq]
  rw [show φ^[n] (φ x) = φ^[n + 1] x from (Function.iterate_succ_apply φ n x).symm,
      pow_succ']
  field_simp

theorem tate_bound {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) (x : S) :
    |limUnder atTop (tateSeq φ h r x) - h x| ≤ C / (r - 1) := by
  have htend := tateSeq_tendsto φ h r hr C hbound x
  have hd := dist_le_tsum_of_dist_le_of_tendsto₀ _
    (tateSeq_dist φ h r hr C hbound x) (summable_tate_bound hr C) htend
  rw [tateSeq_zero, Real.dist_eq] at hd
  linarith [tsum_tate_bound r hr C,
    abs_sub_comm (h x) (limUnder atTop (tateSeq φ h r x))]

theorem tate_comp_eq {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) (x : S) :
    limUnder atTop (tateSeq φ h r (φ x)) =
      r * limUnder atTop (tateSeq φ h r x) := by
  have hseq : tateSeq φ h r (φ x) = fun n => r * tateSeq φ h r x (n + 1) :=
    funext (tateSeq_comp φ h r hr x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (tateSeq_cauchySeq φ h r hr C hbound x)
  have hshift : Tendsto (fun n => tateSeq φ h r x (n + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have htend_phi : Tendsto (tateSeq φ h r (φ x)) atTop (𝓝 (r * L)) := by
    rw [hseq]; exact hshift.const_mul r
  rw [htend_phi.limUnder_eq, hL.limUnder_eq]

lemma iterate_eq_of_comp {S : Type*} (φ : S → S) (f : S → ℝ) (r : ℝ)
    (hf_comp : ∀ x, f (φ x) = r * f x) (x : S) (n : ℕ) :
    f (φ^[n] x) = r ^ n * f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_def, hf_comp, ih]; ring

lemma tateSeq_const_of_comp {S : Type*} (φ : S → S) (f : S → ℝ) (r : ℝ) (hr : 1 < r)
    (hf_comp : ∀ x, f (φ x) = r * f x) (x : S) (n : ℕ) :
    tateSeq φ f r x n = f x := by
  simp only [tateSeq, iterate_eq_of_comp φ f r hf_comp x n]
  exact mul_div_cancel_left₀ _
    (pow_ne_zero n (ne_of_gt (show (0 : ℝ) < r by linarith)))

lemma tendsto_div_pow_zero (r : ℝ) (hr : 1 < r) (D : ℝ) :
    Tendsto (fun n : ℕ => D / r ^ n) atTop (𝓝 0) := by
  rw [show (fun n : ℕ => D / r ^ n) = fun n => D * (r⁻¹ ^ n) from by
    ext n; rw [div_eq_mul_inv, inv_pow]]
  rw [show (0 : ℝ) = D * 0 from (mul_zero D).symm]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ hr)).const_mul D

lemma tateSeq_diff_bound {S : Type*} (φ : S → S) (f h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (D : ℝ) (hD : ∀ x, |f x - h x| ≤ D) (x : S) (n : ℕ) :
    ‖tateSeq φ f r x n - tateSeq φ h r x n‖ ≤ D / r ^ n := by
  simp only [tateSeq, Real.norm_eq_abs, ← sub_div, abs_div,
    abs_of_pos (pow_pos (show (0 : ℝ) < r by linarith) n)]
  exact div_le_div_of_nonneg_right (hD (φ^[n] x))
    (pow_pos (show (0 : ℝ) < r by linarith) n).le

theorem tate_unique {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C)
    (f : S → ℝ) (D : ℝ) (hD : ∀ x, |f x - h x| ≤ D)
    (hf_comp : ∀ x, f (φ x) = r * f x) (x : S) :
    f x = limUnder atTop (tateSeq φ h r x) := by
  obtain ⟨Lh, hLh⟩ := cauchySeq_tendsto_of_complete
    (tateSeq_cauchySeq φ h r hr C hbound x)
  rw [hLh.limUnder_eq]
  have hdiff_zero : Tendsto (fun n => tateSeq φ f r x n - tateSeq φ h r x n)
      atTop (𝓝 0) :=
    squeeze_zero_norm (tateSeq_diff_bound φ f h r hr D hD x)
      (tendsto_div_pow_zero r hr D)
  have : (fun n => tateSeq φ f r x n - tateSeq φ h r x n) =
      (fun n => f x - tateSeq φ h r x n) := by
    ext n; rw [tateSeq_const_of_comp φ f r hr hf_comp x]
  rw [this] at hdiff_zero
  linarith [tendsto_nhds_unique (Tendsto.sub tendsto_const_nhds hLh) hdiff_zero]

theorem tate_theorem {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (hr : 1 < r)
    (C : ℝ) (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :

    (∀ x, ∃ L, Tendsto (tateSeq φ h r x) atTop (𝓝 L)) ∧

    (∀ x, |limUnder atTop (tateSeq φ h r x) - h x| ≤ C / (r - 1)) ∧

    (∀ x, limUnder atTop (tateSeq φ h r (φ x)) =
      r * limUnder atTop (tateSeq φ h r x)) ∧

    (∀ (f : S → ℝ) (D : ℝ), (∀ x, |f x - h x| ≤ D) →
      (∀ x, f (φ x) = r * f x) →
      ∀ x, f x = limUnder atTop (tateSeq φ h r x)) :=
  ⟨fun x => cauchySeq_tendsto_of_complete (tateSeq_cauchySeq φ h r hr C hbound x),
   fun x => tate_bound φ h r hr C hbound x,
   fun x => tate_comp_eq φ h r hr C hbound x,
   fun f D hD hf x => tate_unique φ h r hr C hbound f D hD hf x⟩

end TateTheorem

end

noncomputable section

open Height Polynomial Set

namespace Northcott

theorem finite_roots_of_bounded_mahler_degree (d : ℕ) (B : NNReal) :
    Set.Finite {α : ℂ | ∃ p : ℤ[X], p ≠ 0 ∧ p.natDegree ≤ d ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B ∧
      (p.map (Int.castRingHom ℂ)).IsRoot α} := by
  have hfin_polys := Polynomial.finite_mahlerMeasure_le d B
  have hfin_union : (⋃ p ∈ {p : ℤ[X] | p.natDegree ≤ d ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B},
      ((p.map (Int.castRingHom ℂ)).rootSet ℂ : Set ℂ)).Finite :=
    hfin_polys.biUnion (fun p _ => Polynomial.rootSet_finite _ ℂ)
  apply hfin_union.subset
  intro α hα
  obtain ⟨p, hp_ne, hp_deg, hp_mahler, hp_root⟩ := hα
  simp only [Set.mem_iUnion]
  refine ⟨p, ⟨hp_deg, hp_mahler⟩, ?_⟩
  rw [Polynomial.mem_rootSet]
  exact ⟨(Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hp_ne, hp_root⟩





theorem mulHeight₁_le_mulHeight_of_one_eq {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (x : Fin (n + 1) → K) (_hx : x ≠ 0) (i₀ : Fin (n + 1)) (hi₀ : x i₀ = 1)
    (j : Fin (n + 1)) : mulHeight₁ (x j) ≤ mulHeight x := by

  let f : Fin 2 → Fin (n + 1) := ![j, i₀]
  rw [mulHeight₁_eq_mulHeight, show (1 : K) = x i₀ from hi₀.symm]
  have hcomp : ![x j, x i₀] = x ∘ f := by
    ext i; fin_cases i <;> simp [f]
  rw [hcomp]
  exact mulHeight_comp_le f x


noncomputable def mapCoords {K L : Type*} [CommRing K] [CommRing L]
    (σ : K →+* L) (n : ℕ) :
    (Fin (n + 1) → K) →ₛₗ[σ] (Fin (n + 1) → L) where
  toFun v i := σ (v i)
  map_add' x y := by ext i; simp [map_add]
  map_smul' c x := by ext i; simp [RingHom.map_mul]

theorem mapCoords_injective {K L : Type*} [CommRing K] [CommRing L] {σ : K →+* L}
    (hσ : Function.Injective σ) (n : ℕ) : Function.Injective (mapCoords σ n) := by
  intro x y h; ext i; exact hσ (congr_fun h i)


end Northcott

end

noncomputable section

open AddSubgroup Set

theorem addGroup_fg_of_height_descent
    {G : Type*} [AddCommGroup G]
    (ĥ : G → ℝ)
    (hĥ_nonneg : ∀ P : G, 0 ≤ ĥ P)
    (hĥ_double : ∀ P : G, ĥ ((2 : ℤ) • P) = 4 * ĥ P)
    (hĥ_par : ∀ P Q : G, ĥ (P + Q) + ĥ (P - Q) = 2 * ĥ P + 2 * ĥ Q)
    (hquot : Finite (G ⧸ (zsmulAddGroupHom (2 : ℤ) : G →+ G).range))
    (hNorthcott : ∀ B : ℝ, {P : G | ĥ P ≤ B}.Finite)
    : AddGroup.FG G := by
  classical
  rw [AddGroup.fg_iff]
  set H := (zsmulAddGroupHom (2 : ℤ) : G →+ G).range
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _

  set reps : Finset G := Finset.univ.image (fun q : G ⧸ H => q.out)

  have hreps : ∀ Q : G, ∃ P ∈ reps, ∃ R : G, Q - P = (2 : ℤ) • R := by
    intro Q
    let q : G ⧸ H := QuotientAddGroup.mk Q
    refine ⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hrel : (QuotientAddGroup.leftRel H) q.out Q := Quotient.mk_out Q
    rw [QuotientAddGroup.leftRel_apply] at hrel
    obtain ⟨_, hm⟩ := hrel
    exact ⟨_, by rw [show Q - q.out = -q.out + Q from by abel]; exact hm.symm⟩
  have hreps_nonempty : reps.Nonempty :=
    ⟨(QuotientAddGroup.mk (0 : G) : G ⧸ H).out,
     Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩

  obtain ⟨Pmax, _, hPmax⟩ := Finset.exists_max_image reps ĥ hreps_nonempty
  set B := ĥ Pmax

  set S : Set G := {P | ĥ P ≤ B}
  have hS_fin : S.Finite := hNorthcott B
  have hreps_sub : ↑reps ⊆ S := fun P hP => hPmax P (by exact_mod_cast hP)

  suffices AddSubgroup.closure S = ⊤ from ⟨S, this, hS_fin⟩

  by_contra hne
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ ∉ (AddSubgroup.closure S : Set G) := by
    by_contra h; push Not at h; exact hne (eq_top_iff.mpr (fun x _ => h x))

  set bad : Set G := {Q | Q ∉ (AddSubgroup.closure S : Set G)} ∩ {Q | ĥ Q ≤ ĥ Q₀}
  have hbad_fin : bad.Finite := (hNorthcott (ĥ Q₀)).subset inter_subset_right
  have hbad_ne : bad.Nonempty := ⟨Q₀, hQ₀, Set.mem_setOf.mpr le_rfl⟩

  obtain ⟨Q, hQ_bad, hQ_min⟩ :=
    hbad_fin.toFinset.exists_min_image ĥ (by rwa [Set.Finite.toFinset_nonempty])
  rw [Set.Finite.mem_toFinset] at hQ_bad
  have hQ_not := hQ_bad.1
  have hQ_le₀ := hQ_bad.2

  have hQ_global_min : ∀ Q' : G, Q' ∉ (AddSubgroup.closure S : Set G) → ĥ Q ≤ ĥ Q' := by
    intro Q' hQ'
    by_cases h : ĥ Q' ≤ ĥ Q₀
    · exact hQ_min Q' (by rw [Set.Finite.mem_toFinset]; exact ⟨hQ', h⟩)
    · push Not at h; exact le_trans hQ_le₀ (le_of_lt h)

  obtain ⟨P, hP_mem, R, hQPR⟩ := hreps Q

  have hP_cl : P ∈ (AddSubgroup.closure S : Set G) :=
    AddSubgroup.subset_closure (hreps_sub hP_mem)

  have hR_not : R ∉ (AddSubgroup.closure S : Set G) := by
    intro hR
    exact hQ_not ((show Q = P + (2 : ℤ) • R from by rw [← hQPR]; abel) ▸
      (AddSubgroup.closure S).add_mem hP_cl ((AddSubgroup.closure S).zsmul_mem hR 2))

  have hR_ge : ĥ Q ≤ ĥ R := hQ_global_min R hR_not

  have hP_le : ĥ P ≤ B := hreps_sub hP_mem


  have hpar := hĥ_par Q P
  have hĥQP : ĥ (Q - P) = 4 * ĥ R := by rw [hQPR, hĥ_double]
  have : 2 * ĥ Q ≤ 2 * ĥ P := by
    have h1 : 4 * ĥ R ≤ 2 * ĥ Q + 2 * ĥ P := by
      calc 4 * ĥ R = ĥ (Q - P) := hĥQP.symm
        _ ≤ ĥ (Q + P) + ĥ (Q - P) := le_add_of_nonneg_left (hĥ_nonneg _)
        _ = 2 * ĥ Q + 2 * ĥ P := hpar
    linarith

  exact hQ_not (AddSubgroup.subset_closure (show ĥ Q ≤ B by linarith))

section Theorem_25_14

open Height MvPolynomial

def IsProjectiveMorphism {K : Type*} [CommRing K] {n m : ℕ} (d : ℕ)
    (φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  (∀ i, (φ i).IsHomogeneous d) ∧
  (∀ x : Fin (n + 1) → K, x ≠ 0 → ∃ i, MvPolynomial.eval x (φ i) ≠ 0)


variable {K : Type*} [Field K] [NumberField K]
variable {n m : ℕ}

theorem theorem_25_14_upper_bound
    {d : ℕ} {φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K}
    (hφ : IsProjectiveMorphism d φ) :
    ∃ C₁ : ℝ, ∀ (x : Fin (n + 1) → K),
      logHeight (fun j => (φ j).eval x) ≤ C₁ + ↑d * logHeight x :=
  logHeight_eval_le' hφ.1



end Theorem_25_14

end
