/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.DirectedInverseSystem
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup

noncomputable section

open Set

abbrev IsDirectedSet (I : Type*) [PartialOrder I] : Prop :=
  IsDirected I (· ≤ ·) ∧ Nonempty I

abbrev IsAnInverseSystem {ι : Type*} [Preorder ι] {F : ι → Type*}
    (f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i) : Prop :=
  InverseSystem f

def InvLim {ι : Type*} [Preorder ι] (X : ι → Type*) (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) :
    Set (∀ i, X i) :=
  { x | ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i }

theorem InvLim.proj_compat {ι : Type*} [Preorder ι] {X : ι → Type*}
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i} (x : InvLim X f) {i j : ι} (h : i ≤ j) :
    f h (x.1 j) = x.1 i :=
  x.property h

theorem invLim_isClosed {ι : Type*} [Preorder ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
    IsClosed (InvLim X f) := by

  unfold InvLim
  simp_rw [setOf_forall]
  apply isClosed_iInter; intro i
  apply isClosed_iInter; intro j
  apply isClosed_iInter; intro h


  exact isClosed_eq ((hf h).comp (continuous_apply j)) (continuous_apply i)

theorem invLim_isCompact {ι : Type*} [Preorder ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, CompactSpace (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
    IsCompact (InvLim X f) :=
  (invLim_isClosed hf).isCompact

noncomputable def adicComplete_ringEquiv_adicCompletion (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] : R ≃+* AdicCompletion I R :=
  RingEquiv.ofBijective (algebraMap R (AdicCompletion I R))
    (AdicCompletion.of_bijective I R)

noncomputable def dvr_ringEquiv_adicCompletion (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    R ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  adicComplete_ringEquiv_adicCompletion R (IsLocalRing.maximalIdeal R)

section AdicCompletionTopology

theorem mem_ideal_pow_iff_evalₐ_eq_zero (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) (x : R) :
    x ∈ (I ^ n : Ideal R) ↔
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) x) = 0 := by
  rw [show algebraMap R (AdicCompletion I R) x = AdicCompletion.of I R x from rfl]
  rw [AdicCompletion.evalₐ_of]
  rw [Ideal.Quotient.eq_zero_iff_mem]

end AdicCompletionTopology

section AdicCompletionTopologicalRingIso

theorem adicComplete_ringEquiv_symm_mem_iff_evalₐ_eq_zero (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (n : ℕ) (y : AdicCompletion I R) :
    (adicComplete_ringEquiv_adicCompletion R I).symm y ∈ (I ^ n : Ideal R) ↔
    AdicCompletion.evalₐ I n y = 0 := by
  set e := adicComplete_ringEquiv_adicCompletion R I with he
  have key : algebraMap R (AdicCompletion I R) (e.symm y) = y :=
    e.apply_symm_apply y
  constructor
  · intro h
    rw [← key,
      show algebraMap R (AdicCompletion I R) (e.symm y) =
        AdicCompletion.of I R (e.symm y) from rfl,
      AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    exact h
  · intro h
    rw [← key,
      show algebraMap R (AdicCompletion I R) (e.symm y) =
        AdicCompletion.of I R (e.symm y) from rfl,
      AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h

theorem adicComplete_topological_ringIso (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] :

    Nonempty (R ≃+* AdicCompletion I R) ∧

    (∀ n x, x ∈ (I ^ n : Ideal R) ↔
      AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) x) = 0) ∧

    (∀ n y, (adicComplete_ringEquiv_adicCompletion R I).symm y ∈ (I ^ n : Ideal R) ↔
      AdicCompletion.evalₐ I n y = 0) :=
  ⟨⟨adicComplete_ringEquiv_adicCompletion R I⟩,
    fun n x => mem_ideal_pow_iff_evalₐ_eq_zero R I n x,
    fun n y => adicComplete_ringEquiv_symm_mem_iff_evalₐ_eq_zero R I n y⟩

end AdicCompletionTopologicalRingIso

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def padicIntToProd : ℤ_[p] → (∀ n : ℕ, ZMod (p ^ n)) :=
  fun z n => PadicInt.toZModPow n z

theorem padicInt_toZModPow_injective :
    Function.Injective (padicIntToProd (p := p)) := by
  intro x y h
  rw [← PadicInt.ext_of_toZModPow]
  exact fun n => congr_fun h n

theorem padicIntToProd_compat (z : ℤ_[p]) (m n : ℕ) (h : m ≤ n) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (padicIntToProd z n) =
    padicIntToProd z m := by
  simp only [padicIntToProd]
  exact congr_fun (congrArg DFunLike.coe
    (PadicInt.zmod_cast_comp_toZModPow m n h)) z

theorem padicInt_toZModPow_surjective
    (x : ∀ n : ℕ, ZMod (p ^ n))
    (hcompat : ∀ (m n : ℕ) (h : m ≤ n),
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (x n) = x m) :
    ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = x n := by

  set f : ℕ → ℤ := fun n => (ZMod.val (x n) : ℤ)

  have hdvd : ∀ i, (p : ℤ) ^ i ∣ f (i + 1) - f i := by
    intro i
    haveI : NeZero (p ^ i) := ⟨pow_ne_zero i hp.out.ne_zero⟩
    haveI : NeZero (p ^ (i + 1)) := ⟨pow_ne_zero (i + 1) hp.out.ne_zero⟩
    have h := hcompat i (i + 1) (Nat.le_succ i)
    have hval : ZMod.val (x i) = ZMod.val (x (i + 1)) % p ^ i := by
      have := congr_arg ZMod.val h
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] at this
      exact this.symm
    simp only [f]
    rw [hval]
    have key : (ZMod.val (x (i + 1)) : ℤ) - ↑(ZMod.val (x (i + 1)) % p ^ i) =
        ↑(ZMod.val (x (i + 1)) / p ^ i) * (p : ℤ) ^ i := by
      push_cast
      have := Nat.div_add_mod (ZMod.val (x (i + 1))) (p ^ i)
      linarith
    rw [key]
    exact dvd_mul_left _ _

  set z := PadicInt.ofIntSeq f
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub f p hdvd)

  refine ⟨z, fun n => ?_⟩
  have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub f p hdvd n
  rw [this]
  simp only [f]
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def padicInvLimSubring : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := { x | ∀ (m n : ℕ) (h : m ≤ n),
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (x n) = x m }
  mul_mem' := by
    intro a b ha hb m n h
    simp only [Pi.mul_apply]; rw [map_mul, ha m n h, hb m n h]
  one_mem' := by intro m n h; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro a b ha hb m n h
    simp only [Pi.add_apply]; rw [map_add, ha m n h, hb m n h]
  zero_mem' := by intro m n h; simp only [Pi.zero_apply, map_zero]
  neg_mem' := by
    intro a ha m n h
    simp only [Pi.neg_apply]; rw [map_neg, ha m n h]

def padicIntToInvLimRingHom : ℤ_[p] →+* padicInvLimSubring (p := p) where
  toFun z := ⟨fun n => PadicInt.toZModPow n z, by
    intro m n h
    exact congr_fun (congrArg DFunLike.coe
      (PadicInt.zmod_cast_comp_toZModPow m n h)) z⟩
  map_zero' := by apply Subtype.ext; funext n; simp [map_zero]
  map_one' := by apply Subtype.ext; funext n; simp [map_one]
  map_add' := by intro x y; apply Subtype.ext; funext n; simp [map_add]
  map_mul' := by intro x y; apply Subtype.ext; funext n; simp [map_mul]

theorem padicIntToInvLimRingHom_bijective :
    Function.Bijective (padicIntToInvLimRingHom (p := p)) := by
  constructor
  ·
    intro x y hxy
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    have := congr_arg (fun s => s.1 n) hxy
    simpa [padicIntToInvLimRingHom] using this
  ·
    intro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := padicInt_toZModPow_surjective x hx
    exact ⟨z, Subtype.ext (funext hz)⟩

noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

theorem appr_succ_eq (a : ℤ_[p]) (n : ℕ) :
    a.appr (n + 1) = a.appr n + p ^ n * padicDigit a n := by
  unfold padicDigit
  have hmono : a.appr n ≤ a.appr (n + 1) := a.appr_mono (Nat.le_succ n)
  have hdvd := a.dvd_appr_sub_appr n (n + 1) (Nat.le_succ n)
  have key : a.appr (n + 1) - a.appr n = p ^ n * ((a.appr (n + 1) - a.appr n) / p ^ n) :=
    Nat.eq_mul_of_div_eq_right hdvd rfl
  omega

def digitPartialSum (p : ℕ) (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => digitPartialSum p b n + p ^ n * b n

omit hp in
@[simp]
theorem digitPartialSum_succ (b : ℕ → ℕ) (n : ℕ) :
    digitPartialSum p b (n + 1) = digitPartialSum p b n + p ^ n * b n := rfl

theorem digitPartialSum_lt (b : ℕ → ℕ) (hb : ∀ i, b i < p) (n : ℕ) :
    digitPartialSum p b n < p ^ n := by
  induction n with
  | zero => simp [digitPartialSum]
  | succ n ih =>
    simp only [digitPartialSum, pow_succ]
    have hbn := hb n
    have hpn_pos : 0 < p ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hp.out.ne_zero)
    have hp_pos : 0 < p := hp.out.pos
    have h1 : p ^ n * b n ≤ p ^ n * (p - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : p ^ n + p ^ n * (p - 1) = p ^ n * p := by
      have : 1 + (p - 1) = p := by omega
      nlinarith
    linarith

omit hp in
theorem digitPartialSum_dvd (b : ℕ → ℕ) (n : ℕ) :
    (p : ℤ) ^ n ∣ (digitPartialSum p b (n + 1) : ℤ) - (digitPartialSum p b n : ℤ) := by
  simp only [digitPartialSum]
  push_cast
  ring_nf
  exact dvd_mul_right _ _

noncomputable def padicIntOfDigits (b : ℕ → ℕ) (_hb : ∀ i, b i < p) : ℤ_[p] :=
  PadicInt.ofIntSeq (fun n => (digitPartialSum p b n : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (digitPartialSum_dvd b))

theorem toZModPow_padicIntOfDigits (b : ℕ → ℕ) (hb : ∀ i, b i < p) (n : ℕ) :
    PadicInt.toZModPow n (padicIntOfDigits b hb) = (digitPartialSum p b n : ℤ) :=
  PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (digitPartialSum_dvd b) n

theorem appr_padicIntOfDigits (b : ℕ → ℕ) (hb : ∀ i, b i < p) (n : ℕ) :
    (padicIntOfDigits b hb).appr n = digitPartialSum p b n := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  have hlt := digitPartialSum_lt b hb n
  have hzmod := toZModPow_padicIntOfDigits b hb n
  have h1 : (padicIntOfDigits b hb).appr n < p ^ n := PadicInt.appr_lt _ n
  have h2 : PadicInt.toZModPow n (padicIntOfDigits b hb) =
      ((padicIntOfDigits b hb).appr n : ZMod (p ^ n)) := by
    simp [PadicInt.toZModPow]
    rfl
  rw [h2] at hzmod
  have h3 : ((digitPartialSum p b n : ℤ) : ZMod (p ^ n)) =
      (digitPartialSum p b n : ZMod (p ^ n)) := by push_cast; ring
  rw [h3] at hzmod
  exact ZMod.val_cast_of_lt h1 ▸ ZMod.val_cast_of_lt hlt ▸
    congr_arg ZMod.val hzmod

theorem padicExpansion_unique (a a' : ℤ_[p])
    (h : ∀ n, padicDigit a n = padicDigit a' n) : a = a' := by
  suffices happr : ∀ n, a.appr n = a'.appr n by
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have h1 : PadicInt.toZModPow n a = ((a.appr n : ℕ) : ZMod (p ^ n)) := by
      simp [PadicInt.toZModPow]; rfl
    have h2 : PadicInt.toZModPow n a' = ((a'.appr n : ℕ) : ZMod (p ^ n)) := by
      simp [PadicInt.toZModPow]; rfl
    rw [h1, h2, happr n]
  intro n
  induction n with
  | zero =>
    have h1 := a.appr_lt 0
    have h2 := a'.appr_lt 0
    simp at h1 h2
    omega
  | succ n ih =>
    rw [appr_succ_eq a n, appr_succ_eq a' n, ih, h n]

end
