/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open Complex NumberField

theorem isRootOfUnity_of_isIntegral_of_norm_eq_one
    {K : Type*} [Field K] [NumberField K]
    {θ : K} (hθ_int : IsIntegral ℤ θ)
    (hθ_norm : ∀ φ : K →+* ℂ, ‖φ θ‖ = 1) :
    ∃ (n : ℕ) (_ : 0 < n), θ ^ n = 1 :=
  NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hθ_int hθ_norm

open Polynomial

namespace CirculantHadamard

theorem irreducible_cyclotomic_two_pow (k : ℕ) :
    Irreducible (cyclotomic (2 ^ k) ℚ) :=
  cyclotomic.irreducible_rat (pow_pos two_pos k)

section TwoFactorization

open Ideal NumberField RingOfIntegers IsCyclotomicExtension.Rat

variable (k : ℕ) (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))

theorem isPrime_span_zeta_sub_one_two_pow :
    IsPrime (span {hζ.toInteger - 1} : Ideal (𝓞 K)) :=
  isPrime_span_zeta_sub_one 2 k hζ

theorem zeta_sub_one_prime_two_pow :
    Prime (hζ.toInteger - 1) := by
  have hne : hζ.toInteger - 1 ≠ 0 := fun h =>
    span_zeta_sub_one_ne_bot 2 k hζ (Ideal.span_singleton_eq_bot.mpr h)
  exact (Ideal.span_singleton_prime hne).mp (isPrime_span_zeta_sub_one_two_pow k K hζ)

theorem finrank_cyclotomic_two_pow :
    Module.finrank ℚ K = 2 ^ k := by
  rw [IsCyclotomicExtension.Rat.finrank (2 ^ (k + 1)) K]
  simp [Nat.totient_prime_pow_succ Nat.prime_two]

theorem ideal_span_two_eq_span_zeta_sub_one_pow :
    Ideal.map (algebraMap ℤ (𝓞 K)) (span {(2 : ℤ)}) =
      span {hζ.toInteger - 1} ^ (2 ^ k) := by
  have := map_eq_span_zeta_sub_one_pow 2 k hζ
  rwa [finrank_cyclotomic_two_pow k K] at this

theorem associated_two_zeta_sub_one_pow :
    Associated (algebraMap ℤ (𝓞 K) 2) ((hζ.toInteger - 1) ^ (2 ^ k)) := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  have h := ideal_span_two_eq_span_zeta_sub_one_pow k K hζ
  rw [Ideal.map_span, Set.image_singleton] at h
  rwa [Ideal.span_singleton_pow] at h

theorem two_eq_zeta_sub_one_pow_mul_unit :
    ∃ u : (𝓞 K)ˣ, (algebraMap ℤ (𝓞 K) 2) = (hζ.toInteger - 1) ^ (2 ^ k) * ↑u := by
  obtain ⟨u, hu⟩ := (associated_two_zeta_sub_one_pow k K hζ).symm
  exact ⟨u, hu.symm⟩

theorem card_quotient_zeta_sub_one_eq_two :
    Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) = 2 := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩


  rw [IsPrimitiveRoot.card_quotient_toInteger_sub_one hζ]


  rw [← Ideal.absNorm_span_singleton]


  have hfact := ideal_span_two_eq_span_zeta_sub_one_pow k K hζ

  have h_pow : Ideal.absNorm (span {hζ.toInteger - 1} ^ (2 ^ k)) =
      Ideal.absNorm (span {hζ.toInteger - 1}) ^ (2 ^ k) :=
    map_pow Ideal.absNorm _ _

  have h_two : Ideal.absNorm (Ideal.map (algebraMap ℤ (𝓞 K)) (span {(2 : ℤ)})) =
      2 ^ (2 ^ k) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.absNorm_span_singleton]
    rw [Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis ℤ (𝓞 K))]
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      NumberField.RingOfIntegers.rank, finrank_cyclotomic_two_pow k K]
    simp [Int.natAbs_pow]

  have h_eq : Ideal.absNorm (span {hζ.toInteger - 1}) ^ (2 ^ k) = 2 ^ (2 ^ k) := by
    rw [← h_pow, ← hfact]
    exact h_two
  exact Nat.pow_left_injective (by positivity : 2 ^ k ≠ 0) h_eq

end TwoFactorization

end CirculantHadamard

section Kronecker

open NumberField.ComplexEmbedding

theorem kronecker_isRootOfUnity_of_cyclotomic
    {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    {α : K} (hα_int : IsIntegral ℤ α)
    (φ₀ : K →+* ℂ) (hα_norm : ‖φ₀ α‖ = 1) :
    ∃ (m : ℕ) (_ : 0 < m), α ^ m = 1 := by

  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K

  apply isRootOfUnity_of_isIntegral_of_norm_eq_one hα_int
  intro φ

  have h_agree : φ₀.comp (algebraMap ℚ K) = φ.comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  have h_agree_conj : φ₀.comp (algebraMap ℚ K) = (conjugate φ₀).comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  obtain ⟨σ, hσ⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ₀ φ h_agree
  obtain ⟨c, hc⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ₀ (conjugate φ₀) h_agree_conj


  have hcomm : ∀ (a b : K ≃ₐ[ℚ] K), a * b = b * a := by
    intro a b
    have key : (IsCyclotomicExtension.Rat.galEquivZMod n K) (a * b) =
        (IsCyclotomicExtension.Rat.galEquivZMod n K) (b * a) := by
      simp only [map_mul]
      exact mul_comm _ _
    exact (IsCyclotomicExtension.Rat.galEquivZMod n K).injective key

  have hα_prod : α * c.symm α = 1 := by
    have h1 : φ₀ (α * c.symm α) = 1 := by
      rw [map_mul]

      have hc_eq : φ₀ (c.symm α) = starRingEnd ℂ (φ₀ α) := by
        have := RingHom.congr_fun hc α
        simp only [RingHom.comp_apply, conjugate_coe_eq] at this
        exact this
      rw [hc_eq]

      have := RCLike.mul_conj (φ₀ α)
      rw [hα_norm] at this
      simp at this
      exact this
    exact φ₀.injective (by rw [h1, map_one])


  have hconj_φ : starRingEnd ℂ (φ α) = φ₀ (c.symm (σ.symm α)) := by

    have step1 : φ₀ (c.symm (σ.symm α)) = starRingEnd ℂ (φ₀ (σ.symm α)) := by
      have := RingHom.congr_fun hc (σ.symm α)
      simp only [RingHom.comp_apply, conjugate_coe_eq] at this
      exact this
    have step2 : φ₀ (σ.symm α) = φ α := by
      have := RingHom.congr_fun hσ α
      simp only [RingHom.comp_apply] at this
      exact this
    rw [step1, step2]

  have hswap : c.symm (σ.symm α) = σ.symm (c.symm α) := by
    have hcs := hcomm c.symm σ.symm
    exact AlgEquiv.ext_iff.mp hcs α

  have hnorm_sq : (φ α) * starRingEnd ℂ (φ α) = 1 := by
    rw [hconj_φ, hswap]


    have hφ_eq : φ α = φ₀ (σ.symm α) := by
      have := RingHom.congr_fun hσ α
      simp only [RingHom.comp_apply] at this
      exact this.symm
    rw [hφ_eq]

    rw [← map_mul]

    rw [← map_mul σ.symm]

    rw [hα_prod, map_one, map_one]

  have h_real : ‖φ α‖ = 1 := by
    have hmul := RCLike.mul_conj (φ α)
    rw [hnorm_sq] at hmul

    have h1 : (‖φ α‖ : ℂ) ^ 2 = 1 := hmul.symm
    have h2 : ((‖φ α‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by push_cast; exact h1
    have h3 : ‖φ α‖ ^ 2 = (1 : ℝ) := by exact_mod_cast h2
    nlinarith [norm_nonneg (φ α)]
  exact h_real

end Kronecker

section EigenvalueAbs

open Finset

structure CirculantHadamardMatrix (n : ℕ) [NeZero n] where
  a : ZMod n → ℤ
  entries_sq : ∀ i, a i ^ 2 = 1
  orthogonality : ∀ j : ZMod n, ∑ i : ZMod n, a i * a (i + j) = if j = 0 then (n : ℤ) else 0

variable {n : ℕ} [NeZero n]

noncomputable def CirculantHadamardMatrix.eigenvalue (H : CirculantHadamardMatrix n)
    (ζ : ℂ) (j : ZMod n) : ℂ :=
  ∑ i : ZMod n, (H.a i : ℂ) * ζ ^ (i * j).val

lemma pow_zmod_val_add (ζ : ℂ) (hζn : ζ ^ (n : ℕ) = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add]


  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) n, pow_add, pow_mul, hζn, one_pow, one_mul]
  rw [ZMod.val_add]

lemma circulantHadamard_eigenvalue_conj_mul (H : CirculantHadamardMatrix n)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) (j : ZMod n) :
    starRingEnd ℂ (H.eigenvalue ζ j) * H.eigenvalue ζ j = ↑(n : ℤ) := by
  have hζn : ζ ^ (n : ℕ) = 1 := hζ.pow_eq_one
  have hζne : ζ ≠ 0 := by
    intro h; rw [h, zero_pow (NeZero.ne n)] at hζn; exact one_ne_zero hζn.symm
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one (NeZero.ne n)
  have hζ_conj : starRingEnd ℂ ζ = ζ⁻¹ := by
    have hmul : ζ * starRingEnd ℂ ζ = 1 := by
      have h1 := RCLike.mul_conj ζ
      rw [hζ_norm] at h1; norm_num at h1; exact h1
    exact mul_left_cancel₀ hζne
      (by rw [hmul, mul_inv_cancel₀ hζne])
  have hζ_inv_pow : ζ⁻¹ ^ (n : ℕ) = 1 := by rw [inv_pow, hζn, inv_one]

  unfold CirculantHadamardMatrix.eigenvalue

  simp only [map_sum, map_mul, map_intCast, map_pow]

  rw [Fintype.sum_mul_sum]

  simp_rw [hζ_conj]


  simp_rw [show ∀ k i : ZMod n,
    (↑(H.a k) : ℂ) * ζ⁻¹ ^ (k * j).val * (↑(H.a i) * ζ ^ (i * j).val) =
    ↑(H.a i) * ↑(H.a k) * (ζ⁻¹ ^ (k * j).val * ζ ^ (i * j).val) from
    fun k i => by ring]
  rw [Finset.sum_comm]

  simp_rw [show ∀ i : ZMod n,
    (∑ k : ZMod n, ↑(H.a i) * ↑(H.a k) *
      (ζ⁻¹ ^ (k * j).val * ζ ^ (i * j).val)) =
    ∑ m : ZMod n, ↑(H.a i) * ↑(H.a (i + m)) *
      (ζ⁻¹ ^ ((i + m) * j).val * ζ ^ (i * j).val) from
    fun i => (Equiv.sum_comp (Equiv.addLeft i) _).symm]

  simp_rw [show ∀ i m : ZMod n, (i + m) * j = i * j + m * j from fun i m => add_mul i m j]
  simp_rw [pow_zmod_val_add ζ⁻¹ hζ_inv_pow]


  simp_rw [show ∀ i m : ZMod n,
    ↑(H.a i) * ↑(H.a (i + m)) *
      (ζ⁻¹ ^ (i * j).val * ζ⁻¹ ^ (m * j).val * ζ ^ (i * j).val) =
    ↑(H.a i) * ↑(H.a (i + m)) * ζ⁻¹ ^ (m * j).val *
      (ζ⁻¹ ^ (i * j).val * ζ ^ (i * j).val) from fun i m => by ring]
  simp_rw [show ∀ i : ZMod n, ζ⁻¹ ^ (i * j).val * ζ ^ (i * j).val = 1 from
    fun i => by rw [← mul_pow, inv_mul_cancel₀ hζne, one_pow (M := ℂ)]]
  simp only [mul_one]

  rw [Finset.sum_comm]

  simp_rw [show ∀ m i : ZMod n,
    ↑(H.a i) * ↑(H.a (i + m)) * ζ⁻¹ ^ (m * j).val =
    ζ⁻¹ ^ (m * j).val * (↑(H.a i) * ↑(H.a (i + m))) from fun m i => by ring]
  simp_rw [← Finset.mul_sum]

  simp_rw [show ∀ m : ZMod n,
    (∑ i : ZMod n, (↑(H.a i) : ℂ) * ↑(H.a (i + m))) =
    ↑(∑ i : ZMod n, H.a i * H.a (i + m)) from fun m => by push_cast; rfl]
  simp_rw [H.orthogonality]

  simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ 0]
  simp [Finset.mem_univ]

theorem circulantHadamard_eigenvalue_abs (H : CirculantHadamardMatrix n)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) (j : ZMod n) :
    ‖H.eigenvalue ζ j‖ = Real.sqrt n := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  congr 1

  have h := circulantHadamard_eigenvalue_conj_mul H ζ hζ j
  have h2 := Complex.conj_mul' (H.eigenvalue ζ j)


  rw [h] at h2

  have h3 : (‖H.eigenvalue ζ j‖ ^ 2 : ℂ) = (↑(n : ℤ) : ℂ) := h2.symm
  have h4 : (‖H.eigenvalue ζ j‖ ^ 2 : ℝ) = (n : ℝ) := by
    have := Complex.ofReal_re (‖H.eigenvalue ζ j‖ ^ 2)
    rw [← this]
    have := Complex.ofReal_re (n : ℝ)
    rw [← this]
    congr 1
    push_cast at h3 ⊢
    exact h3
  exact h4

def CirculantHadamardMatrix.toMatrix (H : CirculantHadamardMatrix n) :
    Matrix (ZMod n) (ZMod n) ℤ :=
  Matrix.of fun i j => H.a (i - j)

theorem CirculantHadamardMatrix.toMatrix_mul_transpose (H : CirculantHadamardMatrix n) :
    H.toMatrix * H.toMatrix.transpose = (n : ℤ) • (1 : Matrix (ZMod n) (ZMod n) ℤ) := by
  ext i j
  simp only [CirculantHadamardMatrix.toMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero]


  rw [show (∑ k : ZMod n, H.a (i - k) * H.a (j - k)) =
    ∑ d : ZMod n, H.a d * H.a (d + (j - i)) from
    Fintype.sum_equiv (Equiv.subLeft i)
      (fun k => H.a (i - k) * H.a (j - k))
      (fun d => H.a d * H.a (d + (j - i)))
      (fun d => by simp only [Equiv.subLeft_apply]; congr 1; congr 1; abel)]
  rw [H.orthogonality (j - i)]
  split_ifs with h1 h2 h2
  · simp [smul_eq_mul]
  · exact absurd (sub_eq_zero.mp h1).symm h2
  · exact absurd (sub_eq_zero.mpr h2.symm) h1
  · rfl

theorem circulant_hadamard_det_sq (H : CirculantHadamardMatrix n) :
    (Matrix.det H.toMatrix) ^ 2 = (n : ℤ) ^ (n : ℕ) := by
  have hmul := H.toMatrix_mul_transpose
  calc (Matrix.det H.toMatrix) ^ 2
      = Matrix.det H.toMatrix * Matrix.det H.toMatrix := sq _
    _ = Matrix.det H.toMatrix * Matrix.det H.toMatrix.transpose := by
        rw [Matrix.det_transpose]
    _ = Matrix.det (H.toMatrix * H.toMatrix.transpose) := (Matrix.det_mul _ _).symm
    _ = Matrix.det ((n : ℤ) • (1 : Matrix (ZMod n) (ZMod n) ℤ)) := by rw [hmul]
    _ = (n : ℤ) ^ Fintype.card (ZMod n) * Matrix.det 1 := Matrix.det_smul _ _
    _ = (n : ℤ) ^ (n : ℕ) * 1 := by rw [ZMod.card, Matrix.det_one]
    _ = (n : ℤ) ^ (n : ℕ) := mul_one _

end EigenvalueAbs

section EigenvalueFactorization

open Ideal NumberField RingOfIntegers IsCyclotomicExtension.Rat

noncomputable def eigenvalueOI {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K]
    (H : CirculantHadamardMatrix n) (ζ_int : 𝓞 K) (j : ZMod n) : 𝓞 K :=
  ∑ i : ZMod n, algebraMap ℤ (𝓞 K) (H.a i) * ζ_int ^ (i * j).val

lemma dvd_of_dvd_mul_prime_right {R : Type*} [CommRing R] [IsDomain R]
    {p c b : R} (hp : Prime p) (hpc : ¬(p ∣ c)) (h : c ∣ b * p) : c ∣ b := by
  obtain ⟨d, hd⟩ := h
  have hpcd : p ∣ c * d := ⟨b, hd.symm.trans (mul_comm b p)⟩
  obtain ⟨e, he⟩ := (hp.dvd_or_dvd hpcd).resolve_left hpc
  exact ⟨e, mul_left_cancel₀ hp.ne_zero (by rw [mul_comm p b, hd, he]; ring)⟩

lemma dvd_of_dvd_mul_prime_pow_right {R : Type*} [CommRing R] [IsDomain R]
    {p c b : R} (hp : Prime p) (hpc : ¬(p ∣ c)) :
    ∀ (M : ℕ), c ∣ b * p ^ M → c ∣ b := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    intro h
    rw [pow_succ, ← mul_assoc] at h
    exact ih (dvd_of_dvd_mul_prime_right hp hpc h)

variable (k : ℕ) (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))

omit [NumberField K] [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] in
lemma zeta_pow_half_eq_neg_one : hζ.toInteger ^ (2^k) = -1 := by
  have h_dvd : (2 : ℕ)^k ∣ 2^(k+1) := ⟨2, by ring⟩
  have h_ne : (2 : ℕ)^k ≠ 0 := by positivity
  have h_div : 2^(k+1) / 2^k = 2 := by
    rw [pow_succ]
    exact Nat.mul_div_cancel_left 2 (Nat.pos_of_ne_zero h_ne)
  have h_prim2 : IsPrimitiveRoot (hζ.toInteger ^ 2^k) 2 := by
    have := hζ.toInteger_isPrimitiveRoot.pow_of_dvd h_ne h_dvd
    rwa [h_div] at this
  exact h_prim2.eq_neg_one_of_two_right

lemma pow_zmod_val_add_gen {R : Type*} [Monoid R] {m : ℕ} [NeZero m]
    (ζ : R) (hζ : ζ ^ (m : ℕ) = 1) (a b : ZMod m) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) m, pow_add, pow_mul, hζ, one_pow, one_mul]

lemma pow_zmod_mul_val_gen {R : Type*} [Monoid R] {m : ℕ}
    (ζ : R) (hζ : ζ ^ (m : ℕ) = 1) (a b : ZMod m) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, ZMod.val_mul, mul_comm a.val b.val]
  conv_rhs => rw [← Nat.div_add_mod (b.val * a.val) m, pow_add, pow_mul, hζ, one_pow, one_mul]

lemma circulant_transpose_mul_dft {R : Type*} [CommRing R] {m : ℕ} [NeZero m]
    (a : ZMod m → R) (ζ : R) (hζ : ζ ^ (m : ℕ) = 1) :
    (Matrix.of fun i j : ZMod m => a (j - i)) *
    (Matrix.of fun i j : ZMod m => ζ ^ (i * j).val) =
    (Matrix.of fun i j : ZMod m => ζ ^ (i * j).val) *
    Matrix.diagonal (fun j => ∑ i : ZMod m, a i * ζ ^ (i * j).val) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show (∑ x : ZMod m, a (x - i) * ζ ^ (x * j).val) =
    ∑ t : ZMod m, a t * ζ ^ ((t + i) * j).val from
    Fintype.sum_equiv (Equiv.subRight i) _ _ (fun x => by
      simp only [Equiv.subRight_apply, sub_add_cancel])]
  simp_rw [show ∀ t : ZMod m, (t + i) * j = t * j + i * j from fun t => add_mul t i j]
  simp_rw [pow_zmod_val_add_gen ζ hζ]
  simp_rw [show ∀ t : ZMod m, a t * (ζ ^ (t * j).val * ζ ^ (i * j).val) =
    a t * ζ ^ (t * j).val * ζ ^ (i * j).val from fun t => by ring]
  rw [← Finset.sum_mul]; ring

lemma sum_zmod_eq_sum_fin {R : Type*} [AddCommMonoid R] {m : ℕ} [NeZero m]
    (f : Fin m → R) :
    ∑ x : ZMod m, f ⟨x.val, ZMod.val_lt x⟩ = ∑ i : Fin m, f i := by
  apply Fintype.sum_bijective (fun x : ZMod m => (⟨x.val, ZMod.val_lt x⟩ : Fin m))
  · constructor
    · intro a b h
      exact ZMod.val_injective m (congr_arg Fin.val h)
    · intro ⟨i, hi⟩
      exact ⟨(i : ZMod m), by simp [ZMod.val_natCast_of_lt hi]⟩
  · intro x; rfl

lemma geom_sum_zmod_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} [NeZero m] (ω : R) (hω : ω ^ (m : ℕ) = 1) (hω1 : ω ≠ 1) :
    ∑ x : ZMod m, ω ^ x.val = 0 := by
  rw [sum_zmod_eq_sum_fin (fun i => ω ^ (i : ℕ)), Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul ω m
  rw [hω, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hω1)

lemma dft_orthogonality_off_diag {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} [NeZero m] {ζ : R} (hζ : IsPrimitiveRoot ζ m)
    {d : ZMod m} (hd : d ≠ 0) :
    ∑ x : ZMod m, ζ ^ (x * d).val = 0 := by
  simp_rw [pow_zmod_mul_val_gen ζ hζ.pow_eq_one]
  apply geom_sum_zmod_eq_zero
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · have hd_val_ne : d.val ≠ 0 := fun h => hd ((ZMod.val_eq_zero d).mp h)
    exact hζ.pow_ne_one_of_pos_of_lt hd_val_ne (ZMod.val_lt d)

lemma dft_mul_conj_dft {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} [NeZero m] {ζ : R} (hζ : IsPrimitiveRoot ζ m) :
    (Matrix.of fun i j : ZMod m => ζ ^ (i * j).val) *
    (Matrix.of fun i j : ZMod m => ζ ^ (-(i * j)).val) =
    (m : R) • (1 : Matrix (ZMod m) (ZMod m) R) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  simp_rw [show ∀ x : ZMod m, ζ ^ (i * x).val * ζ ^ (-(x * j)).val =
    ζ ^ (i * x + (-(x * j))).val from fun x => (pow_zmod_val_add_gen ζ hζ.pow_eq_one _ _).symm]
  simp_rw [show ∀ x : ZMod m, i * x + -(x * j) = x * (i - j) from fun x => by ring]
  split_ifs with h
  · subst h; simp [ZMod.val_zero]
  · simp only [mul_zero]
    exact dft_orthogonality_off_diag hζ (sub_ne_zero.mpr h)

lemma det_dft_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {m : ℕ} [NeZero m] {ζ : R} (hζ : IsPrimitiveRoot ζ m) :
    (Matrix.of fun i j : ZMod m => ζ ^ (i * j).val).det ≠ 0 := by
  intro h
  have hmul := dft_mul_conj_dft hζ
  have hdet := congr_arg Matrix.det hmul
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have hm_ne : (m : R) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [ZMod.card m] at hdet

  exact absurd hdet.symm (pow_ne_zero m hm_ne)

omit [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] in
theorem prod_eigenvalueOI_eq_algebraMap_det
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    ∏ j : ZMod (2 ^ (k + 1)), eigenvalueOI H (hζ.toInteger) j =
      algebraMap ℤ (𝓞 K) (Matrix.det H.toMatrix) := by
  set n := 2 ^ (k + 1) with hn_def
  set ζ_int := hζ.toInteger with hζ_int_def
  have hζ_prim : IsPrimitiveRoot ζ_int n := hζ.toInteger_isPrimitiveRoot
  have hζ_pow : ζ_int ^ (n : ℕ) = 1 := hζ_prim.pow_eq_one

  rw [RingHom.map_det]

  have hmap : (algebraMap ℤ (𝓞 K)).mapMatrix H.toMatrix =
      Matrix.of (fun i j => algebraMap ℤ (𝓞 K) (H.a (i - j))) := by
    simp only [RingHom.mapMatrix_apply, Matrix.map, Matrix.of_apply,
      CirculantHadamardMatrix.toMatrix]
  rw [hmap]

  conv_rhs => rw [← Matrix.det_transpose]

  have htransp : (Matrix.of fun i j : ZMod n => algebraMap ℤ (𝓞 K) (H.a (i - j))).transpose =
      Matrix.of fun i j : ZMod n => algebraMap ℤ (𝓞 K) (H.a (j - i)) := by
    ext i j; simp [Matrix.transpose_apply, Matrix.of_apply]
  rw [htransp]

  set F := Matrix.of (fun i j : ZMod n => ζ_int ^ (i * j).val) with hF_def
  set γ := fun j : ZMod n => eigenvalueOI H ζ_int j with hγ_def

  have hmatrix_eq : (Matrix.of fun i j : ZMod n => algebraMap ℤ (𝓞 K) (H.a (j - i))) * F =
      F * Matrix.diagonal γ := by
    have := circulant_transpose_mul_dft (fun i => algebraMap ℤ (𝓞 K) (H.a i)) ζ_int hζ_pow
    convert this using 2

  have hdet_F_ne : F.det ≠ 0 := det_dft_ne_zero hζ_prim
  have hdet_eq : (Matrix.of fun i j : ZMod n => algebraMap ℤ (𝓞 K) (H.a (j - i))).det * F.det =
      F.det * ∏ j, γ j := by
    rw [← Matrix.det_mul, hmatrix_eq, Matrix.det_mul, Matrix.det_diagonal]
  rw [mul_comm] at hdet_eq
  exact (mul_left_cancel₀ hdet_F_ne hdet_eq).symm

omit [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] in
theorem prod_eigenvalueOI_eq_pm_pow
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    ∃ (s : ℤ), s ^ 2 = 1 ∧
      ∏ j : ZMod (2 ^ (k + 1)), eigenvalueOI H (hζ.toInteger) j =
        algebraMap ℤ (𝓞 K) (s * (2 : ℤ) ^ ((k + 1) * 2 ^ k)) := by

  rw [prod_eigenvalueOI_eq_algebraMap_det k K hζ H]


  have hsq := circulant_hadamard_det_sq H

  push_cast at hsq

  have hnn : ((2 : ℤ) ^ (k + 1)) ^ (2 ^ (k + 1)) = ((2 : ℤ) ^ ((k + 1) * 2 ^ k)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    rw [pow_succ]
    ring
  rw [hnn] at hsq

  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
  · exact ⟨1, by norm_num, by rw [h, one_mul]⟩
  · exact ⟨-1, by norm_num, by rw [h]; congr 1; ring⟩

lemma algebraMap_two_pow_eq_unit_mul_zeta_sub_one_pow (N : ℕ) :
    ∃ (v : (𝓞 K)ˣ) (M : ℕ),
      (algebraMap ℤ (𝓞 K) 2) ^ N = ↑v * (hζ.toInteger - 1) ^ M := by
  obtain ⟨u, hu⟩ := CirculantHadamard.two_eq_zeta_sub_one_pow_mul_unit k K hζ
  exact ⟨u ^ N, 2 ^ k * N, by rw [hu, mul_pow, pow_mul]; simp [mul_comm, Units.val_pow_eq_pow_val]⟩

theorem eigenvalue_product_eq
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    ∃ (u : (𝓞 K)ˣ) (M : ℕ),
      ∏ j : ZMod (2 ^ (k + 1)), eigenvalueOI H (hζ.toInteger) j =
        ↑u * (hζ.toInteger - 1) ^ M := by

  obtain ⟨s, hs_sq, hprod⟩ := prod_eigenvalueOI_eq_pm_pow k K hζ H

  obtain ⟨v, M, hv⟩ := algebraMap_two_pow_eq_unit_mul_zeta_sub_one_pow k K hζ ((k + 1) * 2 ^ k)

  have hs_unit : IsUnit (algebraMap ℤ (𝓞 K) s) := by
    have : s = 1 ∨ s = -1 := by
      have : s * s = 1 := by nlinarith [hs_sq]
      exact mul_self_eq_one_iff.mp this
    rcases this with rfl | rfl <;> simp [isUnit_one, map_neg, map_one]
  rw [hprod, map_mul, map_pow, hv]
  exact ⟨hs_unit.unit * v, M, by rw [Units.val_mul, IsUnit.unit_spec]; ring⟩

theorem circulantHadamard_eigenvalue_factorization
    (H : CirculantHadamardMatrix (2 ^ (k + 1)))
    (j : ZMod (2 ^ (k + 1))) :
    ∃ (h_j : ℕ) (v_j : (𝓞 K)ˣ),
      eigenvalueOI H (hζ.toInteger) j = ↑v_j * (hζ.toInteger - 1) ^ h_j := by
  obtain ⟨u_prod, M, hprod⟩ := eigenvalue_product_eq k K hζ H
  have hprime := CirculantHadamard.zeta_sub_one_prime_two_pow k K hζ
  have hprime_ne_zero : (hζ.toInteger - 1 : 𝓞 K) ≠ 0 := hprime.ne_zero
  have hprod_ne : ∏ j : ZMod (2 ^ (k + 1)), eigenvalueOI H (hζ.toInteger) j ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero (Units.ne_zero u_prod) (pow_ne_zero M hprime_ne_zero)
  have hj_ne : eigenvalueOI H (hζ.toInteger) j ≠ 0 := by
    intro h
    exact hprod_ne (Finset.prod_eq_zero (Finset.mem_univ j) h)
  haveI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  have hfin : FiniteMultiplicity (hζ.toInteger - 1) (eigenvalueOI H (hζ.toInteger) j) :=
    FiniteMultiplicity.of_prime_left hprime hj_ne
  obtain ⟨c, hc_eq, hc_ndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd

  have hc_dvd_prod : c ∣ ↑u_prod * (hζ.toInteger - 1) ^ M := by
    rw [← hprod]
    calc c ∣ (hζ.toInteger - 1) ^
              multiplicity (hζ.toInteger - 1) (eigenvalueOI H (hζ.toInteger) j) * c :=
            dvd_mul_left c _
      _ = eigenvalueOI H (hζ.toInteger) j := hc_eq.symm
      _ ∣ ∏ j' : ZMod (2 ^ (k + 1)), eigenvalueOI H (hζ.toInteger) j' :=
            Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

  have hc_dvd_u : c ∣ (↑u_prod : 𝓞 K) :=
    dvd_of_dvd_mul_prime_pow_right hprime hc_ndvd M hc_dvd_prod
  have hc_unit : IsUnit c := isUnit_of_dvd_unit hc_dvd_u u_prod.isUnit
  set h := multiplicity (hζ.toInteger - 1) (eigenvalueOI H (hζ.toInteger) j)
  exact ⟨h, hc_unit.unit, by rw [hc_eq, hc_unit.unit_spec, mul_comm]⟩

lemma unit_mul_pow_dvd_unit_mul_pow {R : Type*} [CommMonoidWithZero R]
    (v₀ v₁ : Rˣ) (p : R) {h₀ h₁ : ℕ} (h_le : h₀ ≤ h₁) :
    ↑v₀ * p ^ h₀ ∣ ↑v₁ * p ^ h₁ :=
  (v₀.isUnit.mul_left_dvd).mpr ((v₁.isUnit.dvd_mul_left).mpr (pow_dvd_pow p h_le))

theorem circulantHadamard_eigenvalue_ratio_integral
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    eigenvalueOI H (hζ.toInteger) 1 ∣ eigenvalueOI H (hζ.toInteger) 0 ∨
    eigenvalueOI H (hζ.toInteger) 0 ∣ eigenvalueOI H (hζ.toInteger) 1 := by

  obtain ⟨h₀, v₀, hγ₀⟩ := circulantHadamard_eigenvalue_factorization k K hζ H 0
  obtain ⟨h₁, v₁, hγ₁⟩ := circulantHadamard_eigenvalue_factorization k K hζ H 1

  rcases le_total h₀ h₁ with h_le | h_le
  ·
    right
    rw [hγ₀, hγ₁]
    exact unit_mul_pow_dvd_unit_mul_pow v₀ v₁ _ h_le
  ·
    left
    rw [hγ₀, hγ₁]
    exact unit_mul_pow_dvd_unit_mul_pow v₁ v₀ _ h_le

end EigenvalueFactorization

section RootOfUnityPower

open Polynomial

lemma root_of_unity_eq_pow_zeta (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {x : K} (hx : IsOfFinOrder x) :
    ∃ (i : ℕ), x = ζ ^ i := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  obtain ⟨m, hm_pos, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  obtain ⟨l, hl_mem, hl_root⟩ := (isRoot_of_unity_iff hm_pos K).mp hm
  have hl_ne : l ≠ 0 := by intro h; rw [h] at hl_mem; simp at hl_mem
  haveI : NeZero l := ⟨hl_ne⟩
  rw [isRoot_cyclotomic_iff] at hl_root
  have hl_dvd2 := hl_root.dvd_of_isCyclotomicExtension (2 ^ (k + 1)) hl_ne
  rw [show 2 * 2 ^ (k + 1) = 2 ^ (k + 2) from by ring] at hl_dvd2
  suffices hxn : x ^ (2 ^ (k + 1)) = 1 by
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hxn
    exact ⟨i, hi.symm⟩
  suffices l ∣ 2 ^ (k + 1) by
    obtain ⟨q, hq⟩ := this
    rw [hq, pow_mul, hl_root.pow_eq_one, one_pow]
  by_contra h_not_dvd
  have hl_eq : l = 2 ^ (k + 2) := by
    obtain ⟨a, ha_le, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hl_dvd2
    congr 1; by_contra h
    exact h_not_dvd (Nat.pow_dvd_pow 2 (by omega : a ≤ k + 1))
  rw [hl_eq] at hl_root
  have hfin := IsCyclotomicExtension.finrank K
    (cyclotomic.irreducible_rat (show 0 < 2 ^ (k + 1) by positivity))
  have h_le : Nat.totient (2 ^ (k + 2)) ≤ Module.finrank ℚ K := by
    haveI : NeZero (2 ^ (k + 2) : ℕ) := ⟨by positivity⟩
    have h_lcm_eq : Nat.lcm (2 ^ (k + 2)) (2 ^ (k + 1)) = 2 ^ (k + 2) := by
      rw [Nat.lcm_comm]; exact Nat.lcm_eq_right (Nat.pow_dvd_pow 2 (by omega))
    have := hl_root.lcm_totient_le_finrank
      (IsCyclotomicExtension.zeta_spec (2 ^ (k + 1)) ℚ K)
      (cyclotomic.irreducible_rat (by positivity : 0 < Nat.lcm (2 ^ (k + 2)) (2 ^ (k + 1))))
    rwa [h_lcm_eq] at this
  have h1 : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) := by
    simp [Nat.totient_prime_pow_succ Nat.prime_two]
  have h2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    simp [Nat.totient_prime_pow_succ Nat.prime_two]
  rw [h1, hfin, h2] at h_le
  exact absurd h_le (Nat.not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))

lemma root_of_unity_eq_pm_zeta_pow (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (u : (𝓞 K)ˣ) (hu : ∃ m : ℕ, m > 0 ∧ (u : 𝓞 K) ^ m = 1) :
    ∃ (r : ℤ) (s : ℤ), s^2 = 1 ∧ (u : 𝓞 K) = algebraMap ℤ (𝓞 K) s * hζ.toInteger ^ r.natAbs := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  have hu_field : IsOfFinOrder ((algebraMap (𝓞 K) K) ↑u : K) := by
    obtain ⟨m, hm_pos, hm⟩ := hu
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm_pos, by rw [← map_pow, hm, map_one]⟩
  obtain ⟨i, hi⟩ := root_of_unity_eq_pow_zeta k K hζ hu_field
  refine ⟨(i : ℤ), 1, by norm_num, ?_⟩
  simp only [one_mul, map_one, Int.natAbs_natCast]
  have hζ_val : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := RingOfIntegers.map_mk ζ _
  ext
  change (algebraMap (𝓞 K) K) (↑u) = (algebraMap (𝓞 K) K) (hζ.toInteger ^ i)
  rw [map_pow, hζ_val, hi]

end RootOfUnityPower

section EigenvalueRatio

open Ideal NumberField RingOfIntegers IsCyclotomicExtension.Rat

lemma eigenvalueOI_map_eq_eigenvalue {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K]
    (H : CirculantHadamardMatrix n) (ζ_int : 𝓞 K)
    (σ : K →+* ℂ) (j : ZMod n) :
    σ ((algebraMap (𝓞 K) K) (eigenvalueOI H ζ_int j)) =
      H.eigenvalue (σ ((algebraMap (𝓞 K) K) ζ_int)) j := by
  simp only [eigenvalueOI, CirculantHadamardMatrix.eigenvalue]
  rw [map_sum (algebraMap (𝓞 K) K), map_sum σ]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, map_pow]
  congr 1
  rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  change (σ.comp (algebraMap ℤ K)) (H.a i) = (Int.castRingHom ℂ) (H.a i)
  exact DFunLike.congr_fun (RingHom.ext_int _ _) _

lemma dvd_ratio_isRootOfUnity
    (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {a b : 𝓞 K} (hdvd : a ∣ b)
    (ha : ∀ (σ : K →+* ℂ), ‖σ ((algebraMap (𝓞 K) K) a)‖ = Real.sqrt (2 ^ (k + 1)))
    (hb : ∀ (σ : K →+* ℂ), ‖σ ((algebraMap (𝓞 K) K) b)‖ = Real.sqrt (2 ^ (k + 1))) :
    ∃ (r : ℤ) (s : ℤ), s ^ 2 = 1 ∧
      b = algebraMap ℤ (𝓞 K) s * hζ.toInteger ^ r.natAbs * a := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩

  obtain ⟨c, hc⟩ := hdvd

  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hc_norm : ‖σ₀ ((algebraMap (𝓞 K) K) c)‖ = 1 := by
    have ha₀ := ha σ₀
    have hb₀ := hb σ₀
    have hc_eq : σ₀ ((algebraMap (𝓞 K) K) b) =
        σ₀ ((algebraMap (𝓞 K) K) a) * σ₀ ((algebraMap (𝓞 K) K) c) := by
      rw [hc, map_mul, map_mul]
    rw [hc_eq, Complex.norm_mul, ha₀] at hb₀

    have hsqrt_ne : Real.sqrt (2 ^ (k + 1)) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by positivity)
    exact mul_left_cancel₀ hsqrt_ne (hb₀.trans (mul_one _).symm)

  have hc_int : IsIntegral ℤ ((algebraMap (𝓞 K) K) c) := c.2

  obtain ⟨m, hm_pos, hm⟩ := kronecker_isRootOfUnity_of_cyclotomic
    (n := 2 ^ (k + 1)) hc_int σ₀ hc_norm

  have hm_oi : c ^ m = 1 := by
    have : ((c ^ m : 𝓞 K) : K) = ((1 : 𝓞 K) : K) := by
      push_cast; exact hm
    exact_mod_cast this

  have hc_isunit : IsUnit c := IsUnit.of_pow_eq_one hm_oi hm_pos.ne'

  set u := hc_isunit.unit
  have hu_spec : (u : 𝓞 K) = c := IsUnit.unit_spec hc_isunit

  have hu_pow : (u : 𝓞 K) ^ m = 1 := by rw [hu_spec]; exact hm_oi

  obtain ⟨r, s, hs, hu_eq⟩ :=
    root_of_unity_eq_pm_zeta_pow k K hζ u ⟨m, hm_pos, hu_pow⟩


  refine ⟨r, s, hs, ?_⟩
  rw [hc]
  have : c = algebraMap ℤ (𝓞 K) s * hζ.toInteger ^ r.natAbs := by rw [← hu_spec]; exact hu_eq
  rw [this]; ring

theorem eigenvalue_ratio_eq_pm_zeta_pow
    (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    ∃ (r : ℤ) (s : ℤ), s ^ 2 = 1 ∧
      eigenvalueOI H (hζ.toInteger) 0 =
        algebraMap ℤ (𝓞 K) s * hζ.toInteger ^ r.natAbs *
        eigenvalueOI H (hζ.toInteger) 1 := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩

  have habs : ∀ (j : ZMod (2 ^ (k + 1))) (σ : K →+* ℂ),
      ‖σ ((algebraMap (𝓞 K) K) (eigenvalueOI H (hζ.toInteger) j))‖ =
        Real.sqrt (2 ^ (k + 1)) := by
    intro j σ
    rw [eigenvalueOI_map_eq_eigenvalue]
    rw [show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from RingOfIntegers.map_mk ζ _]
    have := circulantHadamard_eigenvalue_abs H (σ ζ) (hζ.map_of_injective σ.injective) j
    simp only [Nat.cast_pow, Nat.cast_ofNat] at this
    exact this

  rcases circulantHadamard_eigenvalue_ratio_integral k K hζ H with h1 | h2
  ·
    exact dvd_ratio_isRootOfUnity k K hζ h1 (habs 1) (habs 0)
  ·

    obtain ⟨r', s', hs', heq'⟩ := dvd_ratio_isRootOfUnity k K hζ h2 (habs 0) (habs 1)


    obtain ⟨c, hc_dvd⟩ := h2


    have hs'_val : s' = 1 ∨ s' = -1 := by
      have : s' * s' = 1 := by nlinarith [hs']
      rcases mul_self_eq_one_iff.mp this with h | h <;> [left; right] <;> exact h

    have hs'_unit : IsUnit (algebraMap ℤ (𝓞 K) s') := by
      rcases hs'_val with rfl | rfl
      · simp [isUnit_one]
      · rw [map_neg, map_one]; exact IsUnit.neg isUnit_one

    have hζ_unit : IsUnit hζ.toInteger := by
      have : hζ.toInteger ^ (2 ^ (k + 1)) = 1 := by
        have : ((hζ.toInteger ^ (2 ^ (k + 1)) : 𝓞 K) : K) = ((1 : 𝓞 K) : K) := by
          push_cast [RingOfIntegers.map_mk]; exact hζ.pow_eq_one
        exact_mod_cast this
      exact IsUnit.of_pow_eq_one this (by positivity)

    have hmul_unit : IsUnit (algebraMap ℤ (𝓞 K) s' * hζ.toInteger ^ r'.natAbs) :=
      IsUnit.mul hs'_unit (IsUnit.pow _ hζ_unit)


    set w := hmul_unit.unit
    have hw_spec : (w : 𝓞 K) = algebraMap ℤ (𝓞 K) s' * hζ.toInteger ^ r'.natAbs :=
      IsUnit.unit_spec hmul_unit

    have hγ₁_eq : eigenvalueOI H (hζ.toInteger) 1 = w * eigenvalueOI H (hζ.toInteger) 0 := by
      change _ = (w : 𝓞 K) * _
      rw [hw_spec, heq']

    have hγ₀_eq : eigenvalueOI H (hζ.toInteger) 0 =
        (↑w⁻¹ : 𝓞 K) * eigenvalueOI H (hζ.toInteger) 1 := by
      have := Units.inv_mul w
      calc eigenvalueOI H (hζ.toInteger) 0
          = 1 * eigenvalueOI H (hζ.toInteger) 0 := (one_mul _).symm
        _ = (↑w⁻¹ * ↑w) * eigenvalueOI H (hζ.toInteger) 0 := by
            rw [show (↑w⁻¹ : 𝓞 K) * ↑w = 1 from this]
        _ = ↑w⁻¹ * (↑w * eigenvalueOI H (hζ.toInteger) 0) := by ring
        _ = ↑w⁻¹ * eigenvalueOI H (hζ.toInteger) 1 := by rw [← hγ₁_eq]


    have hw_pow : ∃ m : ℕ, m > 0 ∧ (↑(w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ m = 1 := by


      refine ⟨2 ^ (k + 1), by positivity, ?_⟩
      have hw_pow_eq : (w : 𝓞 K) ^ (2 ^ (k + 1)) = 1 := by
        rw [hw_spec]
        have hs'_pow : (algebraMap ℤ (𝓞 K) s') ^ (2 ^ (k + 1)) = 1 := by
          rcases hs'_val with rfl | rfl
          · simp
          · rw [map_neg, map_one]
            have : (-1 : 𝓞 K) ≠ 1 := by
              have : (algebraMap (𝓞 K) K) (-1) ≠ (algebraMap (𝓞 K) K) 1 := by
                simp; norm_num
              exact fun h => this (congr_arg (algebraMap (𝓞 K) K) h)
            rw [neg_one_pow_eq_one_iff_even this]
            exact ⟨2 ^ k, by ring⟩
        have hζ_root : hζ.toInteger ^ (2 ^ (k + 1)) = 1 := by
          have : ((hζ.toInteger ^ (2 ^ (k + 1)) : 𝓞 K) : K) = ((1 : 𝓞 K) : K) := by
            push_cast [RingOfIntegers.map_mk]; exact hζ.pow_eq_one
          exact_mod_cast this
        have hζ_pow : (hζ.toInteger ^ r'.natAbs) ^ (2 ^ (k + 1)) = 1 := by
          rw [← pow_mul, show r'.natAbs * 2 ^ (k + 1) = 2 ^ (k + 1) * r'.natAbs from by ring,
            pow_mul, hζ_root, one_pow]
        rw [mul_pow, hs'_pow, hζ_pow, mul_one]
      rw [← Units.val_pow_eq_pow_val, inv_pow]
      have hw_unit_pow : w ^ (2 ^ (k + 1)) = (1 : (𝓞 K)ˣ) :=
        Units.val_injective (by simp only [Units.val_pow_eq_pow_val, Units.val_one]; exact hw_pow_eq)
      rw [hw_unit_pow, inv_one, Units.val_one]
    obtain ⟨r'', s'', hs'', hu_inv_eq⟩ :=
      root_of_unity_eq_pm_zeta_pow k K hζ w⁻¹ hw_pow
    exact ⟨r'', s'', hs'', by rw [hγ₀_eq, hu_inv_eq]⟩

end EigenvalueRatio

namespace CirculantHadamardMatrix

variable {n : ℕ} [NeZero n]

lemma sum_sq_eq (H : CirculantHadamardMatrix n) :
    (∑ i : ZMod n, H.a i) ^ 2 = (n : ℤ) := by
  rw [sq, Fintype.sum_mul_sum]
  have step : ∀ i : ZMod n,
      ∑ j : ZMod n, H.a i * H.a j =
      ∑ d : ZMod n, H.a i * H.a (i + d) := fun i =>
    (Equiv.sum_comp (Equiv.addLeft i) (fun j => H.a i * H.a j)).symm
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [H.orthogonality]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

end CirculantHadamardMatrix

section EigenvalueZero

open Ideal NumberField RingOfIntegers IsCyclotomicExtension.Rat

variable (k : ℕ) (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))

omit [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] in
lemma eigenvalue_zero_eq_sum
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    eigenvalueOI H (hζ.toInteger) 0 =
      algebraMap ℤ (𝓞 K) (∑ i : ZMod (2 ^ (k + 1)), H.a i) := by
  unfold eigenvalueOI
  simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one]
  rw [map_sum]

end EigenvalueZero

section EigenvalueOneExpand

open Ideal NumberField RingOfIntegers IsCyclotomicExtension.Rat

lemma sum_zmod_split_halves (k : ℕ) [NeZero (2 ^ (k+1))] (R : Type*) [AddCommGroup R]
    (f : ZMod (2 ^ (k+1)) → R) (gLo gHi : ℕ → R)
    (hlo : ∀ j ∈ Finset.range (2^k), f (j : ZMod (2^(k+1))) = gLo j)
    (hhi : ∀ j ∈ Finset.range (2^k), f ((j + 2^k : ℕ) : ZMod (2^(k+1))) = gHi j) :
    ∑ x : ZMod (2 ^ (k+1)), f x =
    (∑ j ∈ Finset.range (2^k), gLo j) + (∑ j ∈ Finset.range (2^k), gHi j) := by
  have hpow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hsplit : ∑ x : ZMod (2 ^ (k+1)), f x =
      (∑ x ∈ Finset.univ.filter (fun x : ZMod _ => x.val < 2^k), f x) +
      (∑ x ∈ Finset.univ.filter (fun x : ZMod _ => ¬(x.val < 2^k)), f x) := by
    rw [← Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _),
        Finset.filter_union_filter_not_eq]
  rw [hsplit]; congr 1
  · apply Finset.sum_nbij' (fun (x : ZMod _) => x.val) (fun j => (j : ZMod _))
    · intro x hx; exact Finset.mem_range.mpr ((Finset.mem_filter.mp hx).2)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at *
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (by linarith)]
    · intro x _; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by linarith)]
    · intro x hx
      conv_lhs => rw [show x = (↑x.val : ZMod _) from by
        simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]]
      exact hlo x.val (Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
  · apply Finset.sum_nbij' (fun (x : ZMod _) => x.val - 2^k)
      (fun j => ((j + 2^k : ℕ) : ZMod _))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Finset.mem_range] at hx ⊢
      have := ZMod.val_lt x; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Finset.mem_range] at *
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by linarith)]; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
      rw [Nat.sub_add_cancel hx]
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by linarith)]; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
      have hmem : x.val - 2^k ∈ Finset.range (2^k) :=
        Finset.mem_range.mpr (by have := ZMod.val_lt x; omega)
      have heq : (↑(x.val - 2^k + 2^k) : ZMod (2^(k+1))) = (↑x.val : ZMod _) := by
        rw [Nat.sub_add_cancel hx]
      rw [show f x = f (↑x.val : ZMod _) from by
        simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]]
      rw [← heq]
      exact hhi _ hmem

theorem eigenvalueOI_one_expanded (k : ℕ)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    eigenvalueOI H (hζ.toInteger) 1 = ∑ j ∈ Finset.range (2 ^ k),
      algebraMap ℤ (𝓞 K) (H.a (j : ZMod (2 ^ (k + 1))) -
        H.a ((j : ZMod (2 ^ (k + 1))) + (2 ^ k : ℕ))) *
      hζ.toInteger ^ j := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  simp only [eigenvalueOI, mul_one]
  have hζ_neg : hζ.toInteger ^ 2 ^ k = -1 := zeta_pow_half_eq_neg_one k (K := K) hζ
  have hpow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  rw [sum_zmod_split_halves k _ _
    (fun j => algebraMap ℤ (𝓞 K) (H.a (↑j : ZMod _)) * hζ.toInteger ^ j)
    (fun j => -(algebraMap ℤ (𝓞 K) (H.a ((↑j : ZMod _) + ↑(2^k))) * hζ.toInteger ^ j))]
  ·
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [map_sub, sub_mul]; push_cast; ring
  ·
    intro j hj; rw [Finset.mem_range] at hj
    congr 1; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by linarith)]
  ·
    intro j hj; rw [Finset.mem_range] at hj
    have hlt : j + 2 ^ k < 2 ^ (k + 1) := by linarith
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    conv_lhs => arg 2; rw [show j + 2 ^ k = 2 ^ k + j from by ring, pow_add, hζ_neg]
    simp only [neg_mul]
    push_cast; ring

end EigenvalueOneExpand

lemma integralPowerBasis_coeff_zero {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (m : ℤ) (c : ℕ → ℤ)
    (heq : ∑ j ∈ Finset.range (hζ.integralPowerBasis.dim),
      algebraMap ℤ (𝓞 K) (c j) * hζ.toInteger ^ j = algebraMap ℤ (𝓞 K) m) :
    c 0 = m := by
  set pb := hζ.integralPowerBasis
  have hgen : pb.gen = hζ.toInteger := hζ.integralPowerBasis_gen
  have hdim_pos : 0 < pb.dim := by
    rw [hζ.integralPowerBasis_dim]; exact Nat.totient_pos.mpr (NeZero.pos n)
  simp_rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← hgen] at heq
  rw [show (1 : 𝓞 K) = pb.basis ⟨0, hdim_pos⟩ from by rw [pb.basis_eq_pow]; simp] at heq
  have h0 := congr_fun (congr_arg DFunLike.coe
    (pb.basis.repr.injective.eq_iff.mpr heq)) ⟨0, hdim_pos⟩
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one,
      map_sum, Finsupp.finset_sum_apply] at h0
  simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h0
  have key : ∀ x ∈ Finset.range pb.dim,
      c x * (pb.basis.repr (pb.gen ^ x)) ⟨0, hdim_pos⟩ =
      if x = 0 then c 0 else 0 := by
    intro j hj
    rw [← pb.basis_eq_pow ⟨j, Finset.mem_range.mp hj⟩, Module.Basis.repr_self,
        Finsupp.single_apply]
    by_cases h : (⟨j, Finset.mem_range.mp hj⟩ : Fin pb.dim) = ⟨0, hdim_pos⟩
    · have hj0 : j = 0 := Fin.ext_iff.mp h; subst hj0; simp
    · have hne : j ≠ 0 := fun h0 => h (Fin.ext h0)
      simp [h, hne]
  rw [Finset.sum_congr rfl key,
    Finset.sum_ite_eq' _ 0 _, if_pos (Finset.mem_range.mpr hdim_pos)] at h0
  exact h0

lemma zeta_pow_mul_sum_eq_reindexed_sum
    (n : ℕ) (hn : 0 < n) {α : Type*} [CommRing α]
    (x : α) (hx : x ^ n = -1) (r : ℕ) (hr : r < n)
    (c : ℕ → α) :
    x ^ r * ∑ j ∈ Finset.range n, c j * x ^ j =
    ∑ i ∈ Finset.range n,
      (if r ≤ i then c (i - r) else -(c (n + i - r))) * x ^ i := by
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, mul_comm (x ^ r), mul_assoc, ← pow_add]
  refine Finset.sum_nbij' (fun j => (j + r) % n) (fun i => if r ≤ i then i - r else n + i - r)
    ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; split_ifs with hri <;> omega
  · intro j hj; simp only [Finset.mem_range] at hj; dsimp only
    by_cases hjr : j + r < n
    · simp only [Nat.mod_eq_of_lt hjr, show r ≤ j + r from Nat.le_add_left _ _, ↓reduceIte]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [show ¬(r ≤ j + r - n) from by omega, ↓reduceIte]; omega
  · intro i hi; simp only [Finset.mem_range] at hi; dsimp only
    split_ifs with hri
    · rw [Nat.sub_add_cancel hri, Nat.mod_eq_of_lt hi]
    · rw [show n + i - r + r = n + i from by omega,
          show n + i = i + n from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · intro j hj; simp only [Finset.mem_range] at hj; dsimp only
    by_cases hjr : j + r < n
    · simp only [Nat.mod_eq_of_lt hjr, show r ≤ j + r from Nat.le_add_left _ _, ↓reduceIte]
      rw [show j + r - r = j from by omega]; congr 1; ring
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [show ¬(r ≤ j + r - n) from by omega, ↓reduceIte]
      rw [show n + (j + r - n) - r = j from by omega]
      have : x ^ (r + j) = -(x ^ (j + r - n)) := by
        calc x ^ (r + j) = x ^ (n + (j + r - n)) := by congr 1; omega
          _ = x ^ n * x ^ (j + r - n) := pow_add x n (j + r - n)
          _ = -x ^ (j + r - n) := by rw [hx]; ring
      rw [this]; ring

theorem power_basis_coeff_extraction
    (k : ℕ) (_hk : 2 ≤ k)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (H : CirculantHadamardMatrix (2 ^ (k + 1)))
    (R : ℕ) (s_int : ℤ) (hs : s_int ^ 2 = 1)
    (h_eq : algebraMap ℤ (𝓞 K) (∑ i : ZMod (2 ^ (k + 1)), H.a i) =
        algebraMap ℤ (𝓞 K) s_int * hζ.toInteger ^ R *
        eigenvalueOI H (hζ.toInteger) 1) :
    ∃ s : ZMod (2 ^ (k + 1)),
      ∑ i : ZMod (2 ^ (k + 1)), H.a i = H.a s - H.a (s + (2 ^ k : ℕ)) := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  rw [eigenvalueOI_one_expanded k hζ H] at h_eq
  have hdim : hζ.integralPowerBasis.dim = 2 ^ k := by
    rw [hζ.integralPowerBasis_dim, Nat.totient_prime_pow_succ Nat.prime_two]; simp
  have hζ_neg : hζ.toInteger ^ (2 ^ k) = -1 := zeta_pow_half_eq_neg_one k (K := K) hζ
  have hs_val : s_int = 1 ∨ s_int = -1 := sq_eq_one_iff.mp hs
  have hkpos : 0 < 2 ^ k := by positivity

  set r := R % (2 ^ k)
  set q := R / (2 ^ k)
  have hr_lt : r < 2 ^ k := Nat.mod_lt _ hkpos
  have hζR : hζ.toInteger ^ R = (-1 : 𝓞 K) ^ q * hζ.toInteger ^ r := by
    conv_lhs => rw [show R = 2 ^ k * q + r from by
      simp only [r, q]; rw [Nat.div_add_mod]]
    rw [pow_add, pow_mul, hζ_neg]
  rw [hζR] at h_eq

  set σ : ℤ := s_int * (-1) ^ q
  have hσ_val : σ = 1 ∨ σ = -1 := by
    have : σ ^ 2 = 1 := by
      simp only [σ]; rw [mul_pow, hs, ← pow_mul, mul_comm]; simp
    exact sq_eq_one_iff.mp this

  have h_eq2 : algebraMap ℤ (𝓞 K) (∑ i : ZMod (2 ^ (k + 1)), H.a i) =
      hζ.toInteger ^ r *
      ∑ j ∈ Finset.range (2 ^ k),
        algebraMap ℤ (𝓞 K) (σ * (H.a (j : ZMod (2 ^ (k + 1))) -
          H.a ((j : ZMod (2 ^ (k + 1))) + (2 ^ k : ℕ)))) *
        hζ.toInteger ^ j := by
    rw [h_eq]; simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    push_cast [σ]; ring

  rw [zeta_pow_mul_sum_eq_reindexed_sum (2 ^ k) hkpos hζ.toInteger hζ_neg r hr_lt] at h_eq2

  let d : ℕ → ℤ := fun j => σ * (H.a (j : ZMod (2 ^ (k + 1))) -
      H.a ((j : ZMod (2 ^ (k + 1))) + (2 ^ k : ℕ)))
  let c : ℕ → ℤ := fun i => if r ≤ i then d (i - r) else -(d (2 ^ k + i - r))

  have h_pb : ∑ i ∈ Finset.range (hζ.integralPowerBasis.dim),
      algebraMap ℤ (𝓞 K) (c i) * hζ.toInteger ^ i =
      algebraMap ℤ (𝓞 K) (∑ i : ZMod (2 ^ (k + 1)), H.a i) := by
    rw [hdim]
    conv_lhs => arg 2; ext i; rw [show algebraMap ℤ (𝓞 K) (c i) = (if r ≤ i then
        algebraMap ℤ (𝓞 K) (d (i - r)) else
        -(algebraMap ℤ (𝓞 K) (d (2 ^ k + i - r)))) from by
      simp only [c, apply_ite (algebraMap ℤ (𝓞 K)), map_neg]]
    exact h_eq2.symm
  have h0 := integralPowerBasis_coeff_zero hζ (∑ i : ZMod (2 ^ (k + 1)), H.a i) c h_pb

  have hc0 : c 0 = if r = 0 then d 0 else -(d (2 ^ k - r)) := by
    simp only [c]
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp only [show ¬(r ≤ 0) from by omega, ↓reduceIte,
                  show 2 ^ k + 0 - r = 2 ^ k - r from by omega]
      simp [hr0]
  rw [hc0] at h0
  have h2k : ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by
    rw [← Nat.cast_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) from by ring]
    exact ZMod.natCast_self _
  by_cases hr0 : r = 0
  · simp only [hr0, ↓reduceIte, d] at h0
    rcases hσ_val with hσ1 | hσ_neg1
    · rw [hσ1, one_mul] at h0
      exact ⟨(↑(0 : ℕ) : ZMod _), h0.symm⟩
    · rw [hσ_neg1, neg_one_mul, neg_sub] at h0
      refine ⟨(2 ^ k : ℕ), ?_⟩
      convert h0.symm using 2 <;> congr 1
      · simp
      · exact_mod_cast h2k
  · simp only [hr0, ↓reduceIte, d] at h0
    rcases hσ_val with hσ1 | hσ_neg1
    · rw [hσ1, one_mul, neg_sub] at h0
      refine ⟨((2 ^ k - r + 2 ^ k : ℕ) : ZMod _), ?_⟩
      convert h0.symm using 3
      · rw [show (2 ^ k - r + 2 ^ k : ℕ) = (2 ^ k - r) + 2 ^ k from by omega, Nat.cast_add]
      · rw [show (2 ^ k - r + 2 ^ k : ℕ) = (2 ^ k - r) + 2 ^ k from by omega, Nat.cast_add,
            add_assoc, h2k, add_zero]
    · rw [hσ_neg1, neg_one_mul, neg_neg] at h0
      exact ⟨((2 ^ k - r : ℕ) : ZMod _), h0.symm⟩

theorem coeff_extraction_from_eigenvalue_divisibility
    (k : ℕ) (hk : 2 ≤ k)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (H : CirculantHadamardMatrix (2 ^ (k + 1)))
    (_h_div : eigenvalueOI H (hζ.toInteger) 1 ∣ eigenvalueOI H (hζ.toInteger) 0 ∨
             eigenvalueOI H (hζ.toInteger) 0 ∣ eigenvalueOI H (hζ.toInteger) 1) :
    ∃ s : ZMod (2 ^ (k + 1)),
      ∑ i : ZMod (2 ^ (k + 1)), H.a i = H.a s - H.a (s + (2 ^ k : ℕ)) := by
  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩

  obtain ⟨R_int, s_int, hs_sq, h_ratio⟩ := eigenvalue_ratio_eq_pm_zeta_pow k K hζ H

  rw [eigenvalue_zero_eq_sum k K hζ H] at h_ratio

  exact power_basis_coeff_extraction k hk hζ H R_int.natAbs s_int hs_sq h_ratio

theorem exists_sum_eq_diff (k : ℕ) (hk : 2 ≤ k)
    (H : CirculantHadamardMatrix (2 ^ (k + 1))) :
    ∃ r : ZMod (2 ^ (k + 1)),
      ∑ i : ZMod (2 ^ (k + 1)), H.a i = H.a r - H.a (r + (2 ^ k : ℕ)) := by

  haveI : NeZero (2 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  set K := CyclotomicField (2 ^ (k + 1)) ℚ
  haveI : NumberField K := CyclotomicField.instNumberField _ _
  haveI : IsCyclotomicExtension {2 ^ (k + 1)} ℚ K :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero _ _
  set ζ := IsCyclotomicExtension.zeta (2 ^ (k + 1)) ℚ K
  have hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)) := IsCyclotomicExtension.zeta_spec _ _ _

  have h_ratio := circulantHadamard_eigenvalue_ratio_integral k K hζ H
  exact coeff_extraction_from_eigenvalue_divisibility k hk hζ H h_ratio

theorem no_circulant_hadamard_pow_two (k : ℕ) (hk : 3 ≤ k) :
    IsEmpty (CirculantHadamardMatrix (2 ^ k)) := by
  constructor
  intro H
  have hk' : 2 ≤ k - 1 := by omega
  have hkn : k = (k - 1) + 1 := by omega
  rw [hkn] at H
  obtain ⟨r, hr⟩ := exists_sum_eq_diff (k - 1) hk' H
  have hsq := H.sum_sq_eq
  rw [hr] at hsq
  have h1 := H.entries_sq r
  have h2 := H.entries_sq (r + (2 ^ (k - 1) : ℕ))
  have hle : (H.a r - H.a (r + (2 ^ (k - 1) : ℕ))) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (H.a r + H.a (r + (2 ^ (k - 1) : ℕ)))]
  have hpow : (8 : ℤ) ≤ ↑(2 ^ ((k - 1) + 1) : ℕ) := by
    have : 8 ≤ 2 ^ ((k - 1) + 1) := le_trans (by norm_num : 8 ≤ 2 ^ 3)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this
  linarith
