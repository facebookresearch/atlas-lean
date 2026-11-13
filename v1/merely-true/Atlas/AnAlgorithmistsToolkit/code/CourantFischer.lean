/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Matrix Finset BigOperators

namespace CourantFischer

lemma eucl_inner_eq_dotProduct {V : Type*} [Fintype V]
    (a b : EuclideanSpace ℝ V) :
    @inner ℝ _ _ a b = dotProduct a.ofLp b.ofLp := by
  have h := EuclideanSpace.inner_eq_star_dotProduct a b
  rw [star_trivial] at h
  rw [dotProduct_comm a.ofLp b.ofLp]; exact h

variable {m : ℕ} [NeZero m]
variable {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)

omit [NeZero m] in
theorem rayleigh_spectral_expansion (x : Fin m → ℝ) :
    dotProduct x (A.mulVec x) =
      ∑ i : Fin m, hA.eigenvalues i *
        (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 := by
  have htrans : Aᵀ = A := by
    ext i j
    have := congr_fun (congr_fun hA i) j
    simp [conjTranspose, star] at this
    exact this
  have key : dotProduct x (A.mulVec x) =
      ∑ i, dotProduct x (⇑(hA.eigenvectorBasis i)) *
        dotProduct (⇑(hA.eigenvectorBasis i)) (A.mulVec x) := by
    have h := hA.eigenvectorBasis.sum_inner_mul_inner
      (WithLp.toLp (p := 2) x) (WithLp.toLp (p := 2) (A.mulVec x))
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
    simpa [dotProduct_comm] using h.symm
  rw [key]
  congr 1
  ext i
  have hmul : dotProduct (⇑(hA.eigenvectorBasis i)) (A.mulVec x) =
      hA.eigenvalues i * dotProduct (⇑(hA.eigenvectorBasis i)) x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, htrans, hA.mulVec_eigenvectorBasis i]
    simp only [smul_dotProduct, smul_eq_mul]
  rw [hmul, dotProduct_comm x]
  ring


omit [NeZero m] in
theorem parseval_eigenvectors (x : Fin m → ℝ) :
    ∑ i : Fin m, (dotProduct (⇑(hA.eigenvectorBasis i)) x) ^ 2 = dotProduct x x := by
  let b := hA.eigenvectorBasis
  let x' : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
  have parseval := OrthonormalBasis.sum_sq_norm_inner_right b x'
  have h_inner : ∀ i : Fin m, @inner ℝ _ _ (b i) x' = (b i).ofLp ⬝ᵥ x := by
    intro i
    show x ⬝ᵥ star (b i).ofLp = (b i).ofLp ⬝ᵥ x
    simp [star_trivial, dotProduct_comm]
  have h_norm_sq : ∀ i : Fin m, ‖@inner ℝ _ _ (b i) x'‖ ^ 2 = ((b i).ofLp ⬝ᵥ x) ^ 2 := by
    intro i
    rw [h_inner i, Real.norm_eq_abs, sq_abs]
  have h_norm_x : ‖x'‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Fintype.sum_nonneg (fun j => ?_))]
    · simp only [dotProduct]
      congr 1
      ext j
      show ‖x j‖ ^ 2 = x j * x j
      rw [Real.norm_eq_abs, sq_abs, sq]
    · positivity
  rw [h_norm_x] at parseval
  convert parseval using 1
  congr 1
  ext i
  exact (h_norm_sq i).symm




open Matrix SimpleGraph Finset BigOperators

section LaplacianRayleigh

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L : Matrix V V ℝ} (hL : L.IsHermitian)


theorem rayleigh_spectral_expansion_V (x : V → ℝ) :
    dotProduct x (L.mulVec x) =
      ∑ i : V, hL.eigenvalues i *
        (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
  set b := hL.eigenvectorBasis
  set x' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) x
  set Lx' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) (L *ᵥ x)
  have hlhs : dotProduct x (L *ᵥ x) = @inner ℝ _ _ x' Lx' := by
    rw [eucl_inner_eq_dotProduct]
  have hrhs_term : ∀ i : V, dotProduct (⇑(b i)) x = @inner ℝ _ _ (b i) x' := by
    intro i; rw [eucl_inner_eq_dotProduct]
  rw [hlhs]
  simp_rw [hrhs_term]
  rw [show @inner ℝ _ _ x' Lx' = ∑ i, @inner ℝ _ _ x' (b i) * @inner ℝ _ _ (b i) Lx' from
    (b.sum_inner_mul_inner x' Lx').symm]
  congr 1; ext i
  have h_eigval : @inner ℝ _ _ (b i) Lx' = hL.eigenvalues i * @inner ℝ _ _ (b i) x' := by
    rw [eucl_inner_eq_dotProduct, eucl_inner_eq_dotProduct]
    rw [dotProduct_mulVec]
    have hvecmul : (b i).ofLp ᵥ* L = hL.eigenvalues i • (b i).ofLp := by
      conv_lhs => rw [show L = Lᴴ from hL.symm]
      rw [vecMul_conjTranspose, star_trivial, star_trivial]
      exact hL.mulVec_eigenvectorBasis i
    rw [hvecmul, smul_dotProduct, smul_eq_mul]
  rw [h_eigval, real_inner_comm x' (b i), sq]
  ring


theorem parseval_eigenvectors_V (x : V → ℝ) :
    ∑ i : V, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 = dotProduct x x := by
  set b := hL.eigenvectorBasis
  set x' : EuclideanSpace ℝ V := WithLp.toLp (p := 2) x
  have hrhs : dotProduct x x = @inner ℝ _ _ x' x' := by rw [eucl_inner_eq_dotProduct]
  have hlhs_term : ∀ i : V, dotProduct (⇑(b i)) x = @inner ℝ _ _ (b i) x' := by
    intro i; rw [eucl_inner_eq_dotProduct]
  rw [hrhs]
  simp_rw [hlhs_term]
  trans (∑ i : V, @inner ℝ _ _ x' (b i) * @inner ℝ _ _ (b i) x')
  · apply Finset.sum_congr rfl
    intro i _
    rw [sq, ← real_inner_comm x' (b i)]
  · exact b.sum_inner_mul_inner x' x'

theorem eigenvalue_eq_rayleigh_eigenvector_V (k : V) :
    dotProduct (⇑(hL.eigenvectorBasis k))
      (L.mulVec (⇑(hL.eigenvectorBasis k))) =
    hL.eigenvalues k := by
  rw [hL.mulVec_eigenvectorBasis k]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hkey : ∀ x : V,
    (hL.eigenvectorBasis k).ofLp x * (hL.eigenvalues k * (hL.eigenvectorBasis k).ofLp x) =
    hL.eigenvalues k * ((hL.eigenvectorBasis k).ofLp x) ^ 2 := by
    intro x; ring
  simp_rw [hkey, ← Finset.mul_sum]
  have hnorm : ‖hL.eigenvectorBasis k‖ = 1 := hL.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq] at hnorm
  have hsum : ∑ x : V, ((hL.eigenvectorBasis k).ofLp x) ^ 2 = 1 := by
    have h1 := Real.sqrt_eq_one.mp hnorm
    convert h1 using 1
    congr 1
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsum, mul_one]

theorem eigenvector_dotProduct_one_V (k : V) :
    dotProduct (⇑(hL.eigenvectorBasis k)) (⇑(hL.eigenvectorBasis k)) = 1 := by
  have hn : ‖hL.eigenvectorBasis k‖ = 1 := hL.eigenvectorBasis.orthonormal.1 k
  have h1 : ‖hL.eigenvectorBasis k‖ ^ 2 = 1 := by rw [hn, one_pow]
  rw [EuclideanSpace.norm_eq] at h1
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by positivity))] at h1
  simp only [dotProduct]
  convert h1 using 1
  congr 1
  ext j
  rw [Real.norm_eq_abs, sq_abs, sq]

theorem rayleighQuotient_orthogonal_isLeast
    (k : V) :
    IsLeast
      {r | ∃ x : V → ℝ, x ≠ 0 ∧
        (∀ j : V, hL.eigenvalues j < hL.eigenvalues k →
          dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧
        dotProduct x (L.mulVec x) / dotProduct x x = r}
      (hL.eigenvalues k) := by
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis k), ?_, ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 k
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis k).ofLp i‖ ^ 2) = 0 :=
        Finset.sum_eq_zero (fun j _ => by simp [congr_fun h j])
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      intro j hj
      have hjk : j ≠ k := ne_of_apply_ne hL.eigenvalues (ne_of_lt hj)
      have h := orthonormal_iff_ite.mp hL.eigenvectorBasis.orthonormal j k
      simp only [hjk, ite_false] at h
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
      simp only [dotProduct]
      convert h using 1
      congr 1; ext i; ring
    ·
      rw [eigenvector_dotProduct_one_V hL k, div_one]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL k
  ·


    intro r ⟨x, hx, horth, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
            (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [le_div_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc hL.eigenvalues k * dotProduct x x
        = hL.eigenvalues k * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          rw [parseval_eigenvectors_V hL x]
      _ = ∑ i, hL.eigenvalues k * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : hL.eigenvalues i < hL.eigenvalues k
          · simp [horth i hi]
          · push Not at hi
            exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)

end LaplacianRayleigh

section LaplacianQuadForm

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem laplacian_quadratic_form_eq (x : V → ℝ) :
    dotProduct x ((G.lapMatrix ℝ).mulVec x) =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  have h := lapMatrix_toLinearMap₂' ℝ G x
  rw [toLinearMap₂'_apply'] at h
  exact h

theorem laplacian_edge_sum_min_characterization
    (hL : (G.lapMatrix ℝ).IsHermitian)
    (k : V) :
    IsLeast
      {r | ∃ x : V → ℝ, x ≠ 0 ∧
        (∀ j : V, hL.eigenvalues j < hL.eigenvalues k →
          dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧
        (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
          dotProduct x x = r}
      (hL.eigenvalues k) := by
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis k), ?_, ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 k
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis k).ofLp i‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show (hL.eigenvectorBasis k).ofLp j = 0 from congr_fun h j]
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      intro j hj
      have hjk : j ≠ k := by intro heq; rw [heq] at hj; exact lt_irrefl _ hj
      have h := orthonormal_iff_ite.mp hL.eigenvectorBasis.orthonormal j k
      simp only [hjk, ite_false] at h
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
      simp only [dotProduct]
      convert h using 1
      congr 1; ext i; ring
    ·
      rw [eigenvector_dotProduct_one_V hL k, div_one]
      rw [← laplacian_quadratic_form_eq]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL k
  ·
    intro r ⟨x, hx, horth, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
            (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [← laplacian_quadratic_form_eq]
    rw [le_div_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc hL.eigenvalues k * dotProduct x x
        = hL.eigenvalues k * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          rw [parseval_eigenvectors_V hL x]
      _ = ∑ i, hL.eigenvalues k * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : hL.eigenvalues i < hL.eigenvalues k
          · simp [horth i hi]
          · push Not at hi
            exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)

theorem laplacian_edge_sum_max_quotient_characterization
    (hL : (G.lapMatrix ℝ).IsHermitian)
    (i₀ : V)
    (hi₀ : ∀ j : V, hL.eigenvalues j ≤ hL.eigenvalues i₀) :
    IsGreatest
      {r | ∃ x : V → ℝ, x ≠ 0 ∧
        (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
          dotProduct x x = r}
      (hL.eigenvalues i₀) := by
  constructor
  ·
    refine ⟨⇑(hL.eigenvectorBasis i₀), ?_, ?_⟩
    ·
      intro h
      have hn := hL.eigenvectorBasis.orthonormal.1 i₀
      simp only [EuclideanSpace.norm_eq] at hn
      have : (∑ i, ‖(hL.eigenvectorBasis i₀).ofLp i‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show (hL.eigenvectorBasis i₀).ofLp j = 0 from congr_fun h j]
      rw [this, Real.sqrt_zero] at hn
      exact zero_ne_one hn
    ·
      rw [eigenvector_dotProduct_one_V hL i₀, div_one]
      rw [← laplacian_quadratic_form_eq]
      exact eigenvalue_eq_rayleigh_eigenvector_V hL i₀
  ·
    intro r ⟨x, hx, hxr⟩
    rw [← hxr]
    have hpos : (0 : ℝ) < dotProduct x x := by
      have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      obtain ⟨i, hi⟩ := this
      calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
        _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
            (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
        _ = dotProduct x x := by simp [dotProduct]
    rw [← laplacian_quadratic_form_eq]
    rw [div_le_iff₀ hpos]
    rw [rayleigh_spectral_expansion_V hL x]
    calc ∑ i, hL.eigenvalues i * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2
        ≤ ∑ i, hL.eigenvalues i₀ * (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (hi₀ i) (sq_nonneg _)
      _ = hL.eigenvalues i₀ * ∑ i, (dotProduct (⇑(hL.eigenvectorBasis i)) x) ^ 2 := by
          rw [Finset.mul_sum]
      _ = hL.eigenvalues i₀ * dotProduct x x := by
          rw [parseval_eigenvectors_V hL x]

end LaplacianQuadForm

section LaplacianLambda1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem ones_ne_zero : (fun _ : V => (1 : ℝ)) ≠ 0 := by
  intro h
  have := congr_fun h (Classical.arbitrary V)
  simp at this

omit [Nonempty V] in
theorem laplacian_quadform_ones_eq_zero :
    dotProduct (fun _ : V => (1 : ℝ)) ((G.lapMatrix ℝ).mulVec (fun _ => 1)) = 0 := by
  rw [lapMatrix_mulVec_const_eq_zero]
  simp [dotProduct]

omit [Nonempty V] in
theorem laplacian_rayleigh_nonneg (x : V → ℝ) (hx : x ≠ 0) :
    0 ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x := by
  apply div_nonneg
  · have h := lapMatrix_toLinearMap₂' ℝ G x
    rw [toLinearMap₂'_apply'] at h
    rw [h]
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    · norm_num
  · have : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    obtain ⟨i, hi⟩ := this
    apply le_of_lt
    calc (0 : ℝ) < x i * x i := mul_self_pos.mpr hi
      _ ≤ ∑ j : V, x j * x j := Finset.single_le_sum
          (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (a := x j)) (Finset.mem_univ i)
      _ = dotProduct x x := by simp [dotProduct]

omit [Nonempty V] in
theorem laplacian_rayleigh_ones_eq_zero :
    dotProduct (fun _ : V => (1 : ℝ)) ((G.lapMatrix ℝ).mulVec (fun _ => 1)) /
    dotProduct (fun _ : V => (1 : ℝ)) (fun _ : V => (1 : ℝ)) = 0 := by
  rw [laplacian_quadform_ones_eq_zero]
  simp

theorem laplacian_rayleighQuotient_min_eq_zero :
    IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧
      dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x = r} 0 := by
  constructor
  ·
    exact ⟨fun _ => 1, ones_ne_zero, laplacian_rayleigh_ones_eq_zero G⟩
  ·
    intro r ⟨x, hx, hxr⟩
    rw [← hxr]
    exact laplacian_rayleigh_nonneg G x hx

theorem corollary24_rayleighQuotient
    (hL : (G.lapMatrix ℝ).IsHermitian)
    (k : V)
    (hk : ∀ x : V → ℝ, (∀ j : V, hL.eigenvalues j < hL.eigenvalues k →
      dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ↔ (∑ i, x i = 0))
    (i₀ : V)
    (hi₀ : ∀ j : V, hL.eigenvalues j ≤ hL.eigenvalues i₀) :

    IsLeast {r | ∃ x : V → ℝ, x ≠ 0 ∧
      dotProduct x ((G.lapMatrix ℝ).mulVec x) / dotProduct x x = r} 0 ∧

    IsLeast
      {r | ∃ x : V → ℝ, x ≠ 0 ∧
        (∑ i, x i = 0) ∧
        (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
          dotProduct x x = r}
      (hL.eigenvalues k) ∧

    IsGreatest
      {r | ∃ x : V → ℝ, x ≠ 0 ∧
        (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
          dotProduct x x = r}
      (hL.eigenvalues i₀) := by
  refine ⟨laplacian_rayleighQuotient_min_eq_zero G, ?_, laplacian_edge_sum_max_quotient_characterization G hL i₀ hi₀⟩

  have h := laplacian_edge_sum_min_characterization G hL k
  have hset : {r | ∃ x : V → ℝ, x ≠ 0 ∧
      (∀ j : V, hL.eigenvalues j < hL.eigenvalues k →
        dotProduct (⇑(hL.eigenvectorBasis j)) x = 0) ∧
      (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
        dotProduct x x = r} =
    {r | ∃ x : V → ℝ, x ≠ 0 ∧
      (∑ i, x i = 0) ∧
      (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 /
        dotProduct x x = r} := by
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hne, horth, hval⟩
      exact ⟨x, hne, (hk x).mp horth, hval⟩
    · rintro ⟨x, hne, hsum, hval⟩
      exact ⟨x, hne, (hk x).mpr hsum, hval⟩
  rw [← hset]
  exact h

end LaplacianLambda1

end CourantFischer
