/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

noncomputable section

open IsLocalRing

/-- The maximal ideal `m_x ⊂ k[x_1,…,x_n]` of polynomials vanishing at the point `x ∈ k^n`,
defined as the kernel of evaluation at `x`. -/
def maxIdealOfPoint {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- The vanishing ideal of a point `x ∈ k^n` is maximal, since the evaluation map is
surjective onto the field `k`. -/
instance maxIdealOfPoint_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- The image of `m_x` in the quotient `k[x_1,…,x_n]/I`, well-defined whenever `I ⊆ m_x`;
this is the maximal ideal of `x` viewed as a point of the affine variety `V(I)`. -/
def maxIdealOfPointInQuotient {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint x)

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is maximal. -/
instance maxIdealOfPointInQuotient_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is prime (since maximal ideals are prime). -/
instance maxIdealOfPointInQuotient_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsPrime :=
  (maxIdealOfPointInQuotient_isMaximal I x hI).isPrime

/-- The local ring of the affine variety `V(I)` at the point `x`, obtained as the
localization of `k[x_1,…,x_n]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :=
  Localization.AtPrime (maxIdealOfPointInQuotient I x hI)

/-- The Jacobian matrix `(∂f_i/∂x_j)(x)` of a family of polynomials `f_1,…,f_m` evaluated
at the point `x ∈ k^n`. -/
def jacobianMatrix {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))

/-- Definition 34 (Lecture 18). The universal property characterising Kähler differentials:
`A`-linear maps `Ω[A⁄k] → M` correspond naturally to `k`-derivations `A → M`. -/
def Definition34_KaehlerDifferential_universalProperty
    (k : Type*) (A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    (Ω[A⁄k] →ₗ[A] M) ≃ₗ[A] Derivation k A M :=
  KaehlerDifferential.linearMapEquivDerivation k A

/-- Definition 35 (Lecture 18). The Zariski cotangent space of a local ring `R`, defined as
`m/m²` viewed as a vector space over the residue field. -/
def Definition35_CotangentSpace
    (R : Type*) [CommRing R] [IsLocalRing R] :=
  IsLocalRing.CotangentSpace R

/-- Lemma 30 (Lecture 18). For a Noetherian local ring, the Krull dimension is at most the
dimension of the Zariski cotangent space. -/
theorem Lemma30_cotangentSpace_dim_ge_krullDim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- Definition 36 (Lecture 18). A Noetherian local ring is smooth (regular) iff the Zariski
cotangent space has dimension equal to the Krull dimension; equality in Lemma 30. -/
theorem Definition36_smooth_iff_regular
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace R



/-- The generic point of an integral finite-type `k`-algebra is regular: localizing at the
zero ideal gives a field, hence trivially a regular local ring. -/
theorem genericPoint_isRegularLocalRing
    (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) := by

  have hField : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    simp

  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hField.toField
  infer_instance





/-- A single-row matrix has rank zero iff it is the zero matrix. -/
lemma matrix_fin1_rank_eq_zero_iff {k : Type*} [Field k] {n : ℕ}
    (M : Matrix (Fin 1) (Fin n) k) : M.rank = 0 ↔ M = 0 := by
  unfold Matrix.rank
  constructor
  · intro h
    rw [Submodule.finrank_eq_zero] at h
    rw [LinearMap.range_eq_bot] at h
    ext i j
    have hcol := LinearMap.ext_iff.mp h (Pi.single j 1)
    simp [Matrix.mulVecLin, Matrix.mulVec_single] at hcol
    have : M.col j 0 = 0 := by rw [hcol]; rfl
    simp [Matrix.col] at this
    fin_cases i
    exact this
  · intro h
    subst h
    exact Matrix.rank_zero

/-- A single-row matrix has rank one iff it has at least one nonzero entry. -/
lemma matrix_fin1_rank_eq_one_iff {k : Type*} [Field k] {n : ℕ}
    (M : Matrix (Fin 1) (Fin n) k) :
    M.rank = 1 ↔ ∃ j, M 0 j ≠ 0 := by
  have hle : M.rank ≤ 1 := by
    have := Matrix.rank_le_card_height M; simp at this; exact this
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : M = 0 := by ext i j; fin_cases i; exact hall j
    rw [hzero, Matrix.rank_zero] at h; omega
  · intro ⟨j, hj⟩
    have hne : M ≠ 0 := by intro h; rw [h] at hj; simp at hj
    have hpos : 0 < M.rank := by
      by_contra h
      push Not at h
      exact hne ((matrix_fin1_rank_eq_zero_iff M).mp (by omega))
    omega

/-- Corollary 23, hypersurface case: for a hypersurface `V(P) ⊂ 𝔸ⁿ`, smoothness at `x`
amounts to some partial derivative `∂P/∂x_i` being nonzero at `x`, i.e. the Jacobian
(`1 × n`) matrix has rank one. -/
theorem Corollary23_hypersurface_criterion
    {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (_hx : MvPolynomial.eval x P = 0) :
    (∃ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔
    (jacobianMatrix (fun _ : Fin 1 => P) x).rank = 1 := by
  rw [matrix_fin1_rank_eq_one_iff]
  simp [jacobianMatrix]







/-- If each `f_i` vanishes at `x`, then `span(f_1,…,f_m) ⊆ m_x`. -/
lemma span_range_le_maxIdealOfPoint {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
    Ideal.span (Set.range f) ≤ maxIdealOfPoint x := by
  rw [Ideal.span_le]
  intro p hp
  obtain ⟨i, rfl⟩ := hp
  rw [maxIdealOfPoint, SetLike.mem_coe, RingHom.mem_ker]
  exact hx i

/-- Polynomials in an ideal `I ⊆ m_x` all vanish at the point `x`. -/
lemma eval_eq_zero_of_mem_le_maxIdeal {k : Type*} [Field k] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x)
    (f : Fin m → MvPolynomial (Fin n) k) (hfI : ∀ i, f i ∈ I) :
    ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro i
  have h := hI (hfI i)
  rwa [maxIdealOfPoint, RingHom.mem_ker] at h


end
