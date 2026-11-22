/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Atlas.EllipticCurves.code.FiniteFields
import Mathlib.FieldTheory.Finite.Extension


namespace FiniteFieldArith

/-- The bit-size of a natural number `n`, defined as `⌊log₂ n⌋ + 1`. This is the
number of bits in the standard binary representation and serves as the cost
parameter `n = lg q` used throughout Sutherland's complexity analyses. -/
noncomputable def bitSize (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Bit-operation cost of addition/subtraction in `𝔽_p`: linear in the bit-size
of `p`. The constant `3` is a small fixed overhead for carry propagation. -/
noncomputable def fpAddBitOps (p : ℕ) : ℕ := 3 * bitSize p

/-- Bit-operation cost of addition in `𝔽_q = 𝔽_{p^d}`: `d` independent additions
in `𝔽_p`, one per coefficient of the polynomial-basis representation. -/
noncomputable def fqAddBitOps (p d : ℕ) : ℕ := d * fpAddBitOps p

open Polynomial in
open Polynomial in
open Polynomial in
/-- The cost of adding in `𝔽_q` is the sum of the per-coordinate costs in `𝔽_p`,
i.e. `∑_{i < d} fpAddBitOps p = fqAddBitOps p d`. -/
theorem fq_add_cost_is_sum_over_coefficients (p d : ℕ) :
    ∑ _i : Fin d, fpAddBitOps p = fqAddBitOps p d := by
  simp only [fqAddBitOps, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Definitional unfolding of `fqAddBitOps`: `fqAddBitOps p d = d · (3 · (⌊log₂ p⌋ + 1))`. -/
@[simp]
theorem fqAddBitOps_def (p d : ℕ) :
    fqAddBitOps p d = d * (3 * (Nat.log 2 p + 1)) := by
  unfold fqAddBitOps fpAddBitOps bitSize; ring

/-- For `p ≥ 2`, `d · log₂ p ≤ log₂(p^d)`. Used to bound costs over extension
fields in terms of the bit-size of `q = p^d`. -/
lemma d_mul_log_le (p d : ℕ) (hp : 2 ≤ p) :
    d * Nat.log 2 p ≤ Nat.log 2 (p ^ d) := by
  have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
  calc d * Nat.log 2 p
      = Nat.log 2 (2 ^ (d * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ d) := by
        apply Nat.log_mono_right
        calc 2 ^ (d * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ d := by ring
          _ ≤ p ^ d := Nat.pow_le_pow_left hle d

/-- For `p ≥ 2`, `d ≤ log₂(p^d)`. A simple monotonicity bound. -/
lemma d_le_log_pow (p d : ℕ) (hp : 2 ≤ p) :
    d ≤ Nat.log 2 (p ^ d) := by
  calc d = Nat.log 2 (2 ^ d) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ d) := Nat.log_mono_right (Nat.pow_le_pow_left hp d)

/-- For `p ≥ 2`, `d · bitSize p ≤ 2 · bitSize (p^d)`. This is the absorbing
inequality used to compare per-`𝔽_p` and per-`𝔽_q` cost contributions. -/
lemma d_mul_bitSize_le (p d : ℕ) (hp : 2 ≤ p) :
    d * bitSize p ≤ 2 * bitSize (p ^ d) := by
  unfold bitSize
  have h1 := d_mul_log_le p d hp
  have h2 := d_le_log_pow p d hp
  have h3 : d * (Nat.log 2 p + 1) = d * Nat.log 2 p + d := by ring
  rw [h3]; linarith

/-- Linear-in-`bitSize (p^d)` bound on the cost of addition in `𝔽_q`:
`fqAddBitOps p d ≤ 6 · bitSize(p^d)`. This is the key inequality behind
Theorem 3.24. -/
lemma fq_add_bitOps_linear (p d : ℕ) (hp : Nat.Prime p) :
    fqAddBitOps p d ≤ 6 * bitSize (p ^ d) := by
  unfold fqAddBitOps fpAddBitOps
  have h := d_mul_bitSize_le p d hp.two_le
  nlinarith

/-- Bit-operation cost of subtraction in `𝔽_q`: identical to addition. -/
noncomputable def fqSubBitOps (p d : ℕ) : ℕ := d * fpAddBitOps p

/-- Linear bound for subtraction in `𝔽_q`, mirroring `fq_add_bitOps_linear`. -/
lemma fq_sub_bitOps_linear (p d : ℕ) (hp : Nat.Prime p) :
    fqSubBitOps p d ≤ 6 * bitSize (p ^ d) :=
  fq_add_bitOps_linear p d hp

/-- Theorem 3.24 (formal statement): addition in `𝔽_q` runs in `O(n)` bit
operations where `n = lg q`. Existence of a universal constant `C` (here `C = 6`)
such that `fqAddBitOps p d ≤ C · bitSize(p^d)` for all primes `p` and all `d`. -/
theorem fq_add_complexity_linear :
    ∃ C : ℕ, ∀ (p : ℕ) (d : ℕ), Nat.Prime p →
      fqAddBitOps p d ≤ C * bitSize (p ^ d) :=
  ⟨6, fun p d hp => fq_add_bitOps_linear p d hp⟩

end FiniteFieldArith


open Polynomial

variable {R : Type*} [CommRing R]

/-- The discrete Fourier transform `DFT_ω(f)(i) := f(ω^i)` at an element `ω ∈ R`
of order dividing `n`, returned as a function `Fin n → R`. Appears in
Theorem 3.29 / Theorem 3.30. -/
noncomputable def DFT (ω : R) (n : ℕ) (f : R[X]) : Fin n → R :=
  fun i => f.eval (ω ^ i.val)

/-- The cyclic convolution `(f * g) mod (X^n − 1)`. Used as the polynomial-level
operation diagonalised by the DFT in Theorem 3.29. -/
noncomputable def cyclicConv (n : ℕ) (f g : R[X]) : R[X] :=
  (f * g) %ₘ (X ^ n - 1)

/-- Definitional `simp` lemma: `DFT_ω(f)(i) = f(ω^i)`. -/
@[simp]
theorem DFT_apply (ω : R) (n : ℕ) (f : R[X]) (i : Fin n) :
    DFT ω n f i = f.eval (ω ^ i.val) := rfl

/-- Definitional `simp` lemma: `cyclicConv n f g = (f · g) mod (X^n − 1)`. -/
@[simp]
theorem cyclicConv_def (n : ℕ) (f g : R[X]) :
    cyclicConv n f g = (f * g) %ₘ (X ^ n - 1) := rfl

/-- If `a` is a root of the monic divisor `m`, then evaluating `(p mod m)` at `a`
is the same as evaluating `p` at `a`. Used to identify `DFT` of a cyclic
convolution with the pointwise product. -/
theorem eval_modByMonic_eq_eval (p m : R[X]) (a : R) (hroot : m.IsRoot a) :
    (p %ₘ m).eval a = p.eval a := by
  conv_rhs => rw [← modByMonic_add_div p m]
  simp only [eval_add, eval_mul]
  rw [IsRoot.def.mp hroot, zero_mul, add_zero]

/-- If `ω^n = 1`, then every power `ω^i` is a root of `X^n − 1`. -/
theorem isRoot_X_pow_sub_one {ω : R} {n : ℕ} (hω : ω ^ n = 1) (i : ℕ) :
    (X ^ n - 1 : R[X]).IsRoot (ω ^ i) := by
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one]
  rw [← pow_mul, mul_comm, pow_mul, hω, one_pow, sub_self]

/-- Theorem 3.29: when `ω^n = 1`, the DFT diagonalises cyclic convolution, i.e.
`DFT_ω(f * g mod X^n − 1) = DFT_ω(f) · DFT_ω(g)` pointwise. -/
theorem dft_cyclicConv (ω : R) (n : ℕ) (f g : R[X]) (hω : ω ^ n = 1) :
    DFT ω n (cyclicConv n f g) = DFT ω n f * DFT ω n g := by
  ext i
  simp only [DFT_apply, Pi.mul_apply, cyclicConv]
  rw [eval_modByMonic_eq_eval _ _ _ (isRoot_X_pow_sub_one hω i.val)]
  exact eval_mul

/-- The "first half" of a polynomial `f`: the truncation `∑_{j < m} c_j X^j` of
`f` to degree `< m`. -/
noncomputable def polyFirstHalf (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C (f.coeff j) * X ^ j

/-- The "second half" of a polynomial `f`: the coefficient sequence
`(f_m, f_{m+1}, …, f_{2m−1})` repackaged as a degree-`< m` polynomial. -/
noncomputable def polySecondHalf (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C (f.coeff (m + j)) * X ^ j

/-- The twisted-difference polynomial `s_f(ω, m) := ∑_{j < m} (f_j − f_{m+j}) ω^j X^j`
that appears in the recursive FFT identity for odd-indexed DFT values. -/
noncomputable def fftTwistedDiff (ω : R) (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C ((f.coeff j - f.coeff (m + j)) * ω ^ j) * X ^ j

/-- The radix-2 FFT (cf. Theorem 3.30): given a primitive `2^n`-th root of unity
`ω`, recursively computes `DFT_ω(f)(i)` for all `i < 2^n` using `O(n · 2^n)`
ring operations. -/
noncomputable def fft (ω : R) : (n : ℕ) → R[X] → (Fin (2 ^ n) → R)
  | 0, f => fun _ => f.eval 1
  | n + 1, f =>
    let m := 2 ^ n
    let r := polyFirstHalf m f + polySecondHalf m f
    let s := fftTwistedDiff ω m f
    let dft_r := fft (ω ^ 2) n r
    let dft_s := fft (ω ^ 2) n s
    fun i =>
      if i.val % 2 = 0 then
        dft_r ⟨i.val / 2, by have := i.isLt; simp only [pow_succ] at this; omega⟩
      else
        dft_s ⟨i.val / 2, by have := i.isLt; simp only [pow_succ] at this; omega⟩

/-- Predicate: `ω` is a primitive `2^n`-th root of unity in the radix-2 sense,
i.e. `ω^(2^(n−1)) = −1` (with the convention that the `n = 0` case is trivial).
This is the hypothesis under which the recursive FFT identities hold. -/
def IsPrim2PowRoot (ω : R) : ℕ → Prop
  | 0 => True
  | n + 1 => ω ^ (2 ^ n) = -1

/-- If `ω` is a primitive `2^(n+1)`-th root of unity, then `ω²` is a primitive
`2^n`-th root of unity. Drives the recursion of the FFT. -/
lemma isPrim2PowRoot_sq {ω : R} (h : IsPrim2PowRoot ω (n + 1)) :
    IsPrim2PowRoot (ω ^ 2) n := by
  cases n with
  | zero => trivial
  | succ n =>
    show (ω ^ 2) ^ 2 ^ n = -1
    rw [← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) from by ring]
    exact h

/-- If `ω` is a primitive `2^(n+1)`-th root of unity (i.e. `ω^(2^n) = −1`),
then `ω^(2^(n+1)) = 1`. -/
lemma isPrim2PowRoot_pow_eq_one {ω : R} (h : IsPrim2PowRoot ω (n + 1)) :
    ω ^ 2 ^ (n + 1) = 1 := by
  rw [show (2:ℕ) ^ (n + 1) = 2 ^ n * 2 from by ring, pow_mul, h]; norm_num

/-- A `∑_{j < m} C(c_j) X^j` polynomial has natural degree strictly less than `m`
(for `m > 0`). Bounds the degrees of the recursive subpolynomials in the FFT. -/
lemma natDegree_sum_C_X_pow_lt {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    (∑ j ∈ Finset.range m, C (c j) * X ^ j).natDegree < m :=
  calc _ ≤ (Finset.range m).sup (fun j => (C (c j) * X ^ j).natDegree) :=
        natDegree_sum_le _ _
    _ ≤ (Finset.range m).sup id :=
        Finset.sup_mono_fun (fun j _ => natDegree_C_mul_X_pow_le (c j) j)
    _ < m := by
        rw [Finset.sup_lt_iff (by omega)]
        intro j hj; exact Finset.mem_range.mp hj

/-- Evaluation rule for the twisted-difference polynomial:
`(fftTwistedDiff ω m f)(x) = ((firstHalf − secondHalf))(ω · x)`. -/
lemma fftTwistedDiff_eval (ω : R) (m : ℕ) (f : R[X]) (x : R) :
    (fftTwistedDiff ω m f).eval x =
    (polyFirstHalf m f - polySecondHalf m f).eval (ω * x) := by
  simp only [fftTwistedDiff, polyFirstHalf, polySecondHalf,
    eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, mul_pow]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- Splitting identity: if `deg f < 2m`, then `f(x) = firstHalf(x) + x^m · secondHalf(x)`. -/
lemma poly_split_eval (m : ℕ) (f : R[X]) (hf : f.natDegree < 2 * m) (x : R) :
    f.eval x = (polyFirstHalf m f).eval x + x ^ m * (polySecondHalf m f).eval x := by
  rw [eval_eq_sum_range' hf]
  simp only [polyFirstHalf, polySecondHalf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [show 2 * m = m + m from by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring

/-- Even-index FFT identity: under `ω^(2m) = 1` and `deg f < 2m`, the value
`f(ω^{2i})` equals `(firstHalf + secondHalf)((ω²)^i)`. -/
theorem fft_even_identity (ω : R) (m : ℕ) (f : R[X]) (hf : f.natDegree < 2 * m)
    (hω : ω ^ (2 * m) = 1) (i : ℕ) :
    f.eval (ω ^ (2 * i)) =
    (polyFirstHalf m f + polySecondHalf m f).eval ((ω ^ 2) ^ i) := by
  rw [show ω ^ (2 * i) = (ω ^ 2) ^ i from pow_mul ω 2 i,
      poly_split_eval m f hf, eval_add]
  have key : ((ω ^ 2) ^ i) ^ m = 1 := by
    calc ((ω ^ 2) ^ i) ^ m = ω ^ (2 * (i * m)) := by rw [← pow_mul, ← pow_mul]
      _ = ω ^ (2 * m * i) := by congr 1; ring
      _ = (ω ^ (2 * m)) ^ i := pow_mul ω (2 * m) i
      _ = 1 := by rw [hω, one_pow]
  rw [key, one_mul]

/-- Odd-index FFT identity: under `ω^m = −1` and `deg f < 2m`, the value
`f(ω^{2i+1})` equals `(fftTwistedDiff ω m f)((ω²)^i)`. -/
theorem fft_odd_identity (ω : R) (m : ℕ) (f : R[X]) (hf : f.natDegree < 2 * m)
    (hωm : ω ^ m = -1) (i : ℕ) :
    f.eval (ω ^ (2 * i + 1)) =
    (fftTwistedDiff ω m f).eval ((ω ^ 2) ^ i) := by
  rw [poly_split_eval m f hf]
  have hpow_odd_m : (ω ^ (2 * i + 1)) ^ m = -1 := by
    calc (ω ^ (2 * i + 1)) ^ m = ω ^ ((2 * i + 1) * m) := (pow_mul _ _ _).symm
      _ = ω ^ (m * (2 * i) + m) := by congr 1; ring
      _ = ω ^ (m * (2 * i)) * ω ^ m := pow_add ω _ m
      _ = (ω ^ m) ^ (2 * i) * ω ^ m := by rw [pow_mul]
      _ = (-1) ^ (2 * i) * (-1) := by rw [hωm]
      _ = -1 := by simp [pow_mul]
  rw [hpow_odd_m, neg_one_mul, ← sub_eq_add_neg, ← eval_sub]
  rw [show ω ^ (2 * i + 1) = ω * (ω ^ 2) ^ i from by
    rw [show 2 * i + 1 = 1 + 2 * i from by ring, pow_add, pow_one, pow_mul]]
  rw [← fftTwistedDiff_eval]

/-- Theorem 3.30 (correctness of the FFT): if `ω` is a primitive `2^n`-th root of
unity and `deg f < 2^n`, then `fft ω n f` equals `DFT_ω(f)` on all of `Fin (2^n)`. -/
theorem fft_eq_DFT (ω : R) (n : ℕ) (f : R[X])
    (hprim : IsPrim2PowRoot ω n) (hdeg : f.natDegree < 2 ^ n) :
    fft ω n f = DFT ω (2 ^ n) f := by
  induction n generalizing ω f with
  | zero =>
    ext ⟨i, hi⟩; simp only [fft, DFT_apply]
    have : i = 0 := by omega
    subst this; simp
  | succ n ih =>
    ext ⟨k, hk⟩; simp only [fft, DFT_apply]
    set m := 2 ^ n
    set r := polyFirstHalf m f + polySecondHalf m f
    set s := fftTwistedDiff ω m f
    have hprim2 : IsPrim2PowRoot (ω ^ 2) n := isPrim2PowRoot_sq hprim
    have hm_pos : 0 < m := Nat.pos_of_ne_zero (by positivity)
    have hdeg_2m : f.natDegree < 2 * m := by
      rwa [show 2 * m = 2 ^ (n + 1) from by simp [m, pow_succ, mul_comm]]
    have hdeg_r : r.natDegree < 2 ^ n := by
      calc r.natDegree
          ≤ max (polyFirstHalf m f).natDegree (polySecondHalf m f).natDegree :=
            natDegree_add_le _ _
        _ < m := by
            simp only [Nat.max_lt]
            exact ⟨natDegree_sum_C_X_pow_lt hm_pos _, natDegree_sum_C_X_pow_lt hm_pos _⟩
    have hdeg_s : s.natDegree < 2 ^ n := natDegree_sum_C_X_pow_lt hm_pos _
    have hω2m : ω ^ (2 * m) = 1 := by
      rw [show 2 * m = 2 ^ (n + 1) from by simp [m, pow_succ, mul_comm]]
      exact isPrim2PowRoot_pow_eq_one hprim
    by_cases hmod : k % 2 = 0
    ·
      simp only [hmod, ↓reduceIte]
      have ih_r := congr_fun (ih (ω ^ 2) r hprim2 hdeg_r) ⟨k / 2, by omega⟩
      simp only [DFT_apply] at ih_r; rw [ih_r]
      conv_rhs => rw [show k = 2 * (k / 2) from by omega]
      exact (fft_even_identity ω m f hdeg_2m hω2m (k / 2)).symm
    ·
      simp only [hmod, ↓reduceIte]
      have ih_s := congr_fun (ih (ω ^ 2) s hprim2 hdeg_s) ⟨k / 2, by omega⟩
      simp only [DFT_apply] at ih_s; rw [ih_s]
      conv_rhs => rw [show k = 2 * (k / 2) + 1 from by omega]
      exact (fft_odd_identity ω m f hdeg_2m hprim (k / 2)).symm

section FFTPolyMulComplexity

/-- Operation count `5 · 2^k · k` for one radix-2 FFT of size `2^k` (Theorem 3.30). -/
def fftOpCount (k : ℕ) : ℕ := 5 * 2 ^ k * k

/-- Operation count `n` for pointwise multiplication of two `n`-vectors. -/
def pointwiseMulOpCount (n : ℕ) : ℕ := n

/-- Operation count `n` for computing `n` consecutive powers of an element. -/
def computePowersOpCount (n : ℕ) : ℕ := n

/-- Operation count `2n` for scalar multiplication of an `n`-vector. -/
def scalarMulOpCount (n : ℕ) : ℕ := 2 * n

/-- Total operation count for FFT-based polynomial multiplication at size `2^k`:
three FFTs plus pointwise multiplication, twiddle-power generation, and scalar
multiplications. This is the operation budget behind Corollary 3.31. -/
def fftPolyMulCost (k : ℕ) : ℕ :=
  let n := 2 ^ k
  3 * fftOpCount k + pointwiseMulOpCount n + 2 * computePowersOpCount n + scalarMulOpCount n

/-- Quantitative form of Corollary 3.31: the FFT polynomial-multiplication cost
at size `2^k` is bounded by `20 · 2^k · (k+1) = O(n log n)`. -/
theorem fftPolyMulCost_le (k : ℕ) :
    fftPolyMulCost k ≤ 20 * 2 ^ k * (k + 1) := by
  unfold fftPolyMulCost fftOpCount pointwiseMulOpCount computePowersOpCount scalarMulOpCount
  nlinarith [Nat.one_le_two_pow (n := k)]

/-- If `deg(f · g) < n`, then the cyclic convolution `(f · g) mod (X^n − 1)` is
just `f · g`. This is the soundness step letting one recover the full product
from a single cyclic convolution by padding the input length. -/
theorem cyclicConv_eq_mul [Nontrivial R] (n : ℕ) (hn : 0 < n) (f g : R[X])
    (hdeg : (f * g).natDegree < n) :
    cyclicConv n f g = f * g := by
  simp only [cyclicConv]
  rw [show (X : R[X]) ^ n - 1 = X ^ n - C 1 by simp,
      modByMonic_eq_self_iff (monic_X_pow_sub_C 1 (by omega)),
      degree_X_pow_sub_C (by omega : 0 < n)]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hdeg)

/-- Corollary 3.31 (full statement): over a commutative ring `R` containing a
primitive `2^(k+1)`-th root of unity `ω` with `2` invertible, two polynomials of
degree `< 2^k` can be multiplied as a cyclic convolution, the DFT diagonalises
the multiplication, `2^(k+1)` is invertible (needed for the inverse FFT), and the
total cost is `O(n log n) = 20 · 2^(k+1) · (k+2)`. -/
theorem fft_poly_mul_complexity
    (R : Type*) [CommRing R] (k : ℕ) (ω : R)
    (hprim : IsPrim2PowRoot ω (k + 1)) (hunit : IsUnit (2 : R))
    (f g : R[X]) (hf : f.natDegree < 2 ^ k) (hg : g.natDegree < 2 ^ k) :

    cyclicConv (2 ^ (k + 1)) f g = f * g

    ∧ DFT ω (2 ^ (k + 1)) (f * g) =
        DFT ω (2 ^ (k + 1)) f * DFT ω (2 ^ (k + 1)) g

    ∧ IsUnit ((2 : R) ^ (k + 1))

    ∧ fftPolyMulCost (k + 1) ≤ 20 * 2 ^ (k + 1) * ((k + 1) + 1) := by

  have hfg : (f * g).natDegree < 2 ^ (k + 1) :=
    calc (f * g).natDegree ≤ f.natDegree + g.natDegree := natDegree_mul_le
      _ < 2 ^ k + 2 ^ k := Nat.add_lt_add hf hg
      _ = 2 ^ (k + 1) := by ring

  rcases subsingleton_or_nontrivial R with hR | hR
  ·
    haveI : Subsingleton R[X] := inferInstance
    refine ⟨Subsingleton.elim _ _, ?_, ?_, ?_⟩
    · have : Subsingleton (Fin (2 ^ (k + 1)) → R) := inferInstance
      exact Subsingleton.elim _ _
    · rw [show (2 : R) ^ (k + 1) = 1 from Subsingleton.elim _ _]; exact isUnit_one
    · exact fftPolyMulCost_le (k + 1)
  ·
    have h1 : cyclicConv (2 ^ (k + 1)) f g = f * g :=
      cyclicConv_eq_mul (2 ^ (k + 1)) (by positivity) f g hfg
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [← h1]
      exact dft_cyclicConv ω (2 ^ (k + 1)) f g (isPrim2PowRoot_pow_eq_one hprim)
    · exact hunit.pow (k + 1)
    · exact fftPolyMulCost_le (k + 1)

end FFTPolyMulComplexity

namespace FiniteFieldArith

/-- Bit-length of a natural number `n`, using `Nat.size`. Equivalent to `bitSize`
but defined in terms of the standard library `Nat.size`. -/
def bitlength (n : ℕ) : ℕ := Nat.size n

variable (intMulCost : ℕ → ℕ)

/-- Bit-length of any element of `𝔽_p` (in its canonical representative
`a ∈ {0, …, p − 1}`) is at most the bit-length of `p`. -/
theorem fp_repr_bitlength_le (p : ℕ) [NeZero p] (a : ZMod p) :
    bitlength a.val ≤ bitlength p := by
  unfold bitlength
  exact Nat.size_le_size (le_of_lt (ZMod.val_lt a))

/-- The integer product of two `𝔽_p`-representatives fits in at most `2 · bitlength p`
bits. Used to bound the input size of modular reduction in `𝔽_p` multiplication. -/
theorem fp_mul_repr_bitlength_le (p : ℕ) [NeZero p] (a b : ZMod p) :
    bitlength (a.val * b.val) ≤ 2 * bitlength p := by
  unfold bitlength
  rw [Nat.size_le]
  have ha : a.val < p := ZMod.val_lt a
  have hb : b.val < p := ZMod.val_lt b
  have hp : p < 2 ^ Nat.size p := Nat.lt_size_self p
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  calc a.val * b.val
      < p * p := Nat.mul_lt_mul_of_le_of_lt (le_of_lt ha) hb hp0
    _ = p ^ 2 := by ring
    _ < (2 ^ Nat.size p) ^ 2 := Nat.pow_lt_pow_left hp (by norm_num)
    _ = 2 ^ (2 * Nat.size p) := by ring

/-- Cost model for modular reduction by an `n`-bit modulus using Newton-iteration
based fast division: `3 · M(n) + n` where `M(n) = intMulCost n`. -/
def modReductionCost (n : ℕ) : ℕ :=
  3 * intMulCost n + n

/-- Bound `modReductionCost(n) ≤ 4 · M(n)` whenever the multiplication cost `M`
dominates the identity (i.e. `M(n) ≥ n`). -/
theorem modReductionCost_le (hM_ge_id : ∀ n, n ≤ intMulCost n) (n : ℕ) :
    modReductionCost intMulCost n ≤ 4 * intMulCost n := by
  unfold modReductionCost
  have h := hM_ge_id n
  linarith

/-- Cost of multiplication in `𝔽_p`: one integer multiplication plus one modular
reduction, both of bit-length `bitlength p`. -/
def fpMulCost (p : ℕ) : ℕ :=
  intMulCost (bitlength p) + modReductionCost intMulCost (bitlength p)

/-- Theorem 3.33: multiplication in `𝔽_p` takes `O(M(n))` bit operations where
`n = lg p` (here packaged as the existence of a constant `C = 5` such that
`fpMulCost p ≤ 5 · M(bitlength p)`). -/
theorem fp_mul_cost_is_O_intMulCost
    (hM_ge_id : ∀ n, n ≤ intMulCost n) :
    ∃ C : ℕ, ∀ p, fpMulCost intMulCost p ≤ C * intMulCost (bitlength p) := by
  refine ⟨5, fun p => ?_⟩
  unfold fpMulCost
  have hred := modReductionCost_le intMulCost hM_ge_id (bitlength p)
  linarith

/-- Schoolbook (quadratic) integer-multiplication cost: `M(n) = n²`. -/
def schoolbookMulCost (n : ℕ) : ℕ := n ^ 2

/-- Recursive cost model for the half-GCD algorithm (Lehmer / Knuth-Schönhage):
`H(n+1) = 2 · H((n+1)/2) + M(n+1)` with `H(0) = 0`. Underlies the
`O(M(n) log n)` complexity of fast Euclidean algorithms. -/
def halfGcdCost (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * halfGcdCost M ((n + 1) / 2) + M (n + 1)


/-- Cost of inversion in `𝔽_p` for an `n`-bit prime: implemented via the half-GCD
extended Euclidean algorithm. -/
def fpInvCost (n : ℕ) : ℕ :=
  halfGcdCost intMulCost n


/-- The size-restriction hypothesis `log₂ e = O(log₂ p)` used in Theorems 3.35
and 3.41, controlling how large the extension degree `e` can be relative to the
base prime. -/
def LogEBoundedByLogP (K : ℕ) (p e : ℕ) : Prop :=
  Nat.log 2 e ≤ K * (Nat.log 2 p + 1)

/-- Cost of computing polynomial GCDs at length `n`, using the half-GCD algorithm
instantiated with a given polynomial-multiplication cost. -/
def polyGcdCost (polyMulCost : ℕ → ℕ) (n : ℕ) : ℕ :=
  halfGcdCost polyMulCost n

/-- Cost model for inversion in `𝔽_q = 𝔽_{p^e}`: the Kronecker substitution
converts polynomial inversion into integer inversion of bit-width
`e · (bitSize p + bitSize e)`, then a half-GCD-based integer inversion gives the
final `O(M(n) log n)` bound. -/
noncomputable def fqInvCost (p e : ℕ) : ℕ :=
  let kroneckerBitWidth := e * (bitSize p + bitSize e)
  2 * intMulCost kroneckerBitWidth * (Nat.log 2 e + 1)

end FiniteFieldArith

namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

/-- For `p ≥ 2`, the bit-size of `p^e` is at least `e`. Useful to express the
cost bounds in Theorems 3.35 / 3.41 purely in terms of `n = bitSize(p^e)`. -/
lemma bitSize_pow_ge_e (p e : ℕ) (hp : 2 ≤ p) : e ≤ bitSize (p ^ e) := by
  unfold bitSize
  calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
    _ ≤ Nat.log 2 (p ^ e) + 1 := Nat.le_succ _

/-- Under the hypothesis `LogEBoundedByLogP K p e`, the Kronecker bit-width
`e · (bitSize p + bitSize e)` used in `fqInvCost` is bounded by
`(2K + 5) · bitSize(p^e)`, i.e. linear in `n = lg q`. -/
lemma fqInvCost_kb_le (p e K : ℕ) (hp : 2 ≤ p)
    (hlog : LogEBoundedByLogP K p e) :
    e * (bitSize p + bitSize e) ≤ (2 * K + 5) * bitSize (p ^ e) := by
  unfold bitSize LogEBoundedByLogP at *
  have h1 : e * Nat.log 2 p ≤ Nat.log 2 (p ^ e) := by
    have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
    calc e * Nat.log 2 p
        = Nat.log 2 (2 ^ (e * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := by
          apply Nat.log_mono_right
          calc 2 ^ (e * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ e := by ring
            _ ≤ p ^ e := Nat.pow_le_pow_left hle e
  have h2 : e ≤ Nat.log 2 (p ^ e) := by
    calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
  nlinarith

/-- Theorem 3.41: assuming `log e = O(log p)` and an `M`-regular multiplication
cost, inversion in `𝔽_q^×` runs in `O(M(n) log n) = O(n log² n)` bit operations
where `n = lg q`. -/
theorem fq_inversion_complexity
    (K : ℕ)
    (_hM_ge_id : ∀ n, n ≤ intMulCost n)
    (hM_mono : ∀ a b, a ≤ b → intMulCost a ≤ intMulCost b) :
    ∃ C : ℕ, ∀ (p e : ℕ), Nat.Prime p → 0 < e → LogEBoundedByLogP K p e →
      fqInvCost intMulCost p e ≤
        C * intMulCost (C * bitSize (p ^ e)) * (Nat.log 2 (bitSize (p ^ e)) + 1) := by
  set C := 2 * K + 5
  refine ⟨C, fun p e hp _he hlog => ?_⟩
  set n := bitSize (p ^ e)
  unfold fqInvCost
  simp only []
  set kb := e * (bitSize p + bitSize e)

  have hkb : kb ≤ C * n := fqInvCost_kb_le p e K hp.two_le hlog

  have hM_kb : intMulCost kb ≤ intMulCost (C * n) := hM_mono _ _ hkb

  have he_le_n : e ≤ n := bitSize_pow_ge_e p e hp.two_le
  have hlog_e : Nat.log 2 e ≤ Nat.log 2 n := Nat.log_mono_right he_le_n

  have hC_ge_2 : 2 ≤ C := by omega

  calc 2 * intMulCost kb * (Nat.log 2 e + 1)
      ≤ 2 * intMulCost (C * n) * (Nat.log 2 n + 1) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left 2 hM_kb
        · omega
    _ ≤ C * intMulCost (C * n) * (Nat.log 2 n + 1) := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_right _ hC_ge_2

open Polynomial in
/-- Bit-width of the Kronecker substitution used to reduce multiplication in
`𝔽_{p^e}` to a single integer multiplication: `e · (2 · bitSize p + bitSize e)`. -/
noncomputable def kroneckerBitWidth (p e : ℕ) : ℕ :=
  e * (2 * bitSize p + bitSize e)

/-- Cost model for multiplication in `𝔽_q = 𝔽_{p^e}` via Kronecker substitution:
one integer multiplication of bit-width `kroneckerBitWidth p e`, plus a coefficient
extraction step costing `kroneckerBitWidth p e` bit operations. -/
noncomputable def fqMulCost (p e : ℕ) : ℕ :=
  2 * intMulCost (kroneckerBitWidth p e) + kroneckerBitWidth p e

/-- Under `LogEBoundedByLogP K p e`, the Kronecker bit-width
`e · (2 bitSize p + bitSize e)` is bounded linearly by `(2K + 5) · bitSize(p^e)`. -/
lemma kronecker_bitWidth_le (p e K : ℕ) (hp : 2 ≤ p)
    (hlog : LogEBoundedByLogP K p e) :
    kroneckerBitWidth p e ≤ (2 * K + 5) * bitSize (p ^ e) := by
  unfold kroneckerBitWidth bitSize LogEBoundedByLogP at *
  have h1 : e * Nat.log 2 p ≤ Nat.log 2 (p ^ e) := by
    have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
    calc e * Nat.log 2 p
        = Nat.log 2 (2 ^ (e * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := by
          apply Nat.log_mono_right
          calc 2 ^ (e * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ e := by
                rw [mul_comm, pow_mul]
            _ ≤ p ^ e := Nat.pow_le_pow_left hle e
  have h2 : e ≤ Nat.log 2 (p ^ e) := by
    calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
  nlinarith

/-- Theorem 3.35: multiplication in `𝔽_q` runs in `O(M(n)) = O(n log n)` bit
operations, where `n = lg q`, under the size hypothesis `log e = O(log p)` and a
regular integer-multiplication cost model. -/
theorem fq_mul_complexity
    (p : ℕ) (e : ℕ) [Fact (Nat.Prime p)] (_he : 0 < e)
    (hM_ge_id : ∀ n, n ≤ intMulCost n)
    (hM_mono : ∀ a b, a ≤ b → intMulCost a ≤ intMulCost b)
    (K : ℕ) (hlog : LogEBoundedByLogP K p e)
    (C_reg : ℕ) (hM_reg : ∀ n, intMulCost ((2 * K + 5) * n) ≤ C_reg * intMulCost n) :
    ∃ C : ℕ, fqMulCost intMulCost p e ≤ C * intMulCost (bitSize (p ^ e)) := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  set n := bitSize (p ^ e)
  set C₀ := 2 * K + 5
  have hkb := kronecker_bitWidth_le p e K hp hlog


  have hkb_C0n : kroneckerBitWidth p e ≤ C₀ * n := hkb
  have hM_kb : intMulCost (kroneckerBitWidth p e) ≤ intMulCost (C₀ * n) :=
    hM_mono _ _ hkb_C0n
  have hM_C0n : intMulCost (C₀ * n) ≤ C_reg * intMulCost n := hM_reg n
  have hM_kb_bound : intMulCost (kroneckerBitWidth p e) ≤ C_reg * intMulCost n :=
    le_trans hM_kb hM_C0n

  have hn_le_Mn : n ≤ intMulCost n := hM_ge_id n
  have hkb_Mn : kroneckerBitWidth p e ≤ C₀ * intMulCost n :=
    le_trans hkb (Nat.mul_le_mul_left C₀ hn_le_Mn)

  refine ⟨2 * C_reg + C₀, ?_⟩
  unfold fqMulCost


  calc 2 * intMulCost (kroneckerBitWidth p e) + kroneckerBitWidth p e
      ≤ 2 * (C_reg * intMulCost n) + C₀ * intMulCost n := by
        linarith [hM_kb_bound, hkb_Mn]
    _ = (2 * C_reg + C₀) * intMulCost n := by ring

end FiniteFieldArith

namespace LongDivision

/-- Helper for the bit-by-bit long-division algorithm (Algorithm 3.37): at bit
index `k`, with current quotient `q` and remainder `r`, perform the shift-and-
conditional-subtract step using the `k`-th bit of `a` against modulus `b`. -/
def longDivAux (a b : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, q, r =>
    if 2 * r + (a.testBit 0).toNat ≥ b then
      (2 * q + 1, 2 * r + (a.testBit 0).toNat - b)
    else
      (2 * q, 2 * r + (a.testBit 0).toNat)
  | k + 1, q, r =>
    if 2 * r + (a.testBit (k + 1)).toNat ≥ b then
      longDivAux a b k (2 * q + 1) (2 * r + (a.testBit (k + 1)).toNat - b)
    else
      longDivAux a b k (2 * q) (2 * r + (a.testBit (k + 1)).toNat)

/-- Algorithm 3.37 (long division): given naturals `a, b`, return a pair `(q, r)`
with `a = qb + r` and `0 ≤ r < b`, handling the edge cases `b = 0`, `b > a`, and
`b = 1` directly. -/
def longDiv (a b : ℕ) : ℕ × ℕ :=
  if b = 0 then (0, a)
  else if b > a then (0, a)
  else if b = 1 then (a, 0)
  else longDivAux a b (Nat.log 2 a) 0 0

/-- Invariant for `longDivAux`: the running remainder stays strictly less than
the modulus `b` throughout the bit-by-bit iteration. -/
lemma longDivAux_rem_lt (a b : ℕ) (_hb : b ≥ 2) (k q r : ℕ) (hr : r < b) :
    (longDivAux a b k q r).2 < b := by
  induction k generalizing q r with
  | zero =>
    unfold longDivAux
    have hle := Bool.toNat_le (a.testBit 0)
    split_ifs with h <;> omega
  | succ k ih =>
    unfold longDivAux
    have hle := Bool.toNat_le (a.testBit (k + 1))
    split_ifs with h
    · exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

/-- Correctness invariant for `longDivAux`: after processing bits `k, k−1, …, 0`,
the quotient/remainder pair `(q', r')` satisfies
`q'·b + r' = q·b·2^(k+1) + r·2^(k+1) + (a mod 2^(k+1))`. -/
lemma longDivAux_spec (a b : ℕ) (_hb : b ≥ 2) (k q r : ℕ) (hr : r < b) :
    (longDivAux a b k q r).1 * b + (longDivAux a b k q r).2 =
    q * b * 2 ^ (k + 1) + r * 2 ^ (k + 1) + a % 2 ^ (k + 1) := by
  induction k generalizing q r with
  | zero =>
    unfold longDivAux
    have hbit := Nat.toNat_testBit a 0
    simp only [pow_zero, Nat.div_one] at hbit
    have hmod : a % 2 ^ 1 = a % 2 := by norm_num
    rw [hmod, ← hbit]
    split_ifs with h
    · zify [h]; ring
    · ring
  | succ k ih =>
    unfold longDivAux
    have hbit := Nat.toNat_testBit a (k + 1)
    have hle := Bool.toNat_le (a.testBit (k + 1))
    have hmod_split : a % 2 ^ (k + 1 + 1) =
        a % 2 ^ (k + 1) + 2 ^ (k + 1) * (a / 2 ^ (k + 1) % 2) := Nat.mod_pow_succ
    split_ifs with h
    · have hr_new : 2 * r + (a.testBit (k + 1)).toNat - b < b := by omega
      rw [ih _ _ hr_new, hmod_split, ← hbit]
      zify [h]; ring
    · have hr_new : 2 * r + (a.testBit (k + 1)).toNat < b := by omega
      rw [ih _ _ hr_new, hmod_split, ← hbit]
      ring

/-- Bit-operation cost model for long division of an `m`-bit integer by an
`n`-bit integer: `3 · m · n`. -/
noncomputable def longDivCost (m n : ℕ) : ℕ := 3 * m * n

/-- Theorem 3.38: long division uses `O(mn)` bit operations to divide an `m`-bit
integer by an `n`-bit integer, witnessed by the explicit constant `C = 3`. -/
theorem longDiv_complexity :
    ∃ C : ℕ, ∀ m n : ℕ, longDivCost m n ≤ C * (m * n) :=
  ⟨3, fun m n => by unfold longDivCost; nlinarith⟩

end LongDivision

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedVariables false in
/-- The "different type" predicate from Theorem 3.44 (Rabin 1980): two nonzero
elements `a, b ∈ 𝔽_q` (with char ≠ 2) have different type when their
`(q−1)/2`-th powers disagree, i.e. one is a square and the other is not. Used in
the root-finding Algorithm 3.45. -/
def AreDifferentType (hF : ringChar F ≠ 2) (a b : F) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ (Fintype.card F / 2) ≠ b ^ (Fintype.card F / 2)

/-- Decidability of `AreDifferentType`: each of the three conditions
(`a ≠ 0`, `b ≠ 0`, distinct `(q−1)/2`-th powers) is decidable in a finite field. -/
instance (hF : ringChar F ≠ 2) (a b : F) : Decidable (AreDifferentType hF a b) := by
  unfold AreDifferentType; exact instDecidableAnd


namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]
open Classical

/-- Squarefree factorization data (Algorithm 3.46): a polynomial `f` is given a
squarefree factorization as `f = ∏_{i < m} g_i^{i+1}` where the `g_i` are
pairwise coprime squarefree polynomials, `m > 0`, and the top exponent factor
`g_{m-1}` is not the constant `1`. -/
structure IsSquarefreeFactorization (f : k[X]) (m : ℕ) (gs : Fin m → k[X]) : Prop where
  pos : 0 < m
  prod_eq : f = ∏ i : Fin m, (gs i) ^ (i.val + 1)
  squarefree : ∀ i : Fin m, Squarefree (gs i)
  coprime : ∀ i j : Fin m, i ≠ j → IsCoprime (gs i) (gs j)
  last_ne_one : gs ⟨m - 1, Nat.sub_one_lt_of_lt pos⟩ ≠ 1

/-- Over a perfect field, an irreducible polynomial `g` satisfies `g² ∣ f` iff
both `g ∣ f` and `g ∣ f'`. The characterization used in Yun's algorithm to
detect squares. -/
theorem irreducible_sq_dvd_iff_dvd_derivative [PerfectField k]
    {f g : k[X]} (hirr : Irreducible g) :
    g ^ 2 ∣ f ↔ g ∣ f ∧ g ∣ derivative f := by
  constructor
  · intro hdvd
    refine ⟨dvd_trans (dvd_pow_self g two_ne_zero) hdvd, ?_⟩
    have h : g ^ 1 ∣ derivative f := pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rwa [pow_one] at h
  · intro ⟨hf, hf'⟩
    obtain ⟨h, rfl⟩ := hf
    rw [derivative_mul] at hf'
    have hg_dvd_g'h : g ∣ derivative g * h :=
      (dvd_add_left (dvd_mul_right g (derivative h))).mp hf'
    have hsep : g.Separable := PerfectField.separable_of_irreducible hirr
    have hg_dvd_h : g ∣ h := hsep.dvd_of_dvd_mul_left hg_dvd_g'h
    rw [pow_succ, pow_one]
    exact mul_dvd_mul_left g hg_dvd_h

/-- Refined form of the previous lemma: `g² ∣ f` iff `g` divides `gcd(f, f')`.
This is the divisibility used directly in Yun's algorithm to peel off the
squarefree part. -/
theorem irreducible_sq_dvd_iff_dvd_gcd_derivative [PerfectField k]
    {f g : k[X]} (hirr : Irreducible g) :
    g ^ 2 ∣ f ↔ g ∣ EuclideanDomain.gcd f (derivative f) := by
  rw [irreducible_sq_dvd_iff_dvd_derivative hirr]
  constructor
  · intro ⟨hf, hf'⟩
    exact EuclideanDomain.dvd_gcd hf hf'
  · intro h
    exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left f _),
           dvd_trans h (EuclideanDomain.gcd_dvd_right f _)⟩

/-- Loop state for Yun's algorithm (Algorithm 3.46): the running pair `(v_i, w_i)`
of polynomials whose GCD with the derivative-difference yields the next factor `g_i`. -/
structure YunState (k : Type*) [Field k] where
  v : k[X]
  w : k[X]

/-- One iteration of Yun's algorithm: from state `(v, w)`, compute
`g = gcd(v, w − v')`, then advance to the new state `(v/g, (w − v')/g)`. -/
noncomputable def yunStep (st : YunState k) : k[X] × YunState k :=
  let diff := st.w - derivative st.v
  let g := EuclideanDomain.gcd st.v diff
  let v_new := st.v / g
  let w_new := diff / g
  (g, ⟨v_new, w_new⟩)

/-- Initialization of Yun's algorithm: from input `f`, divide out `u = gcd(f, f')`
to set `v_1 = f/u` and `w_1 = f'/u`. -/
noncomputable def yunInit (f : k[X]) : YunState k :=
  let u := EuclideanDomain.gcd f (derivative f)
  ⟨f / u, derivative f / u⟩

/-- Iterate Yun's algorithm for a bounded number of steps `n`, collecting the
factor sequence `g_1, g_2, …`. Stops early when the current `v_i` equals the
computed `g_i`. -/
noncomputable def yunIterate (st : YunState k) : ℕ → List (k[X]) × YunState k
  | 0 => ([], st)
  | n + 1 =>
    let (g, st') := yunStep st
    if st.v = g then ([g], st')
    else
      let (gs, st'') := yunIterate st' n
      (g :: gs, st'')

/-- Top-level Yun's algorithm (Algorithm 3.46): start from `f`, initialize, and
iterate for at most `fuel` steps, returning the list of squarefree factors
`g_1, g_2, …, g_m`. -/
noncomputable def yunAlgorithm (f : k[X]) (fuel : ℕ) : List (k[X]) :=
  (yunIterate (yunInit f) fuel).1

/-- `simp` lemma: the first component of `yunStep` is `gcd(v, w − v')`. -/
@[simp]
theorem yunStep_fst (st : YunState k) :
    (yunStep st).1 = EuclideanDomain.gcd st.v (st.w - derivative st.v) := rfl

/-- `simp` lemma: the initial `v` in Yun's algorithm is `f / gcd(f, f')`. -/
@[simp]
theorem yunInit_v (f : k[X]) :
    (yunInit f).v = f / EuclideanDomain.gcd f (derivative f) := rfl

/-- `simp` lemma: the initial `w` in Yun's algorithm is `f' / gcd(f, f')`. -/
@[simp]
theorem yunInit_w (f : k[X]) :
    (yunInit f).w = derivative f / EuclideanDomain.gcd f (derivative f) := rfl


end SqfreeFactorization


section DistinctDegreeFactorization

variable {k : Type*} [Field k] [Fintype k]
open Classical

/-- The polynomial `X^{q^j} - X` over a finite field `k` of cardinality `q`.
Its roots are exactly the elements of the unique subfield `𝔽_{q^j} ⊆ k̄`, so its
factorization isolates irreducibles of degree dividing `j`. Used in
Algorithm 3.47 / Algorithm 3.46 for distinct-degree factorization. -/
noncomputable def xPowCardPowSubX (k : Type*) [Field k] [Fintype k] (j : ℕ) : k[X] :=
  X ^ (Fintype.card k) ^ j - X

/-- Definitional `simp` lemma for `xPowCardPowSubX`. -/
@[simp]
theorem xPowCardPowSubX_def (j : ℕ) :
    xPowCardPowSubX k j = X ^ (Fintype.card k) ^ j - X := rfl

/-- If an irreducible polynomial `g` divides `X^{q^j} − X`, then its degree
divides `j`. This is the key fact behind distinct-degree factorization: roots of
`X^{q^j} − X` lie in `𝔽_{q^j}`, whose irreducible factors over `𝔽_q` have degrees
dividing `j`. -/
theorem irreducible_dvd_xPowCardPowSubX_natDegree_dvd
    {j : ℕ} {g : k[X]} (hirr : Irreducible g)
    (hdvd : g ∣ xPowCardPowSubX k j) : g.natDegree ∣ j := by
  unfold xPowCardPowSubX at hdvd
  rw [show (Fintype.card k : ℕ) = Nat.card k from (Nat.card_eq_fintype_card).symm] at hdvd
  exact hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd

/-- One step of distinct-degree factorization: from `f`, compute
`g = gcd(f, X^{q^j} − X)` (the product of degree-`j` irreducible factors of `f`)
and the new remaining polynomial `f / g`. -/
noncomputable def distinctDegreeStep (f : k[X]) (j : ℕ) : k[X] × k[X] :=
  let g := EuclideanDomain.gcd f (xPowCardPowSubX k j)
  (g, f / g)

/-- `simp` lemma: the first component of `distinctDegreeStep` is `gcd(f, X^{q^j} − X)`. -/
@[simp]
theorem distinctDegreeStep_fst (f : k[X]) (j : ℕ) :
    (distinctDegreeStep f j).1 = EuclideanDomain.gcd f (xPowCardPowSubX k j) := rfl

/-- `simp` lemma: the second component of `distinctDegreeStep` is the quotient
`f / gcd(f, X^{q^j} − X)`. -/
@[simp]
theorem distinctDegreeStep_snd (f : k[X]) (j : ℕ) :
    (distinctDegreeStep f j).2 = f / EuclideanDomain.gcd f (xPowCardPowSubX k j) := rfl

/-- State for the distinct-degree factorization loop: the polynomial still left
to factor and the list of degree-`j` partial products accumulated so far. -/
structure DistinctDegreeState (k : Type*) [Field k] where
  remaining : k[X]
  factors : List (k[X])

/-- A single iteration of the distinct-degree factorization loop: extract the
product of degree-`j` irreducible factors of the current `remaining`, and append
it to the factor list. -/
noncomputable def distinctDegreeIter (st : DistinctDegreeState k) (j : ℕ) :
    DistinctDegreeState k :=
  let g := EuclideanDomain.gcd st.remaining (xPowCardPowSubX k j)
  { remaining := st.remaining / g
    factors := st.factors ++ [g] }

/-- Iterate distinct-degree factorization for `j = 1, 2, …, n`, starting from `f`. -/
noncomputable def distinctDegreeLoop (f : k[X]) : ℕ → DistinctDegreeState k
  | 0 => { remaining := f, factors := [] }
  | n + 1 => distinctDegreeIter (distinctDegreeLoop f n) (n + 1)

/-- Top-level distinct-degree factorization (step 2 of Algorithm 3.47): for input
`f`, run the loop up to degree `deg f` and return the list of degree-`j` factors. -/
noncomputable def distinctDegreeFactorize (f : k[X]) : List (k[X]) :=
  (distinctDegreeLoop f f.natDegree).factors

/-- Distinct-degree factorization specification (step 2 of Algorithm 3.47):
`f` factors as `∏ h_j` where each `h_j` is a (possibly trivial) squarefree
product of irreducibles all of degree `j+1`, and the `h_j` are pairwise coprime. -/
structure IsDistinctDegreeFactorization (f : k[X]) (d : ℕ) (hs : Fin d → k[X]) : Prop where
  prod_eq : f = ∏ i : Fin d, hs i
  irred_deg : ∀ (j : Fin d) (g : k[X]), Irreducible g → g ∣ hs j → g.natDegree = j.val + 1
  squarefree : ∀ j : Fin d, hs j = 1 ∨ Squarefree (hs j)
  coprime : ∀ i j : Fin d, i ≠ j → IsCoprime (hs i) (hs j)


end DistinctDegreeFactorization

end Polynomial
