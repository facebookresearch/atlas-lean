/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section Example_9_1

/-- `101` is prime, the modulus used in Example 9.1 where `G = 𝔽₁₀₁ˣ`. -/
theorem prime_101 : Nat.Prime 101 := by decide

/-- Example 9.1: in `𝔽₁₀₁ˣ`, `3^24 ≡ 37 (mod 101)`, witnessing `log₃ 37 = 24`. -/
theorem ex_9_1_pow : (3 : ZMod 101) ^ 24 = 37 := by decide

/-- The multiplicative group `(ZMod 101)ˣ` has order `100 = φ(101)`. -/
theorem card_units_101 : Fintype.card (ZMod 101)ˣ = 100 := by
  rw [ZMod.card_units_eq_totient]
  decide

/-- Prime factorization `100 = 2² · 5²`, used in analyzing the order of `𝔽₁₀₁ˣ`. -/
theorem order_factorization : (100 : ℕ) = 2 ^ 2 * 5 ^ 2 := by norm_num

end Example_9_1

section Example_9_2

/-- Example 9.2: in `𝔽₁₀₁⁺`, `46 · 3 ≡ 37 (mod 101)`, witnessing `log₃ 37 = 46`. -/
theorem ex_9_2_mul : (46 : ZMod 101) * 3 = 37 := by decide

/-- The additive group `ZMod 101` has cardinality `101`. -/
theorem card_ZMod_101 : Fintype.card (ZMod 101) = 101 :=
  ZMod.card 101

/-- `101` is prime, so `ZMod 101` is a field and `3` is invertible there. -/
theorem prime_order_101 : Nat.Prime 101 := by decide

/-- The inverse of `3` in `ZMod 101` is `34`. -/
theorem inv_3_mod_101 : (3 : ZMod 101)⁻¹ = 34 := by decide

/-- Computation: `log₃ 37 = 34 · 37 = 46` in `ZMod 101`, matching Example 9.2 via inversion. -/
theorem ex_9_2_via_inv : (34 : ZMod 101) * 37 = 46 := by decide

end Example_9_2

open Finset Real Filter Asymptotics MeasureTheory

section Theorem_9_3

/-- Probability that the first `n` steps of a random walk on a set of size `N`
all land on distinct vertices (the birthday-product `∏_{i<n} (1 - (i+1)/N)`). -/
noncomputable def birthdayProb (N : ℕ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - (↑(i + 1) : ℝ) / ↑N)

/-- Expected value of the rho-length for a random walk on a set of size `N`,
expressed as `∑_{n<N} birthdayProb N n`. Theorem 9.3 shows this is asymptotic to `√(πN/2)`. -/
noncomputable def expectedRho (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, birthdayProb N n

/-- Base case: the empty product is `1`, so `birthdayProb N 0 = 1`. -/
@[simp]
lemma birthdayProb_zero (N : ℕ) : birthdayProb N 0 = 1 := by
  simp [birthdayProb]

/-- Recursive relation: appending the `(n+1)`-th step multiplies by `1 - (n+1)/N`. -/
lemma birthdayProb_succ (N : ℕ) (n : ℕ) :
    birthdayProb N (n + 1) = birthdayProb N n * (1 - (↑(n + 1) : ℝ) / ↑N) := by
  simp [birthdayProb, Finset.prod_range_succ]

/-- Each factor `1 - (i+1)/N` is strictly positive when `i + 1 < N`. -/
lemma factor_pos {N : ℕ} {i : ℕ} (hN : 0 < N) (hi : i + 1 < N) :
    (0 : ℝ) < 1 - (↑(i + 1) : ℝ) / ↑N := by
  rw [sub_pos, div_lt_one (Nat.cast_pos.mpr hN)]; exact_mod_cast hi

/-- `birthdayProb N n` is strictly positive whenever `n < N`. -/
lemma birthdayProb_pos {N : ℕ} {n : ℕ} (hN : 0 < N) (hn : n < N) :
    0 < birthdayProb N n := by
  unfold birthdayProb; apply Finset.prod_pos
  intro i hi; rw [Finset.mem_range] at hi; exact factor_pos hN (by omega)

/-- `birthdayProb N n ≤ 1` whenever `n < N` (as a product of factors in `[0, 1)`). -/
lemma birthdayProb_le_one {N : ℕ} {n : ℕ} (hN : 0 < N) (hn : n < N) :
    birthdayProb N n ≤ 1 := by
  unfold birthdayProb; apply Finset.prod_le_one
  · intro i hi; rw [Finset.mem_range] at hi; exact le_of_lt (factor_pos hN (by omega))
  · intro i hi; rw [Finset.mem_range] at hi
    linarith [show (0 : ℝ) ≤ (↑(i + 1) : ℝ) / ↑N from by positivity]

/-- Concavity bound: `log(1 - x) ≤ -x` for the factor `x = (i+1)/N`. -/
lemma log_factor_le {N : ℕ} {i : ℕ} (hN : 0 < N) (hi : i + 1 < N) :
    Real.log (1 - (↑(i + 1) : ℝ) / ↑N) ≤ -(↑(i + 1) : ℝ) / ↑N := by
  have h1 : 0 < 1 - (↑(i + 1) : ℝ) / ↑N := factor_pos hN hi
  have h2 := Real.log_le_sub_one_of_pos h1
  linarith [show 1 - (↑(i + 1) : ℝ) / ↑N - 1 = -(↑(i + 1) : ℝ) / ↑N from by ring]

/-- Closed-form for the shifted arithmetic sum: `∑_{i<n} (i+1) = n(n+1)/2`. -/
lemma sum_range_succ_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, (↑(i + 1) : ℝ) = ↑n * (↑n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Exponential upper bound on `birthdayProb N n`, obtained by summing `log(1 - x) ≤ -x`. -/
lemma birthdayProb_le_exp {N : ℕ} {n : ℕ} (hN : 0 < N) (hn : n < N) :
    birthdayProb N n ≤ Real.exp (-(↑n * (↑n + 1) / (2 * ↑N))) := by
  rw [← Real.log_le_iff_le_exp (birthdayProb_pos hN hn)]
  unfold birthdayProb
  rw [Real.log_prod (fun i hi => by
    rw [Finset.mem_range] at hi; exact ne_of_gt (factor_pos hN (by omega)))]
  calc ∑ i ∈ Finset.range n, Real.log (1 - (↑(i + 1) : ℝ) / ↑N)
      ≤ ∑ i ∈ Finset.range n, (-(↑(i + 1) : ℝ) / ↑N) := by
        apply Finset.sum_le_sum; intro i hi; rw [Finset.mem_range] at hi
        exact log_factor_le hN (by omega)
    _ = -(↑n * (↑n + 1) / (2 * ↑N)) := by
        simp_rw [show ∀ i : ℕ, -(↑(i + 1) : ℝ) / (↑N : ℝ) = -(↑(i + 1) : ℝ) * ((↑N : ℝ)⁻¹)
          from fun i => by ring]
        rw [← Finset.sum_mul, Finset.sum_neg_distrib, sum_range_succ_cast]; ring

/-- Quadratic exponential bound: `birthdayProb N n ≤ exp(-n²/(2N))`, the more
convenient form used in the Gaussian comparison. -/
lemma birthdayProb_le_exp_sq {N : ℕ} {n : ℕ} (hN : 0 < N) (hn : n < N) :
    birthdayProb N n ≤ Real.exp (-((↑n : ℝ) ^ 2 / (2 * ↑N))) :=
  calc birthdayProb N n
      ≤ Real.exp (-(↑n * (↑n + 1) / (2 * ↑N))) := birthdayProb_le_exp hN hn
    _ ≤ Real.exp (-((↑n : ℝ) ^ 2 / (2 * ↑N))) := by
        apply Real.exp_le_exp_of_le; apply neg_le_neg
        apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < 2 * ↑N).le
        nlinarith [sq_nonneg (n : ℝ)]

/-- Gaussian half-line integral: `∫₀^∞ exp(-x²/(2N)) dx = √(πN/2)`. -/
lemma gaussian_integral_half_line (N : ℝ) (hN : 0 < N) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(1 / (2 * N)) * x ^ 2) = √(π * N / 2) := by
  rw [integral_gaussian_Ioi]
  conv_lhs =>
    rw [show π / (1 / (2 * N)) = 4 * (π * N / 2) from by field_simp; ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show √(4 : ℝ) = 2 from by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]; exact Real.sqrt_sq (by norm_num)]
  ring

/-- The Riemann sum `∑_{n<N} exp(-n²/(2N))` is asymptotic to the Gaussian integral
`√(πN/2)`. This is the analytic engine behind Theorem 9.3. -/
theorem gaussian_sum_asymptotic :
    (fun N : ℕ => ∑ n ∈ Finset.range N,
      Real.exp (-((↑n : ℝ) ^ 2 / (2 * ↑N)))) ~[atTop]
    (fun N : ℕ => √(π * ↑N / 2)) := by


  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N,
    Real.exp (-((↑n : ℝ) ^ 2 / (2 * ↑N)))
  set V : ℕ → ℝ := fun N => √(π * ↑N / 2)
  show (S - V) =o[atTop] V

  have hO : (S - V) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with N hN
    simp only [Pi.sub_apply, Real.norm_eq_abs, norm_one, mul_one]
    have hN' : (0 : ℕ) < N := by omega

    have hanti : AntitoneOn (fun x : ℝ => Real.exp (-(x ^ 2 / (2 * ↑N))))
        (Set.Icc 0 ↑N) := by
      intro a ha b hb hab
      apply Real.exp_le_exp_of_le; apply neg_le_neg
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < 2 * ↑N).le
      exact sq_le_sq' (by linarith [ha.1, hb.2]) hab

    have hLB : ∫ x in (0 : ℝ)..(↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) ≤ S N := by
      have h := AntitoneOn.integral_le_sum (x₀ := 0) (a := N)
        (f := fun x => Real.exp (-(x ^ 2 / (2 * ↑N)))) (by simp [hanti])
      simp only [zero_add] at h; exact h

    have hShift : S N ≤ 1 + ∑ i ∈ Finset.range N,
        Real.exp (-(↑(i + 1) ^ 2 / (2 * ↑N))) := by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      show ∑ n ∈ Finset.range (M + 1), _ ≤ _
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_div, neg_zero, Real.exp_zero]
      linarith [Finset.sum_le_sum_of_subset_of_nonneg
        (s := Finset.range M) (t := Finset.range (M + 1))
        (f := fun i => Real.exp (-(↑(i + 1) ^ 2 / (2 * ↑(M + 1)))))
        (Finset.range_mono (Nat.le_succ M))
        (fun i _ _ => Real.exp_nonneg _)]

    have hRS : ∑ i ∈ Finset.range N, Real.exp (-(↑(i + 1) ^ 2 / (2 * ↑N))) ≤
        ∫ x in (0 : ℝ)..(↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) := by
      have h := AntitoneOn.sum_le_integral (x₀ := 0) (a := N)
        (f := fun x => Real.exp (-(x ^ 2 / (2 * ↑N)))) (by simp [hanti])
      simp only [zero_add] at h; exact h

    have hGauss : V N = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) := by
      simp_rw [show ∀ x : ℝ, -(x ^ 2 / (2 * ↑N)) = -(1 / (2 * ↑N)) * x ^ 2
        from fun x => by ring]
      rw [integral_gaussian_Ioi]
      rw [show π / (1 / (2 * (↑N : ℝ))) = 4 * (π * ↑N / 2) from by field_simp; ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        show √(4 : ℝ) = 2 from by
          rw [show (4:ℝ) = 2^2 from by norm_num]; exact Real.sqrt_sq (by norm_num)]
      ring

    have hIntUB : ∫ x in (0 : ℝ)..(↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) ≤ V N := by
      rw [hGauss, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ ↑N)]
      apply MeasureTheory.setIntegral_mono_set
      · have hb : (0 : ℝ) < 1 / (2 * ↑N) := by positivity
        exact (integrable_exp_neg_mul_sq hb).integrableOn.congr
          (Filter.Eventually.of_forall (fun x => by ring_nf))
      · exact Filter.Eventually.of_forall (fun x => Real.exp_nonneg _)
      · exact Filter.Eventually.of_forall (fun x hx => hx.1)

    have hIntLB : V N - 2 ≤
        ∫ x in (0 : ℝ)..(↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) := by

      have hdecomp : Set.Ioi (0 : ℝ) = Set.Ioc 0 ↑N ∪ Set.Ioi ↑N := by
        ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]; constructor
        · intro hx; rcases le_or_gt x ↑N with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
        · rintro (⟨hx, _⟩ | hx)
          · exact hx
          · linarith
      have hb : (0 : ℝ) < 1 / (2 * ↑N) := by positivity
      have hfI : IntegrableOn (fun x => Real.exp (-(x ^ 2 / (2 * ↑N)))) (Set.Ioi 0) :=
        (integrable_exp_neg_mul_sq hb).integrableOn.congr
          (ae_of_all _ (fun x => by ring_nf))
      have hSplit : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N)))) =
          (∫ x in Set.Ioc (0 : ℝ) ↑N, Real.exp (-(x ^ 2 / (2 * ↑N)))) +
          (∫ x in Set.Ioi ↑N, Real.exp (-(x ^ 2 / (2 * ↑N)))) := by
        conv_lhs => rw [hdecomp]
        exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hfI.mono_set (hdecomp ▸ Set.subset_union_left))
          (hfI.mono_set (hdecomp ▸ Set.subset_union_right))
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ ↑N), hGauss]

      have h2N : (0 : ℝ) < 2 * ↑N := by positivity
      have htail : ∫ x in Set.Ioi (↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N))) ≤ 2 :=
        calc ∫ x in Set.Ioi (↑N : ℝ), Real.exp (-(x ^ 2 / (2 * ↑N)))
            ≤ ∫ x in Set.Ioi (↑N : ℝ), Real.exp (-(1/2) * x) := by
              apply setIntegral_mono_on
              · exact hfI.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ ↑N by positivity))
              · exact (exp_neg_integrableOn_Ioi ↑N (by norm_num : (0:ℝ) < 1/2)).congr
                  (ae_of_all _ (fun x => by ring_nf))
              · exact measurableSet_Ioi
              · intro x hx
                apply Real.exp_le_exp_of_le
                by_contra h
                push_neg at h
                have h1 : x ^ 2 / (2 * ↑N) < 1 / 2 * x := by linarith
                have h2 : x ^ 2 < x * ↑N := by
                  have := (div_lt_iff₀ h2N).mp h1; nlinarith
                nlinarith [sq_nonneg (x - ↑N), Set.mem_Ioi.mp hx]
          _ = 2 * Real.exp (-(↑N / 2)) := by
              convert integral_exp_mul_Ioi (show -(1:ℝ)/2 < 0 by norm_num) ↑N using 1
              · congr 1; ext x; ring
              · ring
          _ ≤ 2 := by
              have : Real.exp (-(↑N / 2)) ≤ 1 :=
                Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
              linarith [mul_le_of_le_one_right (by norm_num : (0:ℝ) ≤ 2) this]
      linarith [hSplit]

    rw [abs_le]; constructor
    · linarith [hLB, hIntLB]
    · linarith [hShift, hRS, hIntUB]

  have ho : (fun _ : ℕ => (1 : ℝ)) =o[atTop] V := by
    rw [isLittleO_one_left_iff ℝ]
    apply Filter.Tendsto.comp tendsto_norm_atTop_atTop
    exact tendsto_sqrt_atTop.comp (by
      apply Filter.Tendsto.atTop_div_const (by positivity : (0 : ℝ) < 2)
      exact (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by positivity : (0 : ℝ) < π))
  exact hO.trans_isLittleO ho

/-- `expectedRho N` is bounded above by the Gaussian Riemann sum, term-by-term. -/
lemma expectedRho_le_gaussianSum {N : ℕ} (hN : 0 < N) :
    expectedRho N ≤ ∑ n ∈ Finset.range N,
      Real.exp (-((↑n : ℝ) ^ 2 / (2 * ↑N))) :=
  Finset.sum_le_sum fun n hn => birthdayProb_le_exp_sq hN (Finset.mem_range.mp hn)

/-- Lower bound on `log(1 - x)`: `log(1 - x) ≥ -x - x²/(1 - x)` for `0 ≤ x < 1`. -/
lemma log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -x - x^2 / (1-x) ≤ Real.log (1 - x) := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · simp
  have h := Real.abs_log_sub_add_sum_range_le (abs_lt.mpr ⟨by linarith, hx1⟩) 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, pow_succ] at h
  rw [abs_of_nonneg hx0'.le] at h; rw [abs_le] at h
  have h1 := h.1; simp only [pow_zero, one_mul, div_one] at h1
  rw [show x ^ 2 / (1 - x) = x * x / (1 - x) from by ring]; linarith

/-- For `x ≤ 1/2`, `log(1 - x) ≥ -x - 2x²`, a clean version of the lower bound. -/
lemma log_one_sub_ge' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    -x - 2*x^2 ≤ Real.log (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  calc -x - 2*x^2 ≤ -x - x^2/(1-x) := by
        apply sub_le_sub_left; rw [div_le_iff₀ h1x]; nlinarith [sq_nonneg x]
    _ ≤ Real.log (1-x) := log_one_sub_ge hx0 (by linarith)



end Theorem_9_3

section Algorithm_9_5

variable {G : Type*} [AddCommGroup G]
variable {N : ℕ} [NeZero N]

/-- A triple `(a, b, γ)` tracked by the Pollard-ρ walk for the DLP: scalars
`a, b ∈ ℤ/Nℤ` together with the corresponding group element `γ = a·α + b·β`. -/
@[ext]
structure PollardRhoTriple (N : ℕ) (G : Type*) where
  a : ZMod N
  b : ZMod N
  γ : G

/-- Configuration for Pollard's rho algorithm (Algorithm 9.5): the generator `α`,
the target `β = log_α^{-1} β`, the number `r` of partition classes (with `0 < r`),
the per-class scalar offsets `c`, `d` and group offsets `δ`, and a partition map `h : G → Fin r`. -/
structure PollardRhoConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N] where
  α : G
  β : G
  r : ℕ
  hr : 0 < r
  c : Fin r → ZMod N
  d : Fin r → ZMod N
  δ : Fin r → G
  h : G → Fin r

variable [Module (ZMod N) G]

/-- A triple is valid for `cfg` when `γ = a • α + b • β`, i.e. it tracks the correct
linear combination. -/
def PollardRhoTriple.IsValid (cfg : PollardRhoConfig G N) (t : PollardRhoTriple N G) : Prop :=
  t.a • cfg.α + t.b • cfg.β = t.γ

/-- A partition is valid when each class offset `δ i` equals `c i • α + d i • β`,
so applying a partition step preserves the invariant `γ = a • α + b • β`. -/
def PollardRhoConfig.PartitionValid (cfg : PollardRhoConfig G N) : Prop :=
  ∀ i : Fin cfg.r, cfg.δ i = cfg.c i • cfg.α + cfg.d i • cfg.β

/-- One step of the Pollard-ρ iteration: identify the class `i = h(γ)` and add
`(c i, d i, δ i)` to the triple. -/
def pollardRhoStep (cfg : PollardRhoConfig G N) (t : PollardRhoTriple N G) :
    PollardRhoTriple N G :=
  let i := cfg.h t.γ
  { a := t.a + cfg.c i
    b := t.b + cfg.d i
    γ := t.γ + cfg.δ i }

/-- Under `PartitionValid`, a single `pollardRhoStep` preserves the invariant
`γ = a • α + b • β`. -/
theorem pollardRhoStep_preserves_invariant
    (cfg : PollardRhoConfig G N) (t : PollardRhoTriple N G)
    (hpart : cfg.PartitionValid) (hinv : t.IsValid cfg) :
    (pollardRhoStep cfg t).IsValid cfg := by
  simp only [pollardRhoStep, PollardRhoTriple.IsValid] at *
  rw [add_smul, add_smul, hpart (cfg.h t.γ), ← hinv]; abel

/-- Collision relation: if two valid triples have the same group element `γ`,
then `(a₁ - a₂) • α = (b₂ - b₁) • β`. This is the linear identity that the
discrete log is extracted from. -/
theorem pollardRho_collision_relation
    (cfg : PollardRhoConfig G N)
    (t₁ t₂ : PollardRhoTriple N G)
    (h₁ : t₁.IsValid cfg) (h₂ : t₂.IsValid cfg)
    (hcoll : t₁.γ = t₂.γ) :
    (t₁.a - t₂.a) • cfg.α = (t₂.b - t₁.b) • cfg.β := by
  simp only [PollardRhoTriple.IsValid] at h₁ h₂
  rw [sub_smul, sub_smul]
  have key : t₁.a • cfg.α + t₁.b • cfg.β - (t₂.a • cfg.α + t₁.b • cfg.β) =
      t₂.a • cfg.α + t₂.b • cfg.β - (t₂.a • cfg.α + t₁.b • cfg.β) := by
    rw [h₁, h₂, hcoll]
  have lhs : t₁.a • cfg.α + t₁.b • cfg.β - (t₂.a • cfg.α + t₁.b • cfg.β) =
      t₁.a • cfg.α - t₂.a • cfg.α := by abel
  have rhs : t₂.a • cfg.α + t₂.b • cfg.β - (t₂.a • cfg.α + t₁.b • cfg.β) =
      t₂.b • cfg.β - t₁.b • cfg.β := by abel
  rw [lhs, rhs] at key
  exact key

/-- DLP extraction (Algorithm 9.5, step 4): if `b₂ - b₁` is invertible in `ℤ/Nℤ`,
solve the collision relation for `β = ((b₂ - b₁)⁻¹ (a₁ - a₂)) • α`, recovering `log_α β`. -/
theorem pollardRho_dlog_extraction
    (cfg : PollardRhoConfig G N)
    (t₁ t₂ : PollardRhoTriple N G)
    (h₁ : t₁.IsValid cfg) (h₂ : t₂.IsValid cfg)
    (hcoll : t₁.γ = t₂.γ)
    (hinv : IsUnit (t₂.b - t₁.b)) :
    cfg.β = ((t₂.b - t₁.b)⁻¹ * (t₁.a - t₂.a)) • cfg.α := by
  have key := pollardRho_collision_relation cfg t₁ t₂ h₁ h₂ hcoll
  have step := congr_arg ((t₂.b - t₁.b)⁻¹ • ·) key
  simp only [← mul_smul] at step
  rw [ZMod.inv_mul_of_unit _ hinv, one_smul] at step
  exact step.symm

/-- Iterate `pollardRhoStep` starting from `t₀` for `n` steps. -/
def pollardRhoIter (cfg : PollardRhoConfig G N) (t₀ : PollardRhoTriple N G) :
    ℕ → PollardRhoTriple N G
  | 0 => t₀
  | n + 1 => pollardRhoStep cfg (pollardRhoIter cfg t₀ n)

/-- Iterating preserves the invariant `γ = a • α + b • β` under `PartitionValid`. -/
theorem pollardRhoIter_preserves_invariant
    (cfg : PollardRhoConfig G N) (t₀ : PollardRhoTriple N G)
    (hpart : cfg.PartitionValid) (h₀ : t₀.IsValid cfg)
    (n : ℕ) : (pollardRhoIter cfg t₀ n).IsValid cfg := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact pollardRhoStep_preserves_invariant cfg _ hpart ih

omit [Module (ZMod N) G] in
/-- The `γ`-component of `pollardRhoIter` depends only on the initial `γ`, not on the
initial scalar coordinates `(a, b)`. -/
theorem pollardRhoIter_gamma_independent
    (cfg : PollardRhoConfig G N)
    (t₁ t₂ : PollardRhoTriple N G)
    (hγ : t₁.γ = t₂.γ) (n : ℕ) :
    (pollardRhoIter cfg t₁ n).γ = (pollardRhoIter cfg t₂ n).γ := by
  induction n with
  | zero => exact hγ
  | succ n ih =>
    simp only [pollardRhoIter, pollardRhoStep]
    rw [ih]

end Algorithm_9_5

section Theorem_9_7_Shoup

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Evaluate the affine function `t ↦ a t + b` over `ZMod p` at `t`, where `ab = (a, b)`. -/
def evalAffine (ab : ZMod p × ZMod p) (t : ZMod p) : ZMod p :=
  ab.1 * t + ab.2

/-- A nonzero affine function `t ↦ a t + b` over a field `ZMod p` has at most one root. -/
lemma card_roots_affine_le_one
    (ab : ZMod p × ZMod p) (hab : ab ≠ (0, 0)) :
    (Finset.univ.filter (fun t : ZMod p => evalAffine ab t = 0)).card ≤ 1 := by
  classical
  obtain ⟨a, b⟩ := ab
  simp only [evalAffine] at *
  by_cases ha : a = 0
  ·
    have hb : b ≠ 0 := by intro hb; exact hab (Prod.ext ha hb)
    have : ∀ t : ZMod p, ¬(0 * t + b = 0) := by intro t; simp [hb]
    simp only [ha, this, Finset.filter_false]; simp
  ·
    rw [Finset.card_le_one]
    intro t₁ ht₁ t₂ ht₂
    rw [Finset.mem_filter] at ht₁ ht₂
    obtain ⟨_, h1⟩ := ht₁; obtain ⟨_, h2⟩ := ht₂
    have h1' : a * t₁ = -b := by rwa [add_eq_zero_iff_eq_neg] at h1
    have h2' : a * t₂ = -b := by rwa [add_eq_zero_iff_eq_neg] at h2
    exact mul_left_cancel₀ ha (h1'.trans h2'.symm)

/-- Two distinct affine functions `f, g` over `ZMod p` agree on at most one value of `t`. -/
lemma card_collision_pair_le_one (f g : ZMod p × ZMod p) (hfg : f ≠ g) :
    (Finset.univ.filter (fun t : ZMod p => evalAffine f t = evalAffine g t)).card ≤ 1 := by
  have heq : ∀ t : ZMod p, (evalAffine f t = evalAffine g t) ↔
      evalAffine (f.1 - g.1, f.2 - g.2) t = 0 := by
    intro t; simp only [evalAffine]
    constructor
    · intro h; have := sub_eq_zero.mpr h; linear_combination this
    · intro h
      have : f.1 * t + f.2 - (g.1 * t + g.2) = 0 := by linear_combination h
      exact sub_eq_zero.mp this
  simp_rw [heq]
  apply card_roots_affine_le_one
  intro h; apply hfg
  exact Prod.ext (sub_eq_zero.mp (congr_arg Prod.fst h)) (sub_eq_zero.mp (congr_arg Prod.snd h))

/-- The number of strictly ordered pairs in `Fin s × Fin s` is `s(s-1)/2`. -/
lemma card_lt_pairs_eq (s : ℕ) :
    (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2)).card = s * (s - 1) / 2 := by
  suffices h : 2 * (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2)).card =
      s * (s - 1) by omega

  have h_sym : (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2)).card =
      (Finset.univ.filter (fun ij : Fin s × Fin s => ij.2 < ij.1)).card := by
    apply Finset.card_equiv (Equiv.prodComm (Fin s) (Fin s))
    intro ⟨i, j⟩; simp [Equiv.prodComm]

  have h_union : (Finset.univ : Finset (Fin s)).offDiag =
      Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2) ∪
      Finset.univ.filter (fun ij : Fin s × Fin s => ij.2 < ij.1) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => (ne_iff_lt_or_gt.mp h).imp id id,
           fun h => h.elim ne_of_lt ne_of_gt⟩
  have h_disj : Disjoint
      (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2))
      (Finset.univ.filter (fun ij : Fin s × Fin s => ij.2 < ij.1)) := by
    rw [Finset.disjoint_filter]
    intro ⟨i, j⟩ _ h1 h2; exact absurd h1 (not_lt.mpr h2.le)

  have h_card_offDiag : (Finset.univ : Finset (Fin s)).offDiag.card = s * s - s := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  rw [h_union, Finset.card_union_of_disjoint h_disj, h_sym] at h_card_offDiag
  have h_ss : s * s - s = s * (s - 1) := by
    cases s with | zero => simp | succ n => simp [Nat.succ_mul]; ring
  omega

/-- Real-valued upper bound: `binom(s, 2) ≤ s²/2`. -/
lemma choose_two_le_sq_div_two (s : ℕ) : (Nat.choose s 2 : ℝ) ≤ s ^ 2 / 2 := by
  rw [Nat.choose_two_right]
  have : s * (s - 1) ≤ s * s := Nat.mul_le_mul_left s (Nat.sub_le s 1)
  calc (↑(s * (s - 1) / 2) : ℝ)
      ≤ ↑(s * (s - 1)) / 2 := Nat.cast_div_le
    _ ≤ ↑(s * s) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast this
    _ = s ^ 2 / 2 := by push_cast; ring

/-- Shoup's collision set: the set of `t ∈ ZMod p` such that two distinct affine
encodings `F i ≠ F j` (with `i < j`) collide at `t`. The generic-group adversary
can only succeed on these `t`. -/
noncomputable def collisionSet (s : ℕ) (F : Fin s → ZMod p × ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun t : ZMod p =>
    ∃ i j : Fin s, i < j ∧ F i ≠ F j ∧ evalAffine (F i) t = evalAffine (F j) t)

/-- The collision set has cardinality at most `s(s-1)/2`: at most one collision per
ordered pair of distinct affine encodings. -/
lemma card_collisionSet_le (s : ℕ) (F : Fin s → ZMod p × ZMod p) :
    (collisionSet s F).card ≤ s * (s - 1) / 2 := by
  classical

  let pairs := Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2 ∧ F ij.1 ≠ F ij.2)
  let rootSet (ij : Fin s × Fin s) : Finset (ZMod p) :=
    Finset.univ.filter (fun t => evalAffine (F ij.1) t = evalAffine (F ij.2) t)
  have h_sub : collisionSet s F ⊆ pairs.biUnion rootSet := by
    intro t ht
    simp only [collisionSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨i, j, hij, hne, heq⟩ := ht
    simp only [pairs, rootSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(i, j), ⟨hij, hne⟩, heq⟩

  have h_biUnion := Finset.card_biUnion_le (s := pairs) (t := rootSet)

  have h_each : ∀ ij ∈ pairs, (rootSet ij).card ≤ 1 := by
    intro ⟨i, j⟩ hij
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    exact card_collision_pair_le_one (F i) (F j) hij.2

  have h_sum : ∑ ij ∈ pairs, (rootSet ij).card ≤ pairs.card := by
    calc ∑ ij ∈ pairs, (rootSet ij).card ≤ ∑ ij ∈ pairs, 1 := Finset.sum_le_sum h_each
      _ = pairs.card := by simp

  have h_pairs : pairs.card ≤
      (Finset.univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2)).card := by
    apply Finset.card_le_card
    intro ⟨i, j⟩ hij
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    exact hij.1

  rw [card_lt_pairs_eq] at h_pairs
  calc (collisionSet s F).card
      ≤ (pairs.biUnion rootSet).card := Finset.card_le_card h_sub
    _ ≤ ∑ ij ∈ pairs, (rootSet ij).card := h_biUnion
    _ ≤ pairs.card := h_sum
    _ ≤ s * (s - 1) / 2 := h_pairs

/-- Non-strict Shoup bound: `|collisionSet| / p ≤ s²/(2p)`. -/
lemma shoup_bound_le (s : ℕ) (F : Fin s → ZMod p × ZMod p) :
    ((collisionSet s F).card : ℝ) / (Fintype.card (ZMod p)) ≤ s ^ 2 / (2 * p) := by
  rw [ZMod.card p]
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos

  have h_card := card_collisionSet_le s F

  calc ((collisionSet s F).card : ℝ) / p
      ≤ (s * (s - 1) / 2 : ℕ) / p := by
        apply div_le_div_of_nonneg_right _ hp'.le
        exact_mod_cast h_card
    _ ≤ (s ^ 2 / 2 : ℝ) / p := by
        apply div_le_div_of_nonneg_right _ hp'.le
        calc (↑(s * (s - 1) / 2) : ℝ) ≤ ↑(s * (s - 1)) / 2 := Nat.cast_div_le
          _ ≤ ↑(s * s) / 2 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              exact_mod_cast Nat.mul_le_mul_left s (Nat.sub_le s 1)
          _ = s ^ 2 / 2 := by push_cast; ring
    _ = s ^ 2 / (2 * p) := by ring

/-- Theorem 9.7 (Shoup, strict form): for `s ≥ 1`, the success probability of any
generic algorithm making at most `s` queries on `ZMod p` is strictly less than `s²/(2p)`. -/
theorem shoup_bound (s : ℕ) (hs : 1 ≤ s) (F : Fin s → ZMod p × ZMod p) :
    ((collisionSet s F).card : ℝ) / (Fintype.card (ZMod p)) < s ^ 2 / (2 * p) := by
  rw [ZMod.card p]
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos

  have h_card := card_collisionSet_le s F

  have h_strict : s * (s - 1) < s * s := by
    have : 0 < s := by omega
    have : s - 1 < s := Nat.sub_lt this Nat.one_pos
    exact Nat.mul_lt_mul_of_pos_left this (by omega)

  calc ((collisionSet s F).card : ℝ) / p
      ≤ (s * (s - 1) / 2 : ℕ) / p := by
        apply div_le_div_of_nonneg_right _ hp'.le
        exact_mod_cast h_card
    _ ≤ ↑(s * (s - 1)) / 2 / p := by
        apply div_le_div_of_nonneg_right _ hp'.le
        exact Nat.cast_div_le
    _ < ↑(s * s) / 2 / p := by
        apply div_lt_div_of_pos_right _ hp'
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast h_strict
    _ = s ^ 2 / (2 * p) := by push_cast; ring

end Theorem_9_7_Shoup

section Corollary_9_8

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Squared form of Corollary 9.8: if a deterministic generic DLP algorithm succeeds
on every `t ∈ ZMod p` (i.e., the collision set is everything) using `s` group operations,
then `s² ≥ 2p`. -/
lemma corollary_9_8_sq
    (s : ℕ) (F : Fin s → ZMod p × ZMod p)
    (h_det : collisionSet s F = Finset.univ) :
    2 * (↑p : ℝ) ≤ (↑s : ℝ) ^ 2 := by
  have hp' : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos
  have h_shoup := shoup_bound_le s F
  rw [h_det, Finset.card_univ, ZMod.card p] at h_shoup
  have h1 : (1 : ℝ) ≤ (↑s : ℝ) ^ 2 / (2 * ↑p) :=
    calc (1 : ℝ) = (↑p : ℝ) / (↑p : ℝ) := (div_self (ne_of_gt hp')).symm
      _ ≤ (↑s : ℝ) ^ 2 / (2 * ↑p) := h_shoup
  have h2pos : (0 : ℝ) < 2 * ↑p := by positivity
  have := (le_div_iff₀ h2pos).mp h1; linarith

/-- Corollary 9.8 (Sutherland): every deterministic generic DLP algorithm in a
cyclic group of prime order `p` uses at least `√(2p)` group operations. -/
theorem corollary_9_8
    (s : ℕ) (F : Fin s → ZMod p × ZMod p)
    (h_det : collisionSet s F = Finset.univ) :
    √(2 * ↑p) ≤ (↑s : ℝ) := by
  have h2 := corollary_9_8_sq s F h_det
  calc √(2 * ↑p) ≤ √((↑s : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
    _ = |↑s| := Real.sqrt_sq_eq_abs ↑s
    _ = ↑s := abs_of_nonneg (Nat.cast_nonneg s)

end Corollary_9_8

section Corollary_9_8_Group

variable {N : ℕ} [hN : Fact (Nat.Prime N)]

/-- Group-theoretic form of Corollary 9.8: for a finite cyclic group `G` of prime order `N`,
every deterministic generic DLP algorithm uses at least `√2 · √|G|` operations. -/
theorem corollary_9_8_group
    (G : Type*) [Group G] [Fintype G] [IsCyclic G]
    (hcard : Fintype.card G = N)
    (s : ℕ) (F : Fin s → ZMod N × ZMod N)
    (h_det : collisionSet s F = Finset.univ) :
    √2 * √(↑(Fintype.card G) : ℝ) ≤ (↑s : ℝ) := by
  rw [hcard]
  have h := corollary_9_8 s F h_det
  calc √2 * √(↑N : ℝ) = √(2 * ↑N) := (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _).symm
    _ ≤ ↑s := h

/-- Squared group-theoretic form of Corollary 9.8: `s² ≥ 2 |G|`. -/
theorem corollary_9_8_group_sq
    (G : Type*) [Group G] [Fintype G] [IsCyclic G]
    (hcard : Fintype.card G = N)
    (s : ℕ) (F : Fin s → ZMod N × ZMod N)
    (h_det : collisionSet s F = Finset.univ) :
    2 * (↑(Fintype.card G) : ℝ) ≤ (↑s : ℝ) ^ 2 := by
  rw [hcard]
  exact corollary_9_8_sq s F h_det

end Corollary_9_8_Group

section Corollary_9_9

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Corollary 9.9 (Sutherland): every generic Monte Carlo DLP algorithm in a cyclic
group of prime order `p` that uses `o(√p / log p)` random group elements still requires
at least `(1 + o(1))√p` group operations. The lemma extracts the quantitative
inequalities `√p ≤ s` and `√p - √p/log p < s - r`. -/
theorem corollary_9_9
    (s : ℕ) (F : Fin s → ZMod p × ZMod p)
    (r : ℕ)
    (hr : (r : ℝ) < √(↑p) / Real.log ↑p)
    (successSet : Finset (ZMod p))
    (h_sub : successSet ⊆ collisionSet s F)
    (h_mc : 1 / 2 ≤ (successSet.card : ℝ) / (Fintype.card (ZMod p))) :
    √(↑p) ≤ (↑s : ℝ) ∧
    √(↑p) - √(↑p) / Real.log ↑p < (↑s : ℝ) - (↑r : ℝ) := by
  have hp' : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos

  have h_success_le_collision : (successSet.card : ℝ) / (Fintype.card (ZMod p)) ≤
      ((collisionSet s F).card : ℝ) / (Fintype.card (ZMod p)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card h_sub

  have h_shoup := shoup_bound_le s F
  have h1 : (1 : ℝ) / 2 ≤ (↑s : ℝ) ^ 2 / (2 * ↑p) :=
    le_trans h_mc (le_trans h_success_le_collision h_shoup)
  have h2pos : (0 : ℝ) < 2 * ↑p := by positivity
  have h2 : (↑p : ℝ) ≤ (↑s : ℝ) ^ 2 := by
    have h3 : 1 / 2 * (2 * ↑p) ≤ (↑s : ℝ) ^ 2 := by
      rwa [le_div_iff₀ h2pos] at h1
    nlinarith

  have h_core : √(↑p) ≤ (↑s : ℝ) :=
    calc √(↑p) ≤ √((↑s : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = |↑s| := Real.sqrt_sq_eq_abs ↑s
      _ = ↑s := abs_of_nonneg (Nat.cast_nonneg s)

  exact ⟨h_core, by linarith⟩

end Corollary_9_9

section LargestPrimeFactor

/-- The largest prime factor of `N > 1`, used by Shoup's bound to express the
generic-group lower bound in terms of the hardest prime-order subgroup. -/
noncomputable def largestPrimeFactor (N : ℕ) (hN : 1 < N) : ℕ :=
  (N.primeFactors).max' (Nat.nonempty_primeFactors.mpr hN)

/-- The largest prime factor of `N > 1` is itself prime. -/
lemma largestPrimeFactor_prime (N : ℕ) (hN : 1 < N) :
    Nat.Prime (largestPrimeFactor N hN) := by
  have h := Finset.max'_mem _ (Nat.nonempty_primeFactors.mpr hN)
  exact (Nat.mem_primeFactors.mp h).1

/-- The largest prime factor divides `N`. -/
lemma largestPrimeFactor_dvd (N : ℕ) (hN : 1 < N) :
    largestPrimeFactor N hN ∣ N := by
  have h := Finset.max'_mem _ (Nat.nonempty_primeFactors.mpr hN)
  exact (Nat.mem_primeFactors.mp h).2.1

/-- Any prime factor of `N` is bounded above by the largest prime factor. -/
lemma le_largestPrimeFactor {N q : ℕ} (hN : 1 < N) (hq : q ∈ N.primeFactors) :
    q ≤ largestPrimeFactor N hN :=
  Finset.le_max' _ _ hq

/-- When `p` is itself prime, its largest prime factor is `p`. -/
lemma largestPrimeFactor_prime_eq (p : ℕ) (hp : Nat.Prime p) :
    largestPrimeFactor p hp.one_lt = p := by
  simp [largestPrimeFactor, hp.primeFactors]

/-- The largest prime factor is positive. -/
lemma largestPrimeFactor_pos (N : ℕ) (hN : 1 < N) :
    0 < largestPrimeFactor N hN :=
  (largestPrimeFactor_prime N hN).pos

/-- Package the primality of the largest prime factor as a `Fact`, for use with
typeclass-driven lemmas like `ZMod.card`. -/
lemma largestPrimeFactor_fact (N : ℕ) (hN : 1 < N) :
    Fact (Nat.Prime (largestPrimeFactor N hN)) :=
  ⟨largestPrimeFactor_prime N hN⟩

end LargestPrimeFactor

section Theorem_9_7_Full

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Any DLP success set contained in the collision set has probability bounded by
the collision-set probability. -/
lemma dlp_success_le_collision_prob (s : ℕ)
    (F : Fin s → ZMod p × ZMod p)
    (successSet : Finset (ZMod p))
    (h_sub : successSet ⊆ collisionSet s F) :
    (successSet.card : ℝ) / (Fintype.card (ZMod p)) ≤
    (collisionSet s F).card / (Fintype.card (ZMod p)) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card h_sub

/-- Theorem 9.7 (Shoup) for prime modulus: any DLP success probability for `s`
generic queries is at most `s²/(2p)`. -/
theorem shoup_theorem_9_7_prime (s : ℕ) (F : Fin s → ZMod p × ZMod p)
    (successSet : Finset (ZMod p))
    (h_sub : successSet ⊆ collisionSet s F) :
    (successSet.card : ℝ) / (Fintype.card (ZMod p)) ≤ s ^ 2 / (2 * p) :=
  calc (successSet.card : ℝ) / (Fintype.card (ZMod p))
      ≤ (collisionSet s F).card / (Fintype.card (ZMod p)) :=
        dlp_success_le_collision_prob s F successSet h_sub
    _ ≤ s ^ 2 / (2 * p) := shoup_bound_le s F

/-- Shoup's bound applied to the largest prime factor of `N`: the success probability
of a DLP attack restricted to the prime-order subgroup of order `lp(N)` is at most
`s²/(2·lp(N))`. -/
theorem shoup_theorem_9_7_at_largest_prime_factor
    (N : ℕ) (hN : 1 < N) (s : ℕ) :
    haveI : Fact (Nat.Prime (largestPrimeFactor N hN)) := largestPrimeFactor_fact N hN
    ∀ (F : Fin s → ZMod (largestPrimeFactor N hN) × ZMod (largestPrimeFactor N hN))
      (successSet : Finset (ZMod (largestPrimeFactor N hN)))
      (_ : successSet ⊆ collisionSet s F),
    (successSet.card : ℝ) / (Fintype.card (ZMod (largestPrimeFactor N hN))) ≤
      s ^ 2 / (2 * ↑(largestPrimeFactor N hN)) := by
  haveI := largestPrimeFactor_fact N hN
  intro F ss h
  exact shoup_theorem_9_7_prime s F ss h

end Theorem_9_7_Full

section Theorem_9_7_General

/-- Canonical ring hom `ZMod N → ZMod (largestPrimeFactor N)` induced by the divisibility
`lp(N) ∣ N`, used to reduce a generic DLP on `ZMod N` to the prime-order subgroup. -/
noncomputable def projToLargestPrime (N : ℕ) (hN : 1 < N) :
    ZMod N →+* ZMod (largestPrimeFactor N hN) :=
  ZMod.castHom (largestPrimeFactor_dvd N hN) (ZMod (largestPrimeFactor N hN))

/-- For a prime `q ∣ N`, the kernel of the cast `ZMod N → ZMod q` has cardinality `N / q`. -/
lemma zmod_castHom_kernel_card {N q : ℕ} [NeZero N] (hq : Fact (Nat.Prime q)) (hdvd : q ∣ N) :
    (Finset.univ.filter (fun a : ZMod N => ZMod.castHom hdvd (ZMod q) a = 0)).card = N / q := by
  classical
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  set f := ZMod.castHom hdvd (ZMod q)
  set k := (Finset.univ.filter (fun a : ZMod N => f a = 0)).card
  have hfiber_eq : ∀ b : ZMod q,
      (Finset.univ.filter (fun a : ZMod N => f a = b)).card = k := by
    intro b
    obtain ⟨a₀, ha₀⟩ := ZMod.castHom_surjective hdvd b
    apply Finset.card_equiv (Equiv.subRight a₀)
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply]
    exact ⟨fun h => by simp only [f, map_sub, h, ha₀, sub_self],
           fun h => by rw [show f (a - a₀) = f a - f a₀ from map_sub f a a₀] at h
                       rwa [ha₀, sub_eq_zero] at h⟩
  have hsum_N : ∑ b : ZMod q,
      (Finset.univ.filter (fun a : ZMod N => f a = b)).card = N := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := f)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [← this, Finset.card_univ, ZMod.card]
  have hsum_pk : ∑ b : ZMod q,
      (Finset.univ.filter (fun a : ZMod N => f a = b)).card = q * k := by
    simp only [hfiber_eq, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [hsum_pk] at hsum_N
  rw [← hsum_N, Nat.mul_div_cancel_left _ (Nat.Prime.pos hq.out)]

/-- Every fiber of the cast `ZMod N → ZMod q` has cardinality at most `N / q`
(equal cardinality `N / q` in fact). -/
lemma zmod_castHom_fiber_le {N q : ℕ} [NeZero N] (hq : Fact (Nat.Prime q)) (hdvd : q ∣ N)
    (b : ZMod q) :
    (Finset.univ.filter (fun a : ZMod N => ZMod.castHom hdvd (ZMod q) a = b)).card ≤ N / q := by
  classical
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨a₀, ha₀⟩ := ZMod.castHom_surjective hdvd b
  have : (Finset.univ.filter (fun a : ZMod N => ZMod.castHom hdvd (ZMod q) a = b)).card =
      (Finset.univ.filter (fun a : ZMod N => ZMod.castHom hdvd (ZMod q) a = 0)).card := by
    apply Finset.card_equiv (Equiv.subRight a₀)
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply]
    exact ⟨fun h => by simp only [map_sub, h, ha₀, sub_self],
           fun h => by rw [map_sub] at h; rwa [ha₀, sub_eq_zero] at h⟩
  rw [this, zmod_castHom_kernel_card hq hdvd]

/-- For any `S ⊆ ZMod N`, `|S| ≤ |image S| · (N / q)` using the uniform fiber bound. -/
lemma card_le_card_image_mul_div {N q : ℕ} [NeZero N] (hq : Fact (Nat.Prime q)) (hdvd : q ∣ N)
    (S : Finset (ZMod N)) :
    S.card ≤ (S.image (ZMod.castHom hdvd (ZMod q))).card * (N / q) := by
  classical
  rw [mul_comm]
  apply Finset.card_le_mul_card_image
  intro b _hb
  calc (S.filter (fun a => ZMod.castHom hdvd (ZMod q) a = b)).card
      ≤ (Finset.univ.filter (fun a : ZMod N => ZMod.castHom hdvd (ZMod q) a = b)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ ≤ N / q := zmod_castHom_fiber_le hq hdvd b

/-- Theorem 9.7 (Shoup) for general modulus `N`: reducing to the largest prime factor
gives a success-probability bound of `s²/(2 · lp(N))` for any generic DLP attack on `ZMod N`. -/
theorem shoup_theorem_9_7_general_N
    (N : ℕ) [NeZero N] (hN : 1 < N)
    (s : ℕ)
    (successSet : Finset (ZMod N))
    (F : Fin s → ZMod (largestPrimeFactor N hN) × ZMod (largestPrimeFactor N hN))
    (hp : Fact (Nat.Prime (largestPrimeFactor N hN)))
    (h_reduction : successSet.image (projToLargestPrime N hN) ⊆
      @collisionSet (largestPrimeFactor N hN) hp s F) :
    (successSet.card : ℝ) / (Fintype.card (ZMod N)) ≤
      s ^ 2 / (2 * ↑(largestPrimeFactor N hN)) := by
  classical
  let lp := largestPrimeFactor N hN
  have hdvd := largestPrimeFactor_dvd N hN
  have hlp_pos : (0 : ℝ) < lp := Nat.cast_pos.mpr (largestPrimeFactor_pos N hN)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)

  have h_card_bound := card_le_card_image_mul_div hp hdvd successSet

  have hproj_eq : (projToLargestPrime N hN : ZMod N → ZMod lp) =
      (ZMod.castHom hdvd (ZMod lp) : ZMod N → ZMod lp) := rfl

  have h_image_le : (successSet.image (projToLargestPrime N hN)).card ≤
      (@collisionSet lp hp s F).card :=
    Finset.card_le_card h_reduction

  rw [hproj_eq] at h_image_le

  have h_ratio : (successSet.card : ℝ) / N ≤ (@collisionSet lp hp s F).card / lp := by
    rw [div_le_div_iff₀ hN_pos hlp_pos]
    have h_step : successSet.card ≤ (@collisionSet lp hp s F).card * (N / lp) :=
      le_trans h_card_bound (Nat.mul_le_mul_right _ h_image_le)
    have h_div_mul : N / lp * lp = N := Nat.div_mul_cancel hdvd
    calc (successSet.card : ℝ) * lp
        ≤ ((@collisionSet lp hp s F).card * (N / lp) : ℕ) * lp := by
          exact_mod_cast Nat.mul_le_mul_right lp h_step
      _ = (@collisionSet lp hp s F).card * ((N / lp : ℕ) * lp) := by push_cast; ring
      _ = (@collisionSet lp hp s F).card * N := by rw_mod_cast [h_div_mul]

  rw [ZMod.card N]
  calc (successSet.card : ℝ) / N
      ≤ (@collisionSet lp hp s F).card / lp := h_ratio
    _ ≤ s ^ 2 / (2 * lp) := by
        have := @shoup_bound_le lp hp s F
        rw [ZMod.card] at this
        exact this

end Theorem_9_7_General

section Corollary_9_10

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Closed form for the sum of squares: `∑_{k<n} k² = n(n-1)(2n-1)/6`. -/
lemma sum_sq_range_real (n : ℕ) :
    (∑ k ∈ Finset.range n, ((↑k : ℝ) ^ 2)) =
    ↑n * (↑n - 1) * (2 * ↑n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Expected-value lower bound used in Corollary 9.10: `∑_{m<M} (1 - m²/(2p))`, which
bounds the expected number of group operations for a Las Vegas DLP algorithm. -/
noncomputable def lasVegasExpectedLB (p M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (1 - (↑m : ℝ) ^ 2 / (2 * ↑p))

/-- Closed form: `lasVegasExpectedLB p M = M - M(M-1)(2M-1)/(12 p)`. -/
lemma lasVegasExpectedLB_closed_form (p M : ℕ) (hp' : (0 : ℝ) < p) :
    lasVegasExpectedLB p M = ↑M - ↑M * (↑M - 1) * (2 * ↑M - 1) / (12 * ↑p) := by
  unfold lasVegasExpectedLB
  conv_lhs => arg 2; ext m; rw [show (1 : ℝ) - (↑m : ℝ) ^ 2 / (2 * ↑p) =
    1 - (↑m : ℝ) ^ 2 * (2 * ↑p)⁻¹ from by rw [div_eq_mul_inv]]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← Finset.sum_mul, sum_sq_range_real]; field_simp; ring

omit [Fact (Nat.Prime p)] in
/-- Using Shoup's bound `cdf s ≤ s²/(2p)` term-by-term gives the lower bound
`lasVegasExpectedLB p M ≤ ∑ (1 - cdf m)`. -/
theorem lasVegas_shoup_lb (M : ℕ) (cdf : ℕ → ℝ)
    (hcdf : ∀ s : ℕ, cdf s ≤ (↑s : ℝ) ^ 2 / (2 * ↑(p : ℕ))) :
    lasVegasExpectedLB p M ≤ ∑ m ∈ Finset.range M, (1 - cdf m) := by
  apply Finset.sum_le_sum; intro m _; exact sub_le_sub_left (hcdf m) 1

/-- When `M² ≤ 2p` and `M ≥ 1`, the expected-LB satisfies `lasVegasExpectedLB p M ≥ 2M/3`. -/
lemma lasVegasExpectedLB_ge (p M : ℕ) (hp' : (0 : ℝ) < p)
    (hM : (↑M : ℝ) ^ 2 ≤ 2 * ↑p) (hM1 : 1 ≤ M) :
    2 * (↑M : ℝ) / 3 ≤ lasVegasExpectedLB p M := by
  rw [lasVegasExpectedLB_closed_form p M hp']
  suffices h : ↑M * (↑M - 1) * (2 * ↑M - 1) / (12 * ↑p) ≤ (↑M : ℝ) / 3 by linarith
  by_contra hlt
  push Not at hlt
  have hM_real : (1 : ℝ) ≤ ↑M := by exact_mod_cast hM1
  have : (↑M : ℝ) * (12 * ↑p) < ↑M * (↑M - 1) * (2 * ↑M - 1) * 3 := by
    rwa [div_lt_div_iff₀ (by positivity : (0:ℝ) < 3) (by positivity : (0:ℝ) < 12 * ↑p)] at hlt
  nlinarith [sq_nonneg ((↑M : ℝ) - 1), sq_nonneg (↑M : ℝ),
    sq_nonneg ((↑M : ℝ) * ((↑M : ℝ) - 1))]

omit [Fact (Nat.Prime p)] in
/-- `⌊√(2p)⌋² ≤ 2p`, providing the hypothesis `M² ≤ 2p` for `M = ⌊√(2p)⌋`. -/
lemma floor_sqrt_2p_sq_le (p : ℕ) :
    (↑⌊√(2 * (↑p : ℝ))⌋₊ : ℝ) ^ 2 ≤ 2 * (↑p : ℝ) := by
  nlinarith [Nat.floor_le (Real.sqrt_nonneg (2 * (↑p : ℝ))),
    Real.sq_sqrt (show (0:ℝ) ≤ 2 * ↑p by positivity),
    sq_nonneg (√(2 * (↑p : ℝ)) - ↑⌊√(2 * (↑p : ℝ))⌋₊)]

/-- For `p` prime, `⌊√(2p)⌋ ≥ 1`. -/
lemma floor_sqrt_2p_ge_one : 1 ≤ ⌊√(2 * (↑p : ℝ))⌋₊ := by
  rw [Nat.one_le_iff_ne_zero]; intro h
  have h1 : √(2 * (↑p : ℝ)) < 1 := by
    calc √(2 * (↑p : ℝ)) < ↑⌊√(2 * (↑p : ℝ))⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = 1 := by rw [h]; simp
  have hp_pos : (1 : ℝ) ≤ ↑p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have h2 : 1 ≤ √(2 * (↑p : ℝ)) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

omit [Fact (Nat.Prime p)] in
/-- Rewrite `2√(2p)/3 = (2√2/3)·√p`. -/
lemma two_sqrt_two_p_eq (p : ℕ) :
    2 * √(2 * (↑p : ℝ)) / 3 = 2 * √2 / 3 * √(↑p : ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring

/-- Corollary 9.10 (Sutherland), explicit form: given Shoup's bound `cdf s ≤ s²/(2p)`
on the success probability, the expected number of operations of a Las Vegas DLP
algorithm is at least `(2√2/3) √p - 2/3`, giving the `(2√2/3 + o(1))√N` lower bound. -/
theorem corollary_9_10
    (cdf : ℕ → ℝ)
    (hcdf : ∀ s : ℕ, cdf s ≤ (↑s : ℝ) ^ 2 / (2 * ↑(p : ℕ))) :
    2 * √2 / 3 * √(↑p : ℝ) - 2 / 3 ≤
    ∑ m ∈ Finset.range ⌊√(2 * (↑p : ℝ))⌋₊, (1 - cdf m) := by
  have hp' : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos
  rw [← two_sqrt_two_p_eq]
  have h_floor_lb : 2 * √(2 * ↑p) / 3 - 2 / 3 ≤ 2 * ↑⌊√(2 * (↑p : ℝ))⌋₊ / 3 := by
    linarith [Nat.sub_one_lt_floor (√(2 * (↑p : ℝ)))]
  calc 2 * √(2 * ↑p) / 3 - 2 / 3
      ≤ 2 * ↑⌊√(2 * (↑p : ℝ))⌋₊ / 3 := h_floor_lb
    _ ≤ lasVegasExpectedLB p ⌊√(2 * (↑p : ℝ))⌋₊ :=
        lasVegasExpectedLB_ge p _ hp' (floor_sqrt_2p_sq_le p) floor_sqrt_2p_ge_one
    _ ≤ ∑ m ∈ Finset.range ⌊√(2 * (↑p : ℝ))⌋₊, (1 - cdf m) :=
        lasVegas_shoup_lb _ cdf hcdf

end Corollary_9_10

section Corollary_9_10

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Tail-sum identity: `∑_{m<M} |{x : m < f x}| ≤ ∑_x f x`, used to convert a
collection of tail counts into a sum of integer-valued data. -/
lemma tail_sum_le_nat {α : Type*} [Fintype α] (f : α → ℕ) (M : ℕ) :
    ∑ m ∈ Finset.range M, (Finset.univ.filter (fun x => m < f x)).card ≤
    ∑ x : α, f x := by
  classical
  have hcard : ∀ m, (Finset.univ.filter (fun x => m < f x)).card =
    ∑ x : α, (if m < f x then 1 else 0 : ℕ) := by
    intro m; rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hcard, Finset.sum_comm (s := Finset.range M) (t := Finset.univ)]
  apply Finset.sum_le_sum; intro x _
  have heq : ∑ m ∈ Finset.range M, (if m < f x then 1 else 0 : ℕ) =
    ((Finset.range M).filter (· < f x)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [heq]
  calc ((Finset.range M).filter (· < f x)).card
      ≤ (Finset.range (f x)).card := Finset.card_le_card (fun m hm => by
        simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2)
    _ = f x := Finset.card_range _

/-- Closed form for the falling-factorial sum: `∑_{k<n} k(k-1) = n(n-1)(n-2)/3`. -/
lemma sum_falling_range_real (n : ℕ) :
    (∑ k ∈ Finset.range n, ((↑k : ℝ) * (↑k - 1))) =
    ↑n * (↑n - 1) * (↑n - 2) / 3 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Corollary 9.10 (expected-value form): if the work function `w : ZMod p → ℕ`
satisfies Shoup's combinatorial constraint, then the expected number of operations
`(∑ w t)/p` is at least `2√(2p)/3`. -/
theorem corollary_9_10_expected_bound :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (w : ZMod p → ℕ),
    (∀ s : ℕ, (Finset.univ.filter (fun t : ZMod p => w t ≤ s)).card ≤ s * (s - 1) / 2) →
    2 * √(2 * ↑p) / 3 ≤ (∑ t : ZMod p, (w t : ℝ)) / ↑p := by
  intro p hp w hw
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos

  let N := ⌊√(2 * (↑p : ℝ))⌋₊
  let M := N + 1
  have hM_gt : √(2 * (↑p : ℝ)) < (↑M : ℝ) := by
    show √(2 * (↑p : ℝ)) < ↑(⌊√(2 * (↑p : ℝ))⌋₊ + 1)
    exact_mod_cast Nat.lt_floor_add_one (√(2 * (↑p : ℝ)))
  have hN_sq : (↑N : ℝ) ^ 2 ≤ 2 * ↑p := by
    show (↑⌊√(2 * (↑p : ℝ))⌋₊ : ℝ) ^ 2 ≤ 2 * ↑p
    nlinarith [Nat.floor_le (Real.sqrt_nonneg (2 * (↑p : ℝ))),
      Real.sq_sqrt (show (0:ℝ) ≤ 2 * ↑p by positivity),
      sq_nonneg (√(2 * (↑p : ℝ)) - ↑⌊√(2 * (↑p : ℝ))⌋₊)]

  suffices h_main : 2 * (↑M : ℝ) / 3 ≤ (∑ t : ZMod p, (w t : ℝ)) / ↑p by
    have : 2 * √(2 * (↑p : ℝ)) / 3 < 2 * (↑M : ℝ) / 3 := by
      apply div_lt_div_of_pos_right _ (by positivity : (0:ℝ) < 3); linarith
    linarith

  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 3) hp_pos]

  have h_tail : (∑ m ∈ Finset.range M,
    ((Finset.univ.filter (fun t : ZMod p => m < w t)).card : ℝ)) ≤
    ∑ t : ZMod p, (w t : ℝ) := by exact_mod_cast tail_sum_le_nat w M

  have h_term : ∀ m : ℕ, m ∈ Finset.range M →
    (↑p : ℝ) - ↑m * (↑m - 1) / 2 ≤
    ((Finset.univ.filter (fun t : ZMod p => m < w t)).card : ℝ) := by
    intro m _
    have hcomp : Finset.univ.filter (fun t : ZMod p => m < w t) =
      Finset.univ \ Finset.univ.filter (fun t : ZMod p => w t ≤ m) := by
      ext t; simp [not_le]
    have hcard_le : (Finset.univ.filter (fun t : ZMod p => w t ≤ m)).card ≤ p :=
      (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, ZMod.card])
    rw [hcomp, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, ZMod.card, Nat.cast_sub hcard_le]
    have : ((Finset.univ.filter (fun t : ZMod p => w t ≤ m)).card : ℝ) ≤
      ↑m * (↑m - 1) / 2 := by
      calc ((Finset.univ.filter (fun t : ZMod p => w t ≤ m)).card : ℝ)
          ≤ ↑(m * (m - 1) / 2) := by exact_mod_cast hw m
        _ ≤ ↑(m * (m - 1)) / 2 := Nat.cast_div_le
        _ ≤ ↑m * (↑m - 1) / 2 := by
            rcases m with _ | k
            · simp
            · simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ]; linarith
    linarith

  have h_sum_lb : ∑ m ∈ Finset.range M, (↑p - ↑m * (↑m - 1) / 2 : ℝ) ≤
    ∑ m ∈ Finset.range M, ((Finset.univ.filter (fun t : ZMod p => m < w t)).card : ℝ) :=
    Finset.sum_le_sum h_term

  have h_closed : ∑ m ∈ Finset.range M, (↑p - ↑m * (↑m - 1) / 2 : ℝ) =
    ↑M * ↑p - ↑M * (↑M - 1) * (↑M - 2) / 6 := by
    conv_lhs => arg 2; ext m; rw [show (↑p : ℝ) - ↑m * (↑m - 1) / 2 =
      ↑p - ↑m * (↑m - 1) * (1/2) from by ring]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show ∑ m ∈ Finset.range M, ((↑m : ℝ) * (↑m - 1) * (1/2)) =
      (∑ m ∈ Finset.range M, ((↑m : ℝ) * (↑m - 1))) * (1/2) from by
      rw [← Finset.sum_mul]]
    rw [sum_falling_range_real]; ring

  have h_arith : (2 : ℝ) * ↑M * ↑p ≤
    3 * (↑M * ↑p - ↑M * (↑M - 1) * (↑M - 2) / 6) := by
    have hM1 : (↑M : ℝ) - 1 = ↑N := by
      show (↑(N + 1) : ℝ) - 1 = ↑N; push_cast; ring
    have hM2 : (↑M : ℝ) - 2 = ↑N - 1 := by
      show (↑(N + 1) : ℝ) - 2 = ↑N - 1; push_cast; ring
    rw [hM1, hM2]
    nlinarith [sq_nonneg (↑N : ℝ)]

  calc (2 : ℝ) * ↑M * ↑p
      ≤ 3 * (↑M * ↑p - ↑M * (↑M - 1) * (↑M - 2) / 6) := h_arith
    _ = 3 * (∑ m ∈ Finset.range M, (↑p - ↑m * (↑m - 1) / 2 : ℝ)) := by rw [h_closed]
    _ ≤ 3 * (∑ m ∈ Finset.range M,
        ((Finset.univ.filter (fun t : ZMod p => m < w t)).card : ℝ)) := by linarith
    _ ≤ 3 * (∑ t : ZMod p, (w t : ℝ)) := by linarith
    _ = (∑ t : ZMod p, (w t : ℝ)) * 3 := by ring

end Corollary_9_10

section Corollary_9_11

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Shoup's combinatorial constraint on a Las Vegas DLP work function `w`: for every
`s`, at most `s(s-1)/2` instances `t` are solved by `w t ≤ s` queries. -/
def LasVegasShoupConstraint (w : ZMod p → ℕ) : Prop :=
  ∀ s : ℕ, (Finset.univ.filter (fun t : ZMod p => w t ≤ s)).card ≤ s * (s - 1) / 2

/-- At most `p/2` instances are solved within `⌊√p⌋` queries. -/
lemma las_vegas_count_solved_le (w : ZMod p → ℕ) (hw : LasVegasShoupConstraint w) :
    (Finset.univ.filter (fun t : ZMod p => w t ≤ Nat.sqrt p)).card ≤ p / 2 := by
  calc (Finset.univ.filter (fun t : ZMod p => w t ≤ Nat.sqrt p)).card
      ≤ Nat.sqrt p * (Nat.sqrt p - 1) / 2 := hw (Nat.sqrt p)
    _ ≤ Nat.sqrt p * Nat.sqrt p / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ ≤ p / 2 := by
        apply Nat.div_le_div_right
        have h := Nat.sqrt_le' p; rw [sq] at h; exact h

/-- Complementary count: at least `p/2` instances are unsolved within `⌊√p⌋` queries. -/
lemma las_vegas_count_unsolved_ge (w : ZMod p → ℕ) (hw : LasVegasShoupConstraint w) :
    p / 2 ≤ (Finset.univ.filter (fun t : ZMod p => Nat.sqrt p < w t)).card := by
  have huniv : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card p]
  have hcomp : Finset.univ.filter (fun t : ZMod p => Nat.sqrt p < w t) =
      Finset.univ \ Finset.univ.filter (fun t : ZMod p => w t ≤ Nat.sqrt p) := by
    ext t; simp
  rw [hcomp, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), huniv]
  have := las_vegas_count_solved_le w hw; omega

/-- Natural-number lower bound: `(⌊√p⌋ + 1) · (p/2) ≤ ∑ w t`. -/
lemma las_vegas_sum_lower_bound_nat (w : ZMod p → ℕ) (hw : LasVegasShoupConstraint w) :
    (Nat.sqrt p + 1) * (p / 2) ≤ ∑ t : ZMod p, w t := by
  let S := Finset.univ.filter (fun t : ZMod p => Nat.sqrt p < w t)
  calc (Nat.sqrt p + 1) * (p / 2)
      ≤ (Nat.sqrt p + 1) * S.card :=
        Nat.mul_le_mul_left _ (las_vegas_count_unsolved_ge w hw)
    _ = ∑ _t ∈ S, (Nat.sqrt p + 1) := by rw [Finset.sum_const]; ring
    _ ≤ ∑ t ∈ S, w t := by
        apply Finset.sum_le_sum; intro t ht
        simp only [S, Finset.mem_filter] at ht; omega
    _ ≤ ∑ t : ZMod p, w t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)

/-- `√n ≤ Nat.sqrt n + 1` as real numbers. -/
lemma real_sqrt_le_nat_sqrt_succ (n : ℕ) : √(↑n : ℝ) ≤ ↑(Nat.sqrt n) + 1 := by
  have h : (n : ℝ) ≤ (↑(Nat.sqrt n) + 1) ^ 2 := by exact_mod_cast (Nat.lt_succ_sqrt' n).le
  calc √(↑n : ℝ) ≤ √((↑(Nat.sqrt n) + 1) ^ 2) := Real.sqrt_le_sqrt h
    _ = |↑(Nat.sqrt n) + 1| := Real.sqrt_sq_eq_abs _
    _ = ↑(Nat.sqrt n) + 1 := abs_of_nonneg (by positivity)

/-- Quantitative form of Corollary 9.11: real-valued lower bound on the expected
work `(∑ w t)/p` in terms of `(⌊√p⌋ + 1)(p/2)/p`. -/
theorem corollary_9_11_quantitative (w : ZMod p → ℕ) (hw : LasVegasShoupConstraint w) :
    (↑(Nat.sqrt p + 1) : ℝ) * ↑(p / 2) / ↑p ≤ (∑ t : ZMod p, (w t : ℝ)) / ↑p := by
  have hp' : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos
  apply div_le_div_of_nonneg_right _ hp'.le
  have h := las_vegas_sum_lower_bound_nat w hw
  calc (↑(Nat.sqrt p + 1) : ℝ) * ↑(p / 2)
      = ↑((Nat.sqrt p + 1) * (p / 2)) := by push_cast; ring
    _ ≤ ↑(∑ t : ZMod p, w t) := by exact_mod_cast h
    _ = ∑ t : ZMod p, (w t : ℝ) := by push_cast; rfl

/-- Sharp constant form: the expected work `(∑ w t)/p ≥ √(2p)/2`. -/
theorem corollary_9_11_precise_constant :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (w : ZMod p → ℕ),
    LasVegasShoupConstraint w →
    √(2 * ↑p) / 2 ≤ (∑ t : ZMod p, (w t : ℝ)) / ↑p := by
  intro p hp w hw
  have h10 := corollary_9_10_expected_bound p w hw
  have hsq : 0 ≤ √(2 * ↑p) := Real.sqrt_nonneg _
  nlinarith

/-- Corollary 9.11 (Sutherland): every generic Las Vegas DLP algorithm in a cyclic
group of prime order `p` uses an expected `Ω(√p)` group operations, with the explicit
constant `√2/2 · √p`. -/
theorem corollary_9_11 (p : ℕ) [Fact (Nat.Prime p)] (w : ZMod p → ℕ)
    (hw : LasVegasShoupConstraint w) :
    √2 / 2 * √(↑p : ℝ) ≤ (∑ t : ZMod p, (w t : ℝ)) / ↑p := by
  have h := corollary_9_11_precise_constant p w hw
  have heq : √(2 * (↑p : ℝ)) / 2 = √2 / 2 * √(↑p : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring
  rwa [heq] at h

end Corollary_9_11

section Algorithm_9_6

variable {G : Type*} [AddCommGroup G]
variable {N : ℕ} [NeZero N]

/-- Configuration for Pollard-ρ with distinguished points (Algorithm 9.6): extends
`PollardRhoConfig` with a boolean predicate `B : G → Bool` identifying distinguished
group elements that get logged for collision detection. -/
structure PollardRhoDPConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N]
    extends PollardRhoConfig G N where
  B : G → Bool

variable [Module (ZMod N) G]

/-- A triple is distinguished when its `γ`-component is flagged by `B`. -/
def PollardRhoTriple.IsDistinguished
    (dpCfg : PollardRhoDPConfig G N) (t : PollardRhoTriple N G) : Prop :=
  dpCfg.B t.γ = true

/-- Two distinguished-point triples are a "DP collision" when both are distinguished
and have the same `γ` (only then does the algorithm record a useful collision). -/
def PollardRhoDPConfig.IsCollision
    (dpCfg : PollardRhoDPConfig G N)
    (t₁ t₂ : PollardRhoTriple N G) : Prop :=
  t₁.IsDistinguished dpCfg ∧ t₂.IsDistinguished dpCfg ∧ t₁.γ = t₂.γ

/-- The collision relation `(a₁ - a₂) • α = (b₂ - b₁) • β` for the distinguished-points
variant, derived from the ordinary Pollard-ρ collision relation. -/
theorem pollardRhoDP_collision_relation
    (dpCfg : PollardRhoDPConfig G N)
    (t₁ t₂ : PollardRhoTriple N G)
    (h₁ : t₁.IsValid dpCfg.toPollardRhoConfig) (h₂ : t₂.IsValid dpCfg.toPollardRhoConfig)
    (hcoll : dpCfg.IsCollision t₁ t₂) :
    (t₁.a - t₂.a) • dpCfg.α = (t₂.b - t₁.b) • dpCfg.β :=
  pollardRho_collision_relation dpCfg.toPollardRhoConfig t₁ t₂ h₁ h₂ hcoll.2.2

/-- DLP extraction for the distinguished-points variant of Pollard-ρ:
`β = ((b₂ - b₁)⁻¹ (a₁ - a₂)) • α` when `b₂ - b₁` is invertible in `ZMod N`. -/
theorem pollardRhoDP_dlog_extraction
    (dpCfg : PollardRhoDPConfig G N)
    (t₁ t₂ : PollardRhoTriple N G)
    (h₁ : t₁.IsValid dpCfg.toPollardRhoConfig) (h₂ : t₂.IsValid dpCfg.toPollardRhoConfig)
    (hcoll : dpCfg.IsCollision t₁ t₂)
    (hinv : IsUnit (t₂.b - t₁.b)) :
    dpCfg.β = ((t₂.b - t₁.b)⁻¹ * (t₁.a - t₂.a)) • dpCfg.α := by
  have key := pollardRhoDP_collision_relation dpCfg t₁ t₂ h₁ h₂ hcoll
  have step := congr_arg ((t₂.b - t₁.b)⁻¹ • ·) key
  simp only [← mul_smul] at step
  rw [ZMod.inv_mul_of_unit _ hinv, one_smul] at step
  exact step.symm

/-- Iterating the underlying Pollard-ρ step in the DP setting preserves the validity
invariant `γ = a • α + b • β`. -/
theorem pollardRhoDP_iter_preserves_invariant
    (dpCfg : PollardRhoDPConfig G N) (t₀ : PollardRhoTriple N G)
    (hpart : dpCfg.toPollardRhoConfig.PartitionValid)
    (h₀ : t₀.IsValid dpCfg.toPollardRhoConfig)
    (n : ℕ) :
    (pollardRhoIter dpCfg.toPollardRhoConfig t₀ n).IsValid dpCfg.toPollardRhoConfig :=
  pollardRhoIter_preserves_invariant dpCfg.toPollardRhoConfig t₀ hpart h₀ n

/-- End-to-end correctness of Pollard-ρ with distinguished points (Algorithm 9.6):
once a DP collision occurs at iteration indices `j, k` and `b_k - b_j` is invertible
in `ZMod N`, the algorithm correctly recovers `β` as a multiple of `α`, hence `log_α β`. -/
theorem pollardRhoDP_correctness
    (dpCfg : PollardRhoDPConfig G N) (t₀ : PollardRhoTriple N G)
    (hpart : dpCfg.toPollardRhoConfig.PartitionValid)
    (h₀ : t₀.IsValid dpCfg.toPollardRhoConfig)
    (j k : ℕ)
    (hcoll : dpCfg.IsCollision
      (pollardRhoIter dpCfg.toPollardRhoConfig t₀ j)
      (pollardRhoIter dpCfg.toPollardRhoConfig t₀ k))
    (hinv : IsUnit ((pollardRhoIter dpCfg.toPollardRhoConfig t₀ k).b -
      (pollardRhoIter dpCfg.toPollardRhoConfig t₀ j).b)) :
    dpCfg.β = (((pollardRhoIter dpCfg.toPollardRhoConfig t₀ k).b -
      (pollardRhoIter dpCfg.toPollardRhoConfig t₀ j).b)⁻¹ *
      ((pollardRhoIter dpCfg.toPollardRhoConfig t₀ j).a -
      (pollardRhoIter dpCfg.toPollardRhoConfig t₀ k).a)) • dpCfg.α :=
  pollardRhoDP_dlog_extraction dpCfg _ _
    (pollardRhoDP_iter_preserves_invariant dpCfg t₀ hpart h₀ j)
    (pollardRhoDP_iter_preserves_invariant dpCfg t₀ hpart h₀ k)
    hcoll hinv

omit [Module (ZMod N) G] in
/-- Degenerate sanity check: if the distinguishing predicate `B` always returns true,
then every triple is distinguished (so Algorithm 9.6 reduces to ordinary Pollard-ρ). -/
theorem pollardRhoDP_all_distinguished
    (dpCfg : PollardRhoDPConfig G N)
    (hB : ∀ g : G, dpCfg.B g = true)
    (t : PollardRhoTriple N G) : t.IsDistinguished dpCfg :=
  hB t.γ

end Algorithm_9_6
