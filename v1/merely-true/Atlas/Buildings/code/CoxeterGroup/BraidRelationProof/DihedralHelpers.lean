/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.BraidRelation

open Finset BigOperators Real

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The composition $\sigma_s \sigma_t$ is additive. -/
theorem sigma_comp_add (M : CoxeterMatrix B) (s t : B) (v₁ v₂ : B → ℝ) :
    sigma M s (sigma M t (v₁ + v₂)) =
    sigma M s (sigma M t v₁) + sigma M s (sigma M t v₂) := by
  rw [sigma_add M t, sigma_add M s]

/-- The composition $\sigma_s \sigma_t$ commutes with scalar multiplication. -/
theorem sigma_comp_smul (M : CoxeterMatrix B) (s t : B) (c : ℝ) (v : B → ℝ) :
    sigma M s (sigma M t (c • v)) = c • sigma M s (sigma M t v) := by
  rw [sigma_smul M t, sigma_smul M s]

/-- The $n$-fold iterate of $\sigma_s \sigma_t$ is additive. -/
theorem iterate_sigma_comp_add (M : CoxeterMatrix B) (s t : B) (n : ℕ) (v₁ v₂ : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[n] (v₁ + v₂) =
    (fun w => sigma M s (sigma M t w))^[n] v₁ +
    (fun w => sigma M s (sigma M t w))^[n] v₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_add]

/-- The $n$-fold iterate of $\sigma_s \sigma_t$ commutes with scalar
multiplication. -/
theorem iterate_sigma_comp_smul (M : CoxeterMatrix B) (s t : B) (n : ℕ) (c : ℝ) (v : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[n] (c • v) =
    c • (fun w => sigma M s (sigma M t w))^[n] v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_smul]


/-- The $n$-fold iterate of $\sigma_s \sigma_t$ fixes any vector orthogonal to
both $e_s$ and $e_t$. -/
theorem iterate_sigma_comp_fixes_orthogonal (M : CoxeterMatrix B) (s t : B) (n : ℕ)
    (w : B → ℝ) (hs : bilinForm M w (e s) = 0) (ht : bilinForm M w (e t) = 0) :
    (fun v => sigma M s (sigma M t v))^[n] w = w := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_fixes_orthogonal M s t w hs ht]


/-- Trigonometric step identity used to recognise the Chebyshev recurrence:
$2\cos(2\theta)\sin x - \sin(x - 2\theta) = \sin(x + 2\theta)$. -/
lemma sin_chebyshev_step (θ x : ℝ) :
    2 * cos (2 * θ) * sin x - sin (x - 2 * θ) = sin (x + 2 * θ) := by
  linarith [Real.sin_add x (2 * θ), Real.sin_sub x (2 * θ)]

/-- The Chebyshev-like sequence $A_n$ that tracks the $e_s$-coefficient of
$(\sigma_s \sigma_t)^n (e_s)$ in the geometric representation. -/
noncomputable def seqA (c α : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 4 * c ^ 2 - 1
  | (n + 2) => α * seqA c α (n + 1) - seqA c α n

/-- The sequence $B_n$ that tracks the $e_t$-coefficient of
$(\sigma_s \sigma_t)^n (e_s)$. -/
noncomputable def seqB (c α : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => -2 * c
  | (n + 2) => α * seqB c α (n + 1) - seqB c α n

/-- The sequence $C_n$ that tracks the $e_s$-coefficient of
$(\sigma_s \sigma_t)^n (e_t)$. -/
noncomputable def seqC (c α : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 2 * c
  | (n + 2) => α * seqC c α (n + 1) - seqC c α n

/-- The sequence $D_n$ that tracks the $e_t$-coefficient of
$(\sigma_s \sigma_t)^n (e_t)$. -/
noncomputable def seqD (c α : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | (n + 2) => α * seqD c α (n + 1) - seqD c α n

/-- The sequences $C_n$ and $B_n$ are negatives of each other:
$C_n = -B_n$ for all $n$. -/
lemma seqC_eq_neg_seqB (c α : ℝ) : ∀ n, seqC c α n = -seqB c α n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => simp [seqC, seqB]
  | 1 => simp [seqC, seqB]
  | n + 2 =>
    simp only [seqC, seqB]
    rw [ih (n + 1) (by omega), ih n (by omega)]; ring


/-- One-step recurrence for the pair $(A_n, B_n)$ giving the matrix product
that corresponds to applying one more copy of $\sigma_s \sigma_t$. -/
lemma seqAB_step (c : ℝ) : ∀ n,
    seqA c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqA c (4 * c ^ 2 - 2) n +
      2 * c * seqB c (4 * c ^ 2 - 2) n ∧
    seqB c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqA c (4 * c ^ 2 - 2) n -
      seqB c (4 * c ^ 2 - 2) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => exact ⟨by simp [seqA, seqB], by simp [seqA, seqB]⟩
  | 1 => exact ⟨by simp [seqA, seqB]; ring, by simp [seqA, seqB]; ring⟩
  | n + 2 =>
    obtain ⟨ihA1, ihB1⟩ := ih (n + 1) (by omega)
    obtain ⟨ihA0, ihB0⟩ := ih n (by omega)
    refine ⟨?_, ?_⟩
    · show seqA c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqA, seqB] at ihA1 ihB0 ⊢
      rw [ihB0] at ihA1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqA c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqA c (4 * c ^ 2 - 2) n)]
    · show seqB c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqA, seqB] at ihA1 ihB1 ihA0 ihB0 ⊢
      rw [ihB0] at ihA1 ⊢
      rw [ihA0] at ihB1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqB c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqB c (4 * c ^ 2 - 2) n)]


/-- One-step recurrence for the pair $(C_n, D_n)$, analogous to
$\mathtt{seqAB\_step}$. -/
lemma seqCD_step (c : ℝ) : ∀ n,
    seqC c (4 * c ^ 2 - 2) (n + 1) = (4 * c ^ 2 - 1) * seqC c (4 * c ^ 2 - 2) n +
      2 * c * seqD c (4 * c ^ 2 - 2) n ∧
    seqD c (4 * c ^ 2 - 2) (n + 1) = -2 * c * seqC c (4 * c ^ 2 - 2) n -
      seqD c (4 * c ^ 2 - 2) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => exact ⟨by simp [seqC, seqD], by simp [seqC, seqD]⟩
  | 1 => exact ⟨by simp [seqC, seqD]; ring, by simp [seqC, seqD]; ring⟩
  | n + 2 =>
    obtain ⟨ihC1, ihD1⟩ := ih (n + 1) (by omega)
    obtain ⟨ihC0, ihD0⟩ := ih n (by omega)
    refine ⟨?_, ?_⟩
    · show seqC c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqC, seqD] at ihC1 ihD0 ⊢
      rw [ihD0] at ihC1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqC c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqC c (4 * c ^ 2 - 2) n)]
    · show seqD c (4 * c ^ 2 - 2) (n + 3) = _
      simp only [seqC, seqD] at ihC1 ihD1 ihC0 ihD0 ⊢
      rw [ihD0] at ihC1 ⊢
      rw [ihC0] at ihD1 ⊢
      nlinarith [mul_self_nonneg c,
                 mul_self_nonneg (seqD c (4 * c ^ 2 - 2) (n + 1)),
                 mul_self_nonneg (seqD c (4 * c ^ 2 - 2) n)]


/-- Closed form for $A_n$ in terms of sines: $\sin\theta \cdot A_n =
\sin((2n+1)\theta)$ when $c = -\cos\theta$. -/
lemma seqA_sin (c α θ : ℝ) (hc : c = -cos θ) (hα : α = 4 * c ^ 2 - 2) :
    ∀ n, sin θ * seqA c α n = sin ((2 * (n : ℝ) + 1) * θ) := by
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => simp only [seqA, mul_one]; ring_nf
  | 1 =>
    simp only [seqA, hc, neg_sq]
    rw [show (2 * (↑(1 : ℕ) : ℝ) + 1) * θ = 3 * θ from by push_cast; ring, sin_three_mul θ]
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
    rw [this]; ring
  | n + 2 =>
    calc sin θ * seqA c α (n + 2)
        = α * (sin θ * seqA c α (n + 1)) - (sin θ * seqA c α n) := by
          show _ = α * _ - _; simp only [seqA]; ring
      _ = α * sin ((2 * ↑(n + 1) + 1) * θ) - sin ((2 * ↑n + 1) * θ) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
      _ = 2 * cos (2 * θ) * sin ((2 * ↑(n + 1) + 1) * θ) - sin ((2 * ↑n + 1) * θ) := by
          rw [hα_cos]
      _ = sin ((2 * ↑(n + 2) + 1) * θ) := by
          rw [show (2 * (↑n : ℝ) + 1) * θ = (2 * ↑(n + 1) + 1) * θ - 2 * θ from by
                push_cast; ring,
              show (2 * (↑(n + 2) : ℝ) + 1) * θ = (2 * ↑(n + 1) + 1) * θ + 2 * θ from by
                push_cast; ring]
          exact sin_chebyshev_step θ _

/-- Closed form for $B_n$ in terms of sines: $\sin\theta \cdot B_n =
\sin(2n\theta)$ when $c = -\cos\theta$. -/
lemma seqB_sin (c α θ : ℝ) (hc : c = -cos θ) (hα : α = 4 * c ^ 2 - 2) :
    ∀ n, sin θ * seqB c α n = sin (2 * (n : ℝ) * θ) := by
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => simp [seqB, Real.sin_zero]
  | 1 =>
    simp only [seqB, hc]
    rw [show 2 * (↑(1 : ℕ) : ℝ) * θ = 2 * θ from by push_cast; ring, Real.sin_two_mul]; ring
  | n + 2 =>
    calc sin θ * seqB c α (n + 2)
        = α * (sin θ * seqB c α (n + 1)) - (sin θ * seqB c α n) := by
          show _ = α * _ - _; simp only [seqB]; ring
      _ = α * sin (2 * ↑(n + 1) * θ) - sin (2 * ↑n * θ) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
      _ = 2 * cos (2 * θ) * sin (2 * ↑(n + 1) * θ) - sin (2 * ↑n * θ) := by rw [hα_cos]
      _ = sin (2 * ↑(n + 2) * θ) := by
          rw [show 2 * (↑n : ℝ) * θ = 2 * ↑(n + 1) * θ - 2 * θ from by push_cast; ring,
              show 2 * (↑(n + 2) : ℝ) * θ = 2 * ↑(n + 1) * θ + 2 * θ from by push_cast; ring]
          exact sin_chebyshev_step θ _

/-- Closed form for $D_n$ in terms of sines: $\sin\theta \cdot D_n =
-\sin((2n-1)\theta)$ when $c = -\cos\theta$. -/
lemma seqD_sin (c α θ : ℝ) (hc : c = -cos θ) (hα : α = 4 * c ^ 2 - 2) :
    ∀ n, sin θ * seqD c α n = -sin ((2 * (n : ℝ) - 1) * θ) := by
  have hα_cos : α = 2 * cos (2 * θ) := by rw [hα, hc, cos_two_mul]; ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 =>
    simp only [seqD, mul_one]
    rw [show (2 * (↑(0 : ℕ) : ℝ) - 1) * θ = -(1 * θ) from by push_cast; ring, Real.sin_neg]
    ring
  | 1 =>
    simp only [seqD]
    rw [show (2 * (↑(1 : ℕ) : ℝ) - 1) * θ = 1 * θ from by push_cast; ring]; ring
  | n + 2 =>
    calc sin θ * seqD c α (n + 2)
        = α * (sin θ * seqD c α (n + 1)) - (sin θ * seqD c α n) := by
          show _ = α * _ - _; simp only [seqD]; ring
      _ = α * (-sin ((2 * ↑(n + 1) - 1) * θ)) - (-sin ((2 * ↑n - 1) * θ)) := by
          rw [ih (n + 1) (by omega), ih n (by omega)]
      _ = -(2 * cos (2 * θ) * sin ((2 * ↑(n + 1) - 1) * θ) -
            sin ((2 * ↑n - 1) * θ)) := by rw [hα_cos]; ring
      _ = -sin ((2 * ↑(n + 2) - 1) * θ) := by
          rw [show (2 * (↑n : ℝ) - 1) * θ = (2 * ↑(n + 1) - 1) * θ - 2 * θ from by
                push_cast; ring,
              show (2 * (↑(n + 2) : ℝ) - 1) * θ = (2 * ↑(n + 1) - 1) * θ + 2 * θ from by
                push_cast; ring,
              sin_chebyshev_step]


/-- Functional form: the $n$-th iterate of $\sigma_s \sigma_t$ applied to
$e_s$ is the linear combination $A_n\, e_s + B_n\, e_t$. -/
lemma iter_e_s_formula_fn (M : CoxeterMatrix B) (s t : B) (n : ℕ) :
    (fun w => sigma M s (sigma M t w))^[n] (e s) =
      seqA (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s +
      seqB (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
  induction n with
  | zero => ext u; simp [seqA, seqB]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_add M t, sigma_smul M t, sigma_smul M t,
        sigma_add M s, sigma_smul M s, sigma_smul M s,
        sigma_comp_e_s, sigma_comp_e_t]
    ext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set c := formVal M s t
    obtain ⟨hA, hB⟩ := seqAB_step c n
    rw [hA, hB]; ring

/-- Pointwise form of $\mathtt{iter\_e\_s\_formula\_fn}$: evaluating at any
index $u$ gives $A_n\, e_s(u) + B_n\, e_t(u)$. -/
lemma iter_e_s_formula (M : CoxeterMatrix B) (s t : B) (n : ℕ) (u : B) :
    let c := formVal M s t
    let α := 4 * c ^ 2 - 2
    (fun w => sigma M s (sigma M t w))^[n] (e s) u =
      seqA c α n * e s u + seqB c α n * e t u := by
  have h := congr_fun (iter_e_s_formula_fn M s t n) u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- Functional form: the $n$-th iterate of $\sigma_s \sigma_t$ applied to
$e_t$ is the linear combination $C_n\, e_s + D_n\, e_t$. -/
lemma iter_e_t_formula_fn (M : CoxeterMatrix B) (s t : B) (n : ℕ) :
    (fun w => sigma M s (sigma M t w))^[n] (e t) =
      seqC (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e s +
      seqD (formVal M s t) (4 * formVal M s t ^ 2 - 2) n • e t := by
  induction n with
  | zero => ext u; simp [seqC, seqD]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_add M t, sigma_smul M t, sigma_smul M t,
        sigma_add M s, sigma_smul M s, sigma_smul M s,
        sigma_comp_e_s, sigma_comp_e_t]
    ext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set c := formVal M s t
    obtain ⟨hC, hD⟩ := seqCD_step c n
    rw [hC, hD]; ring

/-- Pointwise form of $\mathtt{iter\_e\_t\_formula\_fn}$: evaluating at any
index $u$ gives $C_n\, e_s(u) + D_n\, e_t(u)$. -/
lemma iter_e_t_formula (M : CoxeterMatrix B) (s t : B) (n : ℕ) (u : B) :
    let c := formVal M s t
    let α := 4 * c ^ 2 - 2
    (fun w => sigma M s (sigma M t w))^[n] (e t) u =
      seqC c α n * e s u + seqD c α n * e t u := by
  have h := congr_fun (iter_e_t_formula_fn M s t n) u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h


omit [DecidableEq B] [Fintype B] in
/-- If $s \ne t$ and the Coxeter order $m(s,t)$ is finite, then
$m(s,t) \ge 2$. -/
lemma m_ge_two (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    2 ≤ M.M s t := by
  have h1 : M.M s t ≠ 1 := M.off_diagonal s t hst
  omega

omit [DecidableEq B] [Fintype B] in
/-- For $s \ne t$ and finite $m(s,t)$, the angle $\theta = \pi/m(s,t)$ lies
strictly between $0$ and $\pi$, so $\sin\theta > 0$. -/
lemma sin_theta_pos (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    0 < sin (π / (M.M s t : ℝ)) := by
  have hm2 := m_ge_two M s t hst hm
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos (by positivity)
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (M.M s t : ℝ))]
    calc π = π * 1 := by ring
      _ < π * (M.M s t : ℝ) := by
          apply mul_lt_mul_of_pos_left _ Real.pi_pos
          exact_mod_cast show 1 < M.M s t by omega

omit [DecidableEq B] [Fintype B] in
/-- When $m(s,t)$ is finite, the matrix entry $B_{s,t}$ equals
$-\cos(\pi/m(s,t))$. -/
lemma formVal_eq (M : CoxeterMatrix B) (s t : B) (hm : M.M s t ≠ 0) :
    formVal M s t = -cos (π / (M.M s t : ℝ)) := by
  simp [formVal, hm]

omit [DecidableEq B] [Fintype B] in
/-- Endpoint value: $A_{m(s,t)} = 1$, encoding that the $e_s$-coefficient of
$(\sigma_s\sigma_t)^{m(s,t)}(e_s)$ returns to $1$. -/
lemma seqA_at_m (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    seqA (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 1 := by
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq M s t hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos M s t hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqA_sin c α θ hc hα m


  have hangle : (2 * (m : ℝ) + 1) * θ = θ + 2 * π := by
    simp only [θ]; field_simp; ring
  rw [hangle] at hkey
  rw [Real.sin_add_two_pi] at hkey

  exact mul_left_cancel₀ (ne_of_gt hsin_pos) (show sin θ * seqA c α m = sin θ * 1 by linarith)

omit [DecidableEq B] [Fintype B] in
/-- Endpoint value: $B_{m(s,t)} = 0$, encoding that the $e_t$-coefficient of
$(\sigma_s\sigma_t)^{m(s,t)}(e_s)$ vanishes. -/
lemma seqB_at_m (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    seqB (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 0 := by
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq M s t hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos M s t hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqB_sin c α θ hc hα m

  have hangle : 2 * (m : ℝ) * θ = 2 * π := by
    simp only [θ]; field_simp
  rw [hangle, Real.sin_two_pi] at hkey

  exact (mul_eq_zero.mp hkey).resolve_left (ne_of_gt hsin_pos)

omit [DecidableEq B] [Fintype B] in
/-- Endpoint value: $C_{m(s,t)} = 0$, following from $C_n = -B_n$. -/
lemma seqC_at_m (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    seqC (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 0 := by
  rw [seqC_eq_neg_seqB, seqB_at_m M s t hst hm, neg_zero]

omit [DecidableEq B] [Fintype B] in
/-- Endpoint value: $D_{m(s,t)} = 1$, encoding that the $e_t$-coefficient of
$(\sigma_s\sigma_t)^{m(s,t)}(e_t)$ returns to $1$. -/
lemma seqD_at_m (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    seqD (formVal M s t) (4 * formVal M s t ^ 2 - 2) (M.M s t) = 1 := by
  set c := formVal M s t
  set α := 4 * c ^ 2 - 2
  set m := M.M s t
  set θ := π / (m : ℝ)
  have hc : c = -cos θ := formVal_eq M s t hm
  have hα : α = 4 * c ^ 2 - 2 := rfl
  have hsin_pos : 0 < sin θ := sin_theta_pos M s t hst hm
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hkey := seqD_sin c α θ hc hα m


  have hangle : (2 * (m : ℝ) - 1) * θ = 2 * π - θ := by
    simp only [θ]; field_simp
  rw [hangle, Real.sin_two_pi_sub] at hkey

  have hkey' : sin θ * seqD c α m = sin θ := by linarith
  exact mul_left_cancel₀ (ne_of_gt hsin_pos)
    (show sin θ * seqD c α m = sin θ * 1 by linarith)

end CoxeterGroup
