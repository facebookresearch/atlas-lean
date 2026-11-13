/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
namespace FourierBound

/-- Projection of `(x, y) ∈ F × F` onto the line of slope `θ`: `π_θ(x, y) = x + θ y`.
This is the standard projection used throughout finite-field projection theory. -/
def piSlope {F : Type*} [Ring F] (θ : F) : F × F → F := fun p => p.1 + θ * p.2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- For two distinct slopes `θ₁ ≠ θ₂`, the pair of projections
`p ↦ (π_{θ₁}(p), π_{θ₂}(p))` is injective on `F²`. This is the algebraic fact that
two non-parallel lines uniquely determine a point. -/
lemma piSlope_pair_injective {θ₁ θ₂ : F} (hne : θ₁ ≠ θ₂) :
    Function.Injective (fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)) := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [piSlope, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hy : (θ₁ - θ₂) * (y₁ - y₂) = 0 := by linear_combination h1 - h2
  have heqy : y₁ = y₂ := by
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h (sub_ne_zero.mpr hne)
    · exact sub_eq_zero.mp h
  exact Prod.ext (by linear_combination h1 - θ₁ * heqy) heqy

omit [DecidableEq F] in
/-- For distinct slopes, the pair-of-projections map `F × F → F × F` is a bijection;
follows from `piSlope_pair_injective` and equal cardinalities. -/
lemma piSlope_pair_bijective {θ₁ θ₂ : F} (hne : θ₁ ≠ θ₂) :
    Function.Bijective (fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)) :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨piSlope_pair_injective hne, rfl⟩

/-- Counts the number of points `p ∈ F²` whose two projections `π_{θ₁}(p)` and
`π_{θ₂}(p)` lie in given sets `A₁` and `A₂`. For distinct slopes, the bijectivity
of the joint projection gives `|{p : π_{θ₁}(p) ∈ A₁ ∧ π_{θ₂}(p) ∈ A₂}| = |A₁| · |A₂|`. -/
lemma joint_preimage_card {θ₁ θ₂ : F} (hne : θ₁ ≠ θ₂) (A₁ A₂ : Finset F) :
    (Finset.univ.filter (fun p : F × F =>
      piSlope θ₁ p ∈ A₁ ∧ piSlope θ₂ p ∈ A₂)).card = A₁.card * A₂.card := by
  set g := fun p : F × F => (piSlope θ₁ p, piSlope θ₂ p)
  have hinj : Function.Injective g := piSlope_pair_injective hne
  have hsurj : Function.Surjective g := (piSlope_pair_bijective hne).surjective
  conv_lhs =>
    rw [show (Finset.univ.filter (fun p => piSlope θ₁ p ∈ A₁ ∧ piSlope θ₂ p ∈ A₂)) =
      (A₁ ×ˢ A₂).preimage g (hinj.injOn) from by
        ext p; simp [Finset.mem_preimage, Finset.mem_product, g]]
  rw [Finset.card_preimage]
  · convert Finset.card_product A₁ A₂
    ext ⟨b₁, b₂⟩
    simp only [Finset.mem_filter, Finset.mem_product, Set.mem_range]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hsurj _⟩⟩

/-- Every fiber of the projection `π_θ : F² → F` has cardinality `|F| = q`:
the line `π_θ^{-1}(b)` contains exactly `|F|` points. -/
lemma piSlope_fiber_card (θ : F) (b : F) :
    (Finset.univ.filter (fun p : F × F => piSlope θ p = b)).card = Fintype.card F := by
  have hinj : Function.Injective (fun y : F => (b - θ * y, y)) := by
    intro a c h; exact (Prod.mk.inj h).2
  have heq : (Finset.univ.filter (fun p : F × F => piSlope θ p = b)) =
    (Finset.univ.image (fun y : F => (b - θ * y, y))) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, piSlope] at h
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      refine ⟨y, ?_, rfl⟩
      have : b - θ * y = x + θ * y - θ * y := by rw [h]
      rw [this]; ring
    · intro h
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at h
      obtain ⟨y', hx, hy'⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, piSlope]
      rw [← hx, ← hy']; ring
  rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- Numerical bookkeeping step in the Fourier proof of Theorem 2.3. Given the
variance bound `|X| · |D|² · (q - S)² ≤ S · |D| · q³` and `2S ≤ q`, deduce the
projection bound `|D| · |X| ≤ 4 S q`. The factor of 4 comes from `q ≤ 2(q - S)`. -/
lemma fourier_numerical (Xc Dc S q : ℕ)
    (hS_le : 2 * S ≤ q) (hq_pos : 0 < q) (hDc_pos : 0 < Dc)
    (hvar : Xc * Dc * Dc * (q - S) * (q - S) ≤ S * Dc * q * q * q) :
    Dc * Xc ≤ 4 * S * q := by
  have hqS : q ≤ 2 * (q - S) := by omega
  have hq2 : q * q ≤ 4 * (q - S) * (q - S) := by nlinarith [Nat.mul_le_mul hqS hqS]
  have h1 : Xc * Dc * (q - S) * (q - S) ≤ S * q * q * q :=
    Nat.le_of_mul_le_mul_left (by nlinarith) hDc_pos
  have h2 : Dc * Xc * (q * q) ≤ 4 * S * q * (q * q) :=
    calc Dc * Xc * (q * q)
      _ ≤ Dc * Xc * (4 * (q - S) * (q - S)) := Nat.mul_le_mul_left _ hq2
      _ = 4 * (Xc * Dc * (q - S) * (q - S)) := by ring
      _ ≤ 4 * (S * q * q * q) := Nat.mul_le_mul_left 4 h1
      _ = 4 * S * q * (q * q) := by ring
  exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hq_pos hq_pos)

end FourierBound


/-- The preimage `π_θ^{-1}(A) ⊂ F²` of a set `A ⊂ F` of "values" under the
direction-`θ` projection has cardinality `|F| · |A| = q · |A|`. Obtained by
disjointly unioning the fibers `π_θ^{-1}(b)` for `b ∈ A`. -/
lemma FourierBound.preimage_card_eq
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (θ : F) (A : Finset F) :
    (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x ∈ A)).card =
    Fintype.card F * A.card := by
  have hdisj : ∀ b₁ ∈ A, ∀ b₂ ∈ A, b₁ ≠ b₂ →
    Disjoint (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b₁))
             (Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b₂)) :=
    fun _ _ _ _ hne => Finset.disjoint_filter.mpr (fun _ _ h1 h2 => hne (h1 ▸ h2))
  have hsplit : Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x ∈ A) =
    A.biUnion (fun b => Finset.univ.filter (fun x : F × F => FourierBound.piSlope θ x = b)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact ⟨fun h => ⟨FourierBound.piSlope θ x, h, rfl⟩, fun ⟨b, hb, hxb⟩ => hxb ▸ hb⟩
  rw [hsplit, Finset.card_biUnion hdisj]
  simp only [FourierBound.piSlope_fiber_card, Finset.sum_const]; ring

open FourierBound in
/--
Variance / second moment bound underlying the Fourier proof of Theorem 2.3. Let
`f(x) = |{θ ∈ D : π_θ(x) ∈ π_θ(X)}|` and `M = ∑_{θ ∈ D} |π_θ(X)|`. Then
$$|X| \cdot (q|D| - M)^2 \;\le\; q^3 \, M,$$
a consequence of the first and second moments of `f` over `F²` via Cauchy-Schwarz
(equivalently, an `L²` orthogonality / Parseval-type computation).
-/
theorem FourierBound.variance_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (X : Finset (F × F)) (D : Finset F)
    (hX : X.Nonempty)
    (M : ℕ) (hM_def : M = ∑ θ ∈ D, (X.image (piSlope θ)).card)
    (hM_le_qD : M ≤ Fintype.card F * D.card) :
    X.card * (Fintype.card F * D.card - M) * (Fintype.card F * D.card - M) ≤
      Fintype.card F * Fintype.card F * Fintype.card F * M := by
  set q := Fintype.card F
  set f : F × F → ℕ := fun x => (D.filter (fun θ => piSlope θ x ∈ X.image (piSlope θ))).card
  set c : F → ℕ := fun θ => (X.image (piSlope θ)).card
  have hMc : M = ∑ θ ∈ D, c θ := hM_def
  have hfX : ∀ x ∈ X, f x = D.card := by
    intro x hx; simp only [f]; congr 1; ext θ; simp only [Finset.mem_filter]
    exact ⟨And.left, fun h => ⟨h, Finset.mem_image_of_mem _ hx⟩⟩
  have hSf : ∑ x : F × F, f x = q * M := by
    simp only [f, Finset.card_filter]; rw [Finset.sum_comm, hMc, Finset.mul_sum]
    congr 1; ext θ
    rw [show ∑ x : F × F, (if piSlope θ x ∈ X.image (piSlope θ) then (1:ℕ) else 0) =
      (Finset.univ.filter (fun x : F × F => piSlope θ x ∈ X.image (piSlope θ))).card from
        (Finset.card_filter _ _).symm]
    exact FourierBound.preimage_card_eq θ (X.image (piSlope θ))
  have hSf2 : ∑ x : F × F, f x ^ 2 ≤ q * M + M * M := by
    have step : ∑ x : F × F, (f x) ^ 2 =
      ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, (Finset.univ.filter (fun x : F × F =>
        piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₂ x ∈ X.image (piSlope θ₂))).card := by
      simp_rw [f, Finset.card_filter, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]; congr 1; ext θ₁; rw [Finset.sum_comm]; congr 1; ext θ₂
      have h : ∀ x : F × F, (if piSlope θ₁ x ∈ X.image (piSlope θ₁) then (1:ℕ) else 0) *
        (if piSlope θ₂ x ∈ X.image (piSlope θ₂) then 1 else 0) =
        if (piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₂ x ∈ X.image (piSlope θ₂)) then 1 else 0 := by
        intro x; split_ifs <;> simp_all
      simp_rw [h]
    rw [step]
    calc ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, _
      _ ≤ ∑ θ₁ ∈ D, ∑ θ₂ ∈ D, (if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) := by
          apply Finset.sum_le_sum; intro θ₁ _; apply Finset.sum_le_sum; intro θ₂ _
          split_ifs with heq
          · subst heq
            have hsimp : (Finset.univ.filter (fun x : F × F =>
              piSlope θ₁ x ∈ X.image (piSlope θ₁) ∧ piSlope θ₁ x ∈ X.image (piSlope θ₁))) =
              Finset.univ.filter (fun x : F × F => piSlope θ₁ x ∈ X.image (piSlope θ₁)) := by
              ext x; simp
            rw [hsimp, FourierBound.preimage_card_eq]
          · exact le_of_eq (joint_preimage_card heq _ _)
      _ ≤ q * (∑ θ ∈ D, c θ) + (∑ θ ∈ D, c θ) * (∑ θ ∈ D, c θ) := by
          suffices h : ∀ θ₁ ∈ D, (∑ θ₂ ∈ D, if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) ≤
            q * c θ₁ + c θ₁ * (∑ θ ∈ D, c θ) by
            calc _ ≤ ∑ θ₁ ∈ D, (q * c θ₁ + c θ₁ * (∑ θ ∈ D, c θ)) := Finset.sum_le_sum h
              _ = q * (∑ θ ∈ D, c θ) + (∑ θ ∈ D, c θ) * (∑ θ ∈ D, c θ) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          intro θ₁ hθ₁
          rw [← Finset.add_sum_erase D _ hθ₁]; simp only [if_true]
          apply Nat.add_le_add_left
          have h2 : ∀ θ₂ ∈ D.erase θ₁,
            (if θ₁ = θ₂ then q * c θ₁ else c θ₁ * c θ₂) = c θ₁ * c θ₂ :=
            fun θ₂ hθ₂ => if_neg (Finset.ne_of_mem_erase hθ₂).symm
          rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
          exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
      _ = q * M + M * M := by rw [← hMc]

  suffices h : (X.card : ℤ) * ((q : ℤ) * D.card - M) * ((q : ℤ) * D.card - M) ≤
    (q : ℤ) * q * q * M by exact_mod_cast h
  have step1 : (X.card : ℤ) * ((q : ℤ) * D.card - M) ^ 2 ≤
    ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 := by
    have heq : ∀ x ∈ X, ((q : ℤ) * (f x : ℤ) - M) ^ 2 = ((q : ℤ) * D.card - M) ^ 2 := by
      intro x hx; rw [show (f x : ℤ) = (D.card : ℤ) from by exact_mod_cast hfX x hx]
    calc (X.card : ℤ) * ((q : ℤ) * D.card - M) ^ 2
      _ = ∑ x ∈ X, ((q : ℤ) * D.card - M) ^ 2 := by simp [Finset.sum_const]
      _ = ∑ x ∈ X, ((q : ℤ) * (f x : ℤ) - M) ^ 2 := (Finset.sum_congr rfl heq).symm
      _ ≤ ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
  have step2 : ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 ≤ (q : ℤ) * q * q * M := by
    have expand : ∑ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 =
      (q : ℤ)^2 * (∑ x : F × F, (f x : ℤ)^2) - 2 * q * M * (∑ x : F × F, (f x : ℤ)) +
      (M : ℤ)^2 * (Fintype.card (F × F)) := by
      have h : ∀ x : F × F, ((q : ℤ) * (f x : ℤ) - M) ^ 2 =
        (q : ℤ)^2 * (f x : ℤ)^2 - 2 * q * M * (f x : ℤ) + M^2 := by intro x; ring
      simp_rw [h]; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ]; ring
    rw [expand, show (∑ x : F × F, (f x : ℤ)) = (q : ℤ) * M from by exact_mod_cast hSf,
        show (Fintype.card (F × F) : ℤ) = (q : ℤ) * q from by
          exact_mod_cast Fintype.card_prod F F]
    linarith [mul_le_mul_of_nonneg_left
      (show (∑ x : F × F, (f x : ℤ) ^ 2) ≤ (q : ℤ) * M + M * M from by
        have : (∑ x : F × F, (f x : ℤ) ^ 2) = ↑(∑ x : F × F, f x ^ 2) := by push_cast; rfl
        rw [this]; exact_mod_cast hSf2)
      (sq_nonneg (q : ℤ))]
  linarith [step1, step2, sq_abs ((q : ℤ) * ↑D.card - ↑M)]

namespace FourierBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/--
Theorem 2.3 (Fourier / orthogonality projection bound over `𝔽_q`). If `X ⊂ F²`,
`D ⊂ F`, and `S = max_{θ ∈ D} |π_θ(X)|` satisfies `2S ≤ q = |F|`, then
$$|D| \;\lesssim\; \frac{S q}{|X|},$$
explicitly `|D| · |X| ≤ 4 S q`. Proved by combining the variance bound
`|X|(q|D| - M)² ≤ q³ M` (with `M = ∑_{θ ∈ D}|π_θ(X)| ≤ S|D|`) with the numerical
inequality `q ≤ 2(q - S)`.
-/
theorem fourier_bound_finite_field
    (X : Finset (F × F)) (D : Finset F) (S : ℕ)
    (hS : ∀ θ ∈ D, (X.image (piSlope θ)).card ≤ S)
    (hS_le : 2 * S ≤ Fintype.card F)
    (hX : X.Nonempty) (hD : D.Nonempty) :
    D.card * X.card ≤ 4 * S * Fintype.card F := by
  set q := Fintype.card F with hq_def
  have hq_pos : 0 < q := Fintype.card_pos
  have hDc_pos : 0 < D.card := hD.card_pos
  set M := ∑ θ ∈ D, (X.image (piSlope θ)).card
  have hM_le : M ≤ S * D.card := by
    calc M = ∑ θ ∈ D, (X.image (piSlope θ)).card := rfl
      _ ≤ ∑ _ ∈ D, S := Finset.sum_le_sum hS
      _ = S * D.card := by simp [Finset.sum_const, mul_comm]
  have hSq : S ≤ q := by omega
  have hM_le_qD : M ≤ q * D.card := by
    calc M ≤ S * D.card := hM_le
      _ ≤ q * D.card := Nat.mul_le_mul_right _ hSq
  apply fourier_numerical X.card D.card S q hS_le hq_pos hDc_pos


  have hqD_ge : D.card * (q - S) ≤ q * D.card - M := by
    have h3 : D.card * (q - S) = q * D.card - S * D.card := by
      rw [show q * D.card - S * D.card = (q - S) * D.card from
        (Nat.sub_mul q S D.card).symm]; ring
    omega
  have hvar := variance_bound X D hX M rfl hM_le_qD
  calc X.card * D.card * D.card * (q - S) * (q - S)
    _ = X.card * (D.card * (q - S)) * (D.card * (q - S)) := by ring
    _ ≤ X.card * (q * D.card - M) * (q * D.card - M) := by
        nlinarith [Nat.mul_le_mul hqD_ge hqD_ge,
                   Nat.mul_le_mul_left X.card (Nat.mul_le_mul hqD_ge hqD_ge)]
    _ ≤ q * q * q * M := hvar
    _ ≤ q * q * q * (S * D.card) := Nat.mul_le_mul_left _ hM_le
    _ = S * D.card * q * q * q := by ring

end FourierBound
