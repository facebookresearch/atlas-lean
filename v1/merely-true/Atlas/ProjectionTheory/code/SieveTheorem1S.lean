/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SieveTheory

open Finset

/-- **Sieve Theorem 1S.** If $X \subseteq [N]$ and $D$ is a set of primes such that
$|\pi_p(X)| \le S$ for every $p \in D$ (where $\pi_p$ is reduction modulo $p$), then
either $|X| \le 2S$ or $|D| \lessapprox S \log N$. -/
theorem sieve_theorem_1S (N S : ℕ) (X D : Finset ℕ)
    (hX : X ⊆ Finset.range N)
    (hD_prime : ∀ p ∈ D, Nat.Prime p)
    (hS : ∀ p ∈ D, (X.image (· % p)).card ≤ S) :
    X.card ≤ 2 * S ∨ D.card ≤ 2 * S * (Nat.log 2 N) := by
  by_contra h_neg
  push Not at h_neg
  obtain ⟨hXlarge, hDlarge⟩ := h_neg


  have h_lower : X.card ^ 2 * D.card ≤
      S * ∑ p ∈ D, ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card := by
    calc X.card ^ 2 * D.card
        = ∑ _p ∈ D, X.card ^ 2 := by simp [sum_const, mul_comm]
      _ ≤ ∑ p ∈ D, (S * ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card) := by
          apply sum_le_sum; intro p hp

          have hfib : X.card = ∑ y ∈ X.image (· % p), (X.filter (fun x => x % p = y)).card :=
            card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem _ hx)

          have hcoinc : ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card =
              ∑ y ∈ X.image (· % p), (X.filter (fun x => x % p = y)).card ^ 2 := by
            rw [show (X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p) =
              (X.image (· % p)).biUnion (fun y =>
                (X.filter (fun x => x % p = y)) ×ˢ (X.filter (fun x => x % p = y))) from by
                ext ⟨a, b⟩; simp only [mem_filter, mem_product, mem_biUnion, mem_image]
                constructor
                · rintro ⟨⟨ha, hb⟩, hab⟩
                  exact ⟨a % p, ⟨a, ha, rfl⟩, ⟨ha, rfl⟩, ⟨hb, hab.symm⟩⟩
                · rintro ⟨y, _, ⟨ha, hay⟩, hb, hby⟩
                  exact ⟨⟨ha, hb⟩, hay ▸ hby.symm⟩]
            rw [card_biUnion]
            · congr 1; ext y; rw [card_product, sq]
            · intro y _ z _ hyz; apply Finset.disjoint_product.mpr; left
              exact disjoint_filter.mpr (fun x _ hxy hxz => hyz (hxy ▸ hxz))

          have hCS := @sq_sum_le_card_mul_sum_sq _ ℕ _ _ _ _ (X.image (· % p))
            (fun y => (X.filter (fun x => x % p = y)).card)
          rw [← hfib] at hCS; rw [hcoinc]
          exact le_trans hCS (Nat.mul_le_mul_right _ (hS p hp))
      _ = S * ∑ p ∈ D, ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card := by
          rw [Finset.mul_sum]


  have h_upper : ∑ p ∈ D, ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card ≤
      X.card * D.card + X.card * X.card * Nat.log 2 N := by

    rw [show ∑ p ∈ D, ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card =
        ∑ xy ∈ X ×ˢ X, (D.filter (fun p => xy.1 % p = xy.2 % p)).card from by
      simp_rw [card_filter]; rw [sum_comm]]

    rw [← sum_filter_add_sum_filter_not (X ×ˢ X) (fun xy => xy.1 = xy.2)]
    apply add_le_add
    ·
      calc ∑ xy ∈ (X ×ˢ X).filter (fun xy => xy.1 = xy.2),
            (D.filter (fun p => xy.1 % p = xy.2 % p)).card
          ≤ ∑ _xy ∈ (X ×ˢ X).filter (fun xy => xy.1 = xy.2), D.card :=
            sum_le_sum (fun xy _ => card_filter_le D _)
        _ = ((X ×ˢ X).filter (fun xy => xy.1 = xy.2)).card * D.card := by
            simp [sum_const]
        _ = X.card * D.card := by
            congr 1
            rw [show ((X ×ˢ X).filter (fun xy => xy.1 = xy.2)) =
              X.map ⟨fun x => (x, x), fun a b h => by simpa using h⟩ from by
              ext ⟨a, b⟩
              simp only [mem_filter, mem_product, mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
              constructor
              · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
              · rintro ⟨c, hc, hca, hcb⟩; exact ⟨⟨hca ▸ hc, hcb ▸ hca ▸ hc⟩, hca ▸ hcb⟩]
            exact card_map _
    ·

      calc ∑ xy ∈ (X ×ˢ X).filter (fun xy => ¬xy.1 = xy.2),
            (D.filter (fun p => xy.1 % p = xy.2 % p)).card
          ≤ ∑ _xy ∈ (X ×ˢ X).filter (fun xy => ¬xy.1 = xy.2), Nat.log 2 N := by
            apply sum_le_sum; intro ⟨x₁, x₂⟩ hxy
            simp only [mem_filter, mem_product] at hxy
            have hx₁N := mem_range.mp (hX hxy.1.1)
            have hx₂N := mem_range.mp (hX hxy.1.2)

            rcases Nat.lt_or_gt_of_ne hxy.2 with hlt | hgt
            · have hdp : 0 < x₂ - x₁ := Nat.sub_pos_of_lt hlt
              calc _ ≤ (x₂ - x₁).primeFactors.card := by
                    apply card_le_card; intro p hp; rw [mem_filter] at hp
                    rw [Nat.mem_primeFactors]
                    exact ⟨hD_prime p hp.1, (Nat.modEq_iff_dvd' hlt.le).mp hp.2, by omega⟩
                _ ≤ Nat.log 2 (x₂ - x₁) := by
                    apply Nat.le_log_of_pow_le (by norm_num)
                    exact le_trans (pow_card_le_prod _ _ _
                      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
                      (Nat.le_of_dvd hdp (Nat.prod_primeFactors_dvd _))
                _ ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
            · have hdp : 0 < x₁ - x₂ := Nat.sub_pos_of_lt hgt
              calc _ ≤ (x₁ - x₂).primeFactors.card := by
                    apply card_le_card; intro p hp; rw [mem_filter] at hp
                    rw [Nat.mem_primeFactors]
                    exact ⟨hD_prime p hp.1, (Nat.modEq_iff_dvd' hgt.le).mp hp.2.symm, by omega⟩
                _ ≤ Nat.log 2 (x₁ - x₂) := by
                    apply Nat.le_log_of_pow_le (by norm_num)
                    exact le_trans (pow_card_le_prod _ _ _
                      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
                      (Nat.le_of_dvd hdp (Nat.prod_primeFactors_dvd _))
                _ ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
        _ = ((X ×ˢ X).filter (fun xy => ¬xy.1 = xy.2)).card * Nat.log 2 N := by
            simp [sum_const]
        _ ≤ (X.card * X.card) * Nat.log 2 N := by
            apply Nat.mul_le_mul_right
            exact le_trans (card_filter_le _ _) (le_of_eq (card_product X X))

  have h_key : X.card ^ 2 * D.card ≤ S * X.card * D.card + S * X.card ^ 2 * Nat.log 2 N := by
    calc X.card ^ 2 * D.card
        ≤ S * ∑ p ∈ D, ((X ×ˢ X).filter (fun xy => xy.1 % p = xy.2 % p)).card := h_lower
      _ ≤ S * (X.card * D.card + X.card * X.card * Nat.log 2 N) :=
          Nat.mul_le_mul_left _ h_upper
      _ = S * X.card * D.card + S * X.card ^ 2 * Nat.log 2 N := by ring

  have hXpos : 0 < X.card := by omega
  have h1 : X.card * D.card ≤ S * D.card + S * X.card * Nat.log 2 N := by
    have hle : X.card * (X.card * D.card) ≤ X.card * (S * D.card + S * X.card * Nat.log 2 N) := by
      nlinarith
    exact Nat.le_of_mul_le_mul_left hle hXpos
  have hXgeS : S ≤ X.card := by omega
  have h2 : (X.card - S) * D.card ≤ S * X.card * Nat.log 2 N := by
    nlinarith [Nat.sub_add_cancel hXgeS]
  have h3 : X.card < 2 * (X.card - S) := by omega
  have h4 : S * X.card * Nat.log 2 N < 2 * S * Nat.log 2 N * (X.card - S) := by nlinarith
  have h5 : 2 * S * Nat.log 2 N * (X.card - S) ≤ D.card * (X.card - S) := by nlinarith
  nlinarith

end SieveTheory
