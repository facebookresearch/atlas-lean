/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Order.KrullDimension

set_option maxHeartbeats 800000

open Order PrimeSpectrum

namespace FiniteMorphismDimension

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- For an integral extension `B → A`, the induced map on prime spectra is
strictly monotone, so chains in `Spec A` descend to chains in `Spec B`. -/
theorem PrimeSpectrum.comap_strictMono_of_isIntegral
    [Algebra.IsIntegral B A] :
    StrictMono (PrimeSpectrum.comap (algebraMap B A)) := by
  intro p q hpq
  have hpq' : p.asIdeal < q.asIdeal := hpq
  obtain ⟨hle, x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp hpq'
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxp⟩
    (Algebra.IsIntegral.isIntegral x)

/-- An integral extension `B → A` satisfies `dim A ≤ dim B`, via strict
monotonicity of `Spec` on chains. -/
theorem ringKrullDim_le_of_integral [Algebra.IsIntegral B A] :
    ringKrullDim A ≤ ringKrullDim B :=
  krullDim_le_of_strictMono _ PrimeSpectrum.comap_strictMono_of_isIntegral

/-- Going-up: an injective integral extension lifts any strict chain of primes
in `B` to a strict chain in `A` with prescribed comap images. -/
theorem exists_lift_chain [Algebra.IsIntegral B A]
    (hinj : Function.Injective (algebraMap B A))
    (n : ℕ) (f : Fin (n + 1) → PrimeSpectrum B)
    (hf : ∀ i : Fin n, f i.castSucc < f i.succ) :
    ∃ g : Fin (n + 1) → PrimeSpectrum A,
      (∀ i, PrimeSpectrum.comap (algebraMap B A) (g i) = f i) ∧
      (∀ i : Fin n, g i.castSucc < g i.succ) := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) :=
    RingHom.IsIntegral.comap_surjective (Algebra.isIntegral_def.mp inferInstance) hinj
  induction n with
  | zero =>
    obtain ⟨q, hq⟩ := hsurj (f 0)
    exact ⟨fun _ => q, fun i => by fin_cases i; exact hq, fun i => by fin_cases i⟩
  | succ n ih =>

    have hf' : ∀ i : Fin n, (f ∘ Fin.castSucc) i.castSucc < (f ∘ Fin.castSucc) i.succ :=
      fun i => hf i.castSucc
    obtain ⟨g', hg'_comap, hg'_strict⟩ := ih (f ∘ Fin.castSucc) hf'

    have hle : (g' (Fin.last n)).asIdeal.comap (algebraMap B A) ≤
        (f (Fin.last (n + 1))).asIdeal := by
      have h := congr_arg PrimeSpectrum.asIdeal (hg'_comap (Fin.last n))
      simp only [Function.comp, PrimeSpectrum.comap_asIdeal] at h
      rw [h]; exact le_of_lt (hf (Fin.last n))

    obtain ⟨Q, hQ_ge, hQ_prime, hQ_comap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral
        (f (Fin.last (n + 1))).asIdeal (g' (Fin.last n)).asIdeal hle
    let qLast : PrimeSpectrum A := ⟨Q, hQ_prime⟩

    refine ⟨Fin.snoc g' qLast, ?_, ?_⟩
    ·
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact PrimeSpectrum.ext hQ_comap
      · intro j; simp only [Fin.snoc_castSucc]; exact hg'_comap j
    ·
      intro i
      refine Fin.lastCases ?_ ?_ i
      ·
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
        refine lt_of_le_of_ne hQ_ge ?_
        intro heq


        have h1 : PrimeSpectrum.comap (algebraMap B A) qLast = f (Fin.last (n + 1)) :=
          PrimeSpectrum.ext hQ_comap
        have h2 := hg'_comap (Fin.last n)
        simp only [Function.comp] at h2
        have h3 : f (Fin.last (n + 1)) = f (Fin.castSucc (Fin.last n)) := by
          rw [← h1, ← h2, heq]
        exact absurd h3.symm (ne_of_lt (hf (Fin.last n)))
      ·
        intro j; simp only [Fin.snoc_castSucc, Fin.succ_castSucc]; exact hg'_strict j

/-- Combined with going-up: an injective integral extension also satisfies
`dim B ≤ dim A`, so an integral surjection preserves Krull dimension. -/
theorem ringKrullDim_ge_of_injective_integral
    [Algebra.IsIntegral B A]
    (hinj : Function.Injective (algebraMap B A)) :
    ringKrullDim B ≤ ringKrullDim A := by
  unfold ringKrullDim
  apply iSup_le
  intro chain_B
  obtain ⟨g, _, hg_strict⟩ := exists_lift_chain hinj chain_B.length chain_B.toFun chain_B.step
  exact le_iSup_of_le ⟨chain_B.length, g, hg_strict⟩ le_rfl

/-- Lem 10, Lec 5: a finite injective morphism preserves Krull dimension, i.e.
`dim X = dim Y` for a finite surjection `X → Y`. -/
theorem ringKrullDim_eq_of_injective_finite
    [Module.Finite B A]
    (hinj : Function.Injective (algebraMap B A)) :
    ringKrullDim A = ringKrullDim B := by
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact le_antisymm ringKrullDim_le_of_integral (ringKrullDim_ge_of_injective_integral hinj)

end FiniteMorphismDimension
