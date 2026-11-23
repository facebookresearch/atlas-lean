/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec5DimensionResults

set_option maxHeartbeats 400000

noncomputable section

open Ideal

/-- Theorem 5.1 (Lec 5): the Krull dimension of affine `n`-space over a field equals `n`,
i.e. `dim k[X₁,…,Xₙ] = n`. -/
theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- Krull dimension is invariant under ring isomorphism. -/
theorem dim_eq_of_ringEquiv {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) : ringKrullDim R = ringKrullDim S :=
  ringKrullDim_eq_of_ringEquiv e

/-- The vanishing locus `V(p)` of a prime ideal `p` equals the upward closure
`{q ∈ Spec R : p ⊆ q}` in the specialization order. -/
lemma PrimeSpectrum.zeroLocus_prime_eq_Ici {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    PrimeSpectrum.zeroLocus (p : Set R) =
      Set.Ici (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  ext q
  simp [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
  rfl

/-- For a prime ideal `p ⊂ R`, `dim (R/p)` equals the coheight of `p` in `Spec R`,
since `Spec(R/p)` is order-isomorphic to `V(p) = Ici p`. -/
theorem ringKrullDim_quotient_prime_eq_coheight {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) =
      ↑(Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R)) := by
  rw [Order.coheight_eq_krullDim_Ici, ← PrimeSpectrum.zeroLocus_prime_eq_Ici]
  exact Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p)

/-- Height/coheight inequality: for any prime `p`,
`height(p) + dim(R/p) ≤ dim(R)`. -/
theorem height_add_ringKrullDim_quotient_le {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] [Nontrivial R] :
    ↑p.height + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  rw [Ideal.height_eq_primeHeight, ringKrullDim_quotient_prime_eq_coheight]
  change ↑(Ideal.primeHeight p) + ↑(Order.coheight P) ≤ ringKrullDim R
  rw [show (Ideal.primeHeight p : WithBot ℕ∞) = ↑(Order.height P) from rfl]
  rw [← WithBot.coe_add]
  unfold ringKrullDim
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum R)]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) P)
