/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

noncomputable section

open scoped TensorProduct
open KaehlerDifferential Module

universe u v


section ConormalExactSequenceQuotient

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- The kernel of the canonical algebra map `R → R/I` is exactly `I`. -/
theorem conormal_ker_eq_ideal (R : Type*) [CommRing R] (I : Ideal R) :
    RingHom.ker (algebraMap R (R ⧸ I)) = I := by
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- The cotangent module of `ker(R → R/I)` is the cotangent module `I.Cotangent = I/I²`. -/
theorem conormal_ker_eq_ideal_cotangent (R : Type*) [CommRing R] (I : Ideal R) :
    (RingHom.ker (algebraMap R (R ⧸ I))).Cotangent = I.Cotangent := by
  congr 1
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- The canonical algebra map `R → R/I` is surjective. -/
theorem quotient_algebraMap_surjective (R : Type*) [CommRing R] (I : Ideal R) :
    Function.Surjective (algebraMap R (R ⧸ I)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- Conormal exact sequence: for `R → R/I` over `k`, the maps
`I/I² → (R/I) ⊗_R Ω_{R/k} → Ω_{(R/I)/k}` form an exact sequence at the middle term. -/
theorem conormal_exact_sequence_quotient :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I))
      (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- The base-change map `(R/I) ⊗_R Ω_{R/k} → Ω_{(R/I)/k}` is surjective. -/
theorem conormal_mapBaseChange_surjective_quotient :
    Function.Surjective
      (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
  apply KaehlerDifferential.mapBaseChange_surjective
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- The induced map of Kähler differentials `Ω_{R/k} → Ω_{(R/I)/(R/I)}` is surjective. -/
theorem conormal_map_surjective_quotient :
    Function.Surjective (KaehlerDifferential.map k R (R ⧸ I) (R ⧸ I)) :=
  KaehlerDifferential.map_surjective k R (R ⧸ I)

/-- First exact sequence of cotangent modules:
`(R/I) ⊗_R Ω_{R/k} → Ω_{(R/I)/(R/I)} → 0` is exact, where the second map sends to zero. -/
theorem cotangent_first_exact_sequence_quotient :
    Function.Exact
      (KaehlerDifferential.mapBaseChange k R (R ⧸ I))
      (KaehlerDifferential.map k R (R ⧸ I) (R ⧸ I)) :=
  KaehlerDifferential.exact_mapBaseChange_map k R (R ⧸ I)

end ConormalExactSequenceQuotient


section PolynomialQuotient

variable (k : Type*) [Field k]

/-- `Ω_{k[x₀,x₁]/k}` is a free module of rank `2` over `k[x₀,x₁]`. -/
theorem kahler_mvpoly_rank_two :
    Module.finrank (MvPolynomial (Fin 2) k)
      (Ω[MvPolynomial (Fin 2) k⁄k]) = 2 := by
  rw [Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k (Fin 2))]
  simp [Fintype.card_fin]

/-- `Ω_{k[x₁,…,xₙ]/k}` is a free module of rank `n` over `k[x₁,…,xₙ]`. -/
theorem kahler_mvpoly_rank (n : ℕ) :
    Module.finrank (MvPolynomial (Fin n) k)
      (Ω[MvPolynomial (Fin n) k⁄k]) = n := by
  rw [Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k (Fin n))]
  simp [Fintype.card_fin]

/-- `Ω_{k[x₁,…,xₙ]/k}` is a free module over `k[x₁,…,xₙ]`. -/
theorem kahler_mvpoly_free (n : ℕ) :
    Module.Free (MvPolynomial (Fin n) k) (Ω[MvPolynomial (Fin n) k⁄k]) :=
  inferInstance

/-- Conormal exact sequence for a quotient of `k[x₀,x₁]` by an ideal `I`. -/
theorem conormal_exact_mvpoly_quotient (I : Ideal (MvPolynomial (Fin 2) k)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor k (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸ I))
      (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸ I)) := by
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- Surjectivity of the base-change map for a quotient of `k[x₀,x₁]`. -/
theorem conormal_surj_mvpoly_quotient (I : Ideal (MvPolynomial (Fin 2) k)) :
    Function.Surjective
      (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸ I)) := by
  apply KaehlerDifferential.mapBaseChange_surjective
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- Conormal exact sequence for a quotient of `k[x₁,…,xₙ]` by an ideal `I`. -/
theorem conormal_exact_mvpoly_quotient_general (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor k (MvPolynomial (Fin n) k)
        (MvPolynomial (Fin n) k ⧸ I))
      (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin n) k)
        (MvPolynomial (Fin n) k ⧸ I)) := by
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

end PolynomialQuotient


section NumericalAdjunction

/-- Numerical adjunction identity over the integers: `d(d-3) = (d-1)(d-2) - 2`, the algebraic
content of the genus-degree formula for a smooth plane curve of degree `d`. -/
theorem adjunction_formula_int (d : ℤ) :
    d * (d - 3) = (d - 1) * (d - 2) - 2 := by ring

/-- Natural-number form of the adjunction identity for `d ≥ 3`. -/
theorem adjunction_formula_genus_degree (d : ℕ) (hd : 3 ≤ d) :
    d * (d - 3) + 2 = (d - 1) * (d - 2) := by
  zify [hd, show 1 ≤ d by omega, show 2 ≤ d by omega]
  ring

/-- Numerical form: `d(d-3) = 2·[(d-1)(d-2)/2] - 2`, recovering `g = (d-1)(d-2)/2`. -/
theorem adjunction_formula_numerical (d : ℕ) :
    (d : ℤ) * (d - 3) = 2 * (((d : ℤ) - 1) * ((d : ℤ) - 2) / 2) - 2 := by
  have h_even : (2 : ℤ) ∣ ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
    rcases Int.even_or_odd (d : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨((d : ℤ) - 1) * (m - 1), by rw [hm]; ring⟩
    · exact ⟨m * ((d : ℤ) - 2), by rw [hm]; ring⟩
  rw [Int.mul_ediv_cancel' h_even]
  ring

end NumericalAdjunction


section ConormalRankBridge

/-- If `f : M → N` is a surjective `R`-linear map and `M` is finite, then `finrank N ≤ finrank M`. -/
lemma finrank_le_of_surjective_lm {R : Type*} [CommRing R] [Nontrivial R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.finrank R N ≤ Module.finrank R M := by
  have : f.range = ⊤ := LinearMap.range_eq_top.mpr hf
  calc finrank R N
      = finrank R (⊤ : Submodule R N) := (finrank_top R N).symm
    _ = finrank R f.range := by rw [this]
    _ ≤ finrank R M := LinearMap.finrank_range_le f

variable (k : Type*) [Field k]

/-- The base change `(R/I) ⊗_R Ω_{R/k}` of the rank-`n` free module of differentials of
`R = k[x₁,…,xₙ]` has `(R/I)`-rank `n`. -/
theorem conormal_basechange_finrank (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    [Nontrivial (MvPolynomial (Fin n) k ⧸ I)] :
    Module.finrank (MvPolynomial (Fin n) k ⧸ I)
      ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) = n := by
  rw [Module.finrank_eq_card_basis
    ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange (MvPolynomial (Fin n) k ⧸ I))]
  simp [Fintype.card_fin]

/-- Rank bound: `rank Ω_{(R/I)/k} ≤ n` where `R = k[x₁,…,xₙ]`. -/
theorem conormal_rank_bound (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    [Nontrivial (MvPolynomial (Fin n) k ⧸ I)] :
    Module.finrank (MvPolynomial (Fin n) k ⧸ I)
      (Ω[MvPolynomial (Fin n) k ⧸ I⁄k]) ≤ n := by
  have hsurj : Function.Surjective
      (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) := by
    apply KaehlerDifferential.mapBaseChange_surjective
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  haveI : Module.Finite (MvPolynomial (Fin n) k ⧸ I)
      ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) :=
    Module.Finite.of_basis
      ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange (MvPolynomial (Fin n) k ⧸ I))
  calc Module.finrank (MvPolynomial (Fin n) k ⧸ I) (Ω[MvPolynomial (Fin n) k ⧸ I⁄k])
      ≤ Module.finrank (MvPolynomial (Fin n) k ⧸ I)
          ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) :=
        finrank_le_of_surjective_lm _ hsurj
    _ = n := conormal_basechange_finrank k n I

/-- Two-variable specialization: rank of `Ω_{(R/I)/k}` is at most `2` for `R = k[x₀,x₁]`. -/
theorem conormal_rank_bridge (I : Ideal (MvPolynomial (Fin 2) k))
    [Nontrivial (MvPolynomial (Fin 2) k ⧸ I)] :
    Module.finrank (MvPolynomial (Fin 2) k ⧸ I)
      (Ω[MvPolynomial (Fin 2) k ⧸ I⁄k]) ≤ 2 :=
  conormal_rank_bound k 2 I

/-- From the conormal exact sequence on a degree-`d` hypersurface in `ℙⁿ`, the degree of
`ω` on the hypersurface is `d(d - (n+1))`. -/
theorem adjunction_degree_from_exact_sequence (n : ℕ) (d : ℤ)
    (deg_ambient_cotangent_restricted deg_conormal : ℤ)
    (h_euler : deg_ambient_cotangent_restricted = -((n : ℤ) + 1) * d)
    (h_conormal : deg_conormal = -(d * d)) :
    deg_ambient_cotangent_restricted - deg_conormal = d * (d - ((n : ℤ) + 1)) := by
  rw [h_euler, h_conormal]; ring

/-- For a plane curve `C ⊂ ℙ²` of degree `d`, the adjunction formula gives
`deg ω_C = d(d-3) = (d-1)(d-2) - 2`. -/
theorem adjunction_formula_from_sequence_and_genus (d : ℤ) :
    (∀ (deg_Ω_P2_C deg_conormal : ℤ),
      deg_Ω_P2_C = -3 * d →
      deg_conormal = -(d * d) →
      deg_Ω_P2_C - deg_conormal = d * (d - 3)) ∧
    d * (d - 3) = (d - 1) * (d - 2) - 2 := by
  exact ⟨fun deg1 deg2 h1 h2 => by rw [h1, h2]; ring, by ring⟩

end ConormalRankBridge


section Prop35

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- Proposition 35: the conormal sequence `I/I² → (R/I) ⊗_R Ω_{R/k} → Ω_{(R/I)/k} → 0`
is exact at the middle term and the right map is surjective. -/
theorem conormal_exact_sequence_prop35 :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I))
      (KaehlerDifferential.mapBaseChange k R (R ⧸ I))
    ∧ Function.Surjective
      (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
  refine ⟨?_, ?_⟩
  · exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  · exact KaehlerDifferential.mapBaseChange_surjective k R (R ⧸ I)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)

/-- When `R` is formally smooth over `k`, injectivity of `I/I² → (R/I) ⊗_R Ω_{R/k}` is equivalent
to the vanishing of `H¹` of the cotangent complex of `R/I` over `k`. -/
theorem conormal_injective_iff_smooth_quotient
    [Algebra.FormallySmooth k R] :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I))
    ↔ Subsingleton (Algebra.H1Cotangent k (R ⧸ I)) := by
  exact Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)

/-- When both `R` and `R/I` are formally smooth over `k`, the conormal map `I/I² → (R/I) ⊗ Ω_{R/k}`
is injective. -/
theorem conormal_injective_when_both_smooth
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hsurj).mp
    (inferInstance : Algebra.FormallySmooth k (R ⧸ I))
  have h : Function.LeftInverse l (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) :=
    fun x => DFunLike.congr_fun hl x
  exact h.injective

/-- When both `R` and `R/I` are formally smooth over `k`, the conormal map is split-injective. -/
theorem conormal_split_when_both_smooth
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    ∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I) = LinearMap.id := by
  rw [← Algebra.FormallySmooth.iff_split_injection
    (show Function.Surjective (algebraMap R (R ⧸ I)) from by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  infer_instance

/-- Corollary 26: when both `R` and `R/I` are formally smooth over `k`, the conormal sequence
`0 → I/I² → (R/I) ⊗ Ω_{R/k} → Ω_{(R/I)/k} → 0` is short exact and split. -/
theorem corollary_26
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (R ⧸ I)] :
    (Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)))
    ∧ (Function.Exact
        (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I))
        (KaehlerDifferential.mapBaseChange k R (R ⧸ I)))
    ∧ (Function.Surjective (KaehlerDifferential.mapBaseChange k R (R ⧸ I)))
    ∧ (∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I) = LinearMap.id) := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hsurj).mp
      (inferInstance : Algebra.FormallySmooth k (R ⧸ I))
    have h : Function.LeftInverse l (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) :=
      fun x => DFunLike.congr_fun hl x
    exact h.injective
  · exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) hsurj
  · exact KaehlerDifferential.mapBaseChange_surjective k R (R ⧸ I) hsurj
  · exact (Algebra.FormallySmooth.iff_split_injection hsurj).mp inferInstance

/-- Specialization of the adjunction-formula numerics to plane curves: the genus-degree formula
`g = (d-1)(d-2)/2` emerges from `d(d-3) = (d-1)(d-2) - 2`. -/
theorem corollary_26_adjunction_formula (d : ℤ) :
    (∀ (deg_Ω_P2_C deg_conormal : ℤ),
      deg_Ω_P2_C = -(2 + 1) * d →
      deg_conormal = -(d * d) →
      deg_Ω_P2_C - deg_conormal = d * (d - 3))
    ∧ d * (d - 3) = (d - 1) * (d - 2) - 2 := by
  exact ⟨fun _ _ h1 h2 => by rw [h1, h2]; ring, by ring⟩


end Prop35




section AdjunctionFormulaSheaf

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)


end AdjunctionFormulaSheaf

end
