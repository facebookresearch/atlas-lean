/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Polynomial TensorProduct

noncomputable section

namespace TensorSplitting

lemma span_prod_eq_biInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → R)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j)) :
    Ideal.span ({∏ i ∈ s, g i} : Set R) = ⨅ i ∈ s, Ideal.span ({g i} : Set R) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hc_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j) :=
      fun i hi j hj hij =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [Finset.prod_insert ha, Finset.iInf_insert]
    have h_coprime : IsCoprime (g a) (∏ i ∈ s, g i) := by
      apply IsCoprime.prod_right
      intro i hi
      exact hc a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    rw [← ih hc_s, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_eq_inf_of_isCoprime
      ((Ideal.isCoprime_span_singleton_iff _ _).mpr h_coprime)

lemma span_prod_eq_iInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    [Fintype ι] (g : ι → R) (hc : Pairwise fun i j => IsCoprime (g i) (g j)) :
    Ideal.span ({∏ i, g i} : Set R) = ⨅ i, Ideal.span ({g i} : Set R) := by
  have h1 : ∏ i, g i = ∏ i ∈ Finset.univ, g i := by simp
  have h2 : (⨅ i, Ideal.span ({g i} : Set R)) =
      ⨅ i ∈ Finset.univ, Ideal.span ({g i} : Set R) := by simp
  rw [h1, h2]
  exact span_prod_eq_biInf Finset.univ g (fun i _ j _ hij => hc hij)

lemma isCoprime_of_irreducible_of_not_associated {K : Type*} [Field K]
    {p q : Polynomial K}
    (hp : Irreducible p) (hq : Irreducible q) (hne : ¬Associated p q) :
    IsCoprime p q := by
  have hp' : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  exact hp'.coprime_iff_not_dvd.mpr
    (fun h => hne (hp'.associated_of_dvd
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq) h))

lemma quotientInfRingEquivPiQuotient_algebraMap
    {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (I : ι → Ideal (Polynomial K'))
    (hc : Pairwise fun i j => IsCoprime (I i) (I j))
    (k : K') :
    (Ideal.quotientInfRingEquivPiQuotient I hc) ((algebraMap K' _) k) =
    (algebraMap K' _) k := by
  change (Ideal.quotientInfToPiQuotient I)
    ((Ideal.Quotient.mk _).comp C k) = _
  simp only [RingHom.comp_apply]
  unfold Ideal.quotientInfToPiQuotient
  simp only [Ideal.Quotient.lift_mk]
  ext i; rfl

def quotientInfAlgEquivPiQuotient
    {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (I : ι → Ideal (Polynomial K'))
    (hc : Pairwise fun i j => IsCoprime (I i) (I j)) :
    (Polynomial K' ⧸ ⨅ i, I i) ≃ₐ[K'] (∀ i, Polynomial K' ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient I hc)
    (quotientInfRingEquivPiQuotient_algebraMap I hc)

def adjoinRootProdAlgEquiv {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι]
    [Fintype ι] (g : ι → Polynomial K')
    (hc : Pairwise fun i j => IsCoprime (g i) (g j)) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K'] ∀ i, AdjoinRoot (g i) :=
  (Ideal.quotientEquivAlgOfEq K' (span_prod_eq_iInf g hc)).trans
    (quotientInfAlgEquivPiQuotient (fun i => Ideal.span {g i})
      (fun _ _ hij => (Ideal.isCoprime_span_singleton_iff _ _).mpr (hc hij)))

def adjoinRootProdAlgEquiv_of_irreducible {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (g : ι → Polynomial K') (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j)) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K'] ∀ i, AdjoinRoot (g i) :=
  adjoinRootProdAlgEquiv g
    (fun _ _ hij => isCoprime_of_irreducible_of_not_associated (hirr _) (hirr _) (hne hij))

lemma polyEquivTensor'_symm_comp_includeRight
    {K K' : Type*} [Field K] [Field K'] [Algebra K K'] :
    ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* Polynomial K').comp
      (↑(Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        : Polynomial K →+* K' ⊗[K] Polynomial K) =
      Polynomial.mapRingHom (algebraMap K K') := by
  ext
  case h₁ k =>
    simp only [RingHom.comp_apply, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_C, Polynomial.map_C]
    simp [Polynomial.mapRingHom]
  case h₂ =>
    simp only [RingHom.comp_apply, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_X, Polynomial.map_X]
    simp [Polynomial.mapRingHom]

def adjoinRoot_tensorProduct_algEquiv
    {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (f : Polynomial K) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] AdjoinRoot (Polynomial.map (algebraMap K K') f) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')

  let e1 : (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] K' ⊗[K] AdjoinRoot f :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm K (AdjoinRoot f) K').toRingEquiv)
      (fun k' => by
        show (Algebra.TensorProduct.comm K (AdjoinRoot f) K') (1 ⊗ₜ[K] k') = k' ⊗ₜ[K] 1
        simp [Algebra.TensorProduct.comm_tmul])

  let e2 : K' ⊗[K] AdjoinRoot f ≃ₐ[K']
      (K' ⊗[K] Polynomial K) ⧸
        Ideal.map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
          (Ideal.span {f}) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := K) K' (Polynomial K) K' (Ideal.span {f})

  have hideal : Ideal.map ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* Polynomial K')
      (Ideal.map (↑(Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        : Polynomial K →+* K' ⊗[K] Polynomial K)
        (Ideal.span {f})) =
      Ideal.span {Polynomial.map (algebraMap K K') f} := by
    rw [Ideal.map_map, polyEquivTensor'_symm_comp_includeRight, Ideal.map_span,
      Set.image_singleton]
    rfl
  let e3 : ((K' ⊗[K] Polynomial K) ⧸
      Ideal.map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        (Ideal.span {f})) ≃ₐ[K']
      AdjoinRoot (Polynomial.map (algebraMap K K') f) :=
    (Ideal.quotientEquivAlg _ _ (polyEquivTensor' K K').symm rfl).trans
      (Ideal.quotientEquivAlgOfEq K' hideal)
  exact e1.trans (e2.trans e3)

def adjoinRoot_tensor_algEquiv_prod {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : Polynomial K) (_hf_irr : Irreducible f) (_hf_sep : f.Separable)
    (g : ι → Polynomial K') (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] ∀ i, AdjoinRoot (g i) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
  exact (adjoinRoot_tensorProduct_algEquiv f).trans
    ((Ideal.quotientEquivAlgOfEq K'
        (Ideal.span_singleton_eq_span_singleton.mpr hprod) :
        AdjoinRoot (Polynomial.map (algebraMap K K') f) ≃ₐ[K']
          AdjoinRoot (∏ i, g i)).trans
      (adjoinRootProdAlgEquiv_of_irreducible g hirr hne))

end TensorSplitting

end
