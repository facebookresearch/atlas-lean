/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.FunctionFieldGenerators
import Atlas.ArithmeticGeometry.code.ProductVarieties
import Atlas.ArithmeticGeometry.code.CotangentLocal
import Atlas.ArithmeticGeometry.code.RegularFunctions

noncomputable section

open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial

section GeometricTangentSpace

variable {k : Type*} [Field k] {n : ℕ}

def totalDerivativeAt (f : MvPolynomial (Fin n) k) (P : Fin n → k) (v : Fin n → k) : k :=
  ∑ i : Fin n, MvPolynomial.eval P (MvPolynomial.pderiv i f) * v i

def totalDerivativeAtLin (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] k where
  toFun v := totalDerivativeAt f P v
  map_add' a b := by
    simp only [totalDerivativeAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [totalDerivativeAt, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Finset.mul_sum, RingHom.id_apply]

def tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  LinearMap.ker (totalDerivativeAtLin f P)

def tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  ⨅ f ∈ I, tangentSpacePoly f P

lemma totalDerivativeAt_add (f g : MvPolynomial (Fin n) k) (P v : Fin n → k) :
    totalDerivativeAt (f + g) P v =
      totalDerivativeAt f P v + totalDerivativeAt g P v := by
  simp only [totalDerivativeAt, map_add, add_mul, Finset.sum_add_distrib]

lemma totalDerivativeAt_zero (P v : Fin n → k) :
    totalDerivativeAt 0 P v = 0 := by
  simp [totalDerivativeAt, map_zero]

lemma totalDerivativeAt_mul_of_eval_eq_zero (r g : MvPolynomial (Fin n) k)
    (P v : Fin n → k) (hg : MvPolynomial.eval P g = 0) :
    totalDerivativeAt (r * g) P v =
      MvPolynomial.eval P r * totalDerivativeAt g P v := by
  simp only [totalDerivativeAt, pderiv_mul, map_add, MvPolynomial.eval_mul, hg,
    mul_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

lemma totalDerivativeAt_smul_of_eval_eq_zero (r g : MvPolynomial (Fin n) k)
    (P v : Fin n → k) (hg : MvPolynomial.eval P g = 0) :
    totalDerivativeAt (r • g) P v =
      MvPolynomial.eval P r * totalDerivativeAt g P v := by
  rw [smul_eq_mul]
  exact totalDerivativeAt_mul_of_eval_eq_zero r g P v hg

theorem tangentSpaceIdeal_eq_iInf_generators {m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k)
    (hP : ∀ g ∈ Ideal.span (Set.range f), MvPolynomial.eval P g = 0) :
    tangentSpaceIdeal (Ideal.span (Set.range f)) P =
    ⨅ i : Fin m, tangentSpacePoly (f i) P := by
  ext v
  simp only [tangentSpaceIdeal, Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h i
    exact h (f i) (Ideal.subset_span (Set.mem_range_self i))
  · intro h g hg
    refine Submodule.span_induction
      (p := fun g _ => totalDerivativeAt g P v = 0) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨i, rfl⟩
      exact h i
    · exact totalDerivativeAt_zero P v
    · intro g₁ g₂ _ _ h₁ h₂
      rw [totalDerivativeAt_add, h₁, h₂, add_zero]
    · intro r g hg_mem hg_val
      rw [totalDerivativeAt_smul_of_eval_eq_zero r g P v (hP g hg_mem), hg_val, mul_zero]

theorem tangentSpace_eq_ker_jacobian {m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k) :
    (⨅ i : Fin m, tangentSpacePoly (f i) P) =
    LinearMap.ker
      (Matrix.of (fun i j =>
        MvPolynomial.eval P (MvPolynomial.pderiv j (f i))) :
        Matrix (Fin m) (Fin n) k).mulVecLin := by
  ext v
  simp only [Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk, mulVecLin_apply]
  constructor
  · intro h
    ext i
    simp only [mulVec, dotProduct, Pi.zero_apply]
    convert h i using 1
  · intro h i
    have := congr_fun h i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    simp only [totalDerivativeAt]
    convert this using 1

def jointLinearizationMap {m : ℕ} (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] (Fin m → k) where
  toFun v := fun i => totalDerivativeAtLin (f i) P v
  map_add' a b := by ext i; simp [totalDerivativeAtLin, map_add]
  map_smul' c v := by ext i; simp [totalDerivativeAtLin, map_smul]

lemma tangentSpace_eq_ker_jointLinearizationMap {m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k) :
    (⨅ i : Fin m, tangentSpacePoly (f i) P) = LinearMap.ker (jointLinearizationMap f P) := by
  ext v
  simp [Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker, jointLinearizationMap,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]

theorem cotangentSpace_dualAnnihilator_eq_range_dualMap {m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k) :
    (⨅ i : Fin m, tangentSpacePoly (f i) P).dualAnnihilator =
    LinearMap.range (jointLinearizationMap f P).dualMap := by
  rw [tangentSpace_eq_ker_jointLinearizationMap]
  exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker (jointLinearizationMap f P)).symm

end GeometricTangentSpace

namespace TangentSpaces

variable {k : Type*} [Field k]

def jacobianMatrix (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) k)
    (P : Fin n → k) : Matrix (Fin m) (Fin n) k :=
  Matrix.of fun i j => MvPolynomial.eval P ((MvPolynomial.pderiv j) (f i))

def tangentSpace {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) : Submodule k (Fin n → k) :=
  LinearMap.ker M.mulVecLin

def cotangentSpaceDual {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    Submodule k (Module.Dual k (Fin n → k)) :=
  (tangentSpace M).dualAnnihilator

def cotangentSpace {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) : Submodule k (Fin m → k) :=
  LinearMap.range M.mulVecLin


theorem tangent_dim_eq_sub_jacobian_rank {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    finrank k (tangentSpace M) = n - M.rank := by
  unfold tangentSpace Matrix.rank
  have h := finrank_range_add_finrank_ker M.mulVecLin
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

theorem jacobian_rank_add_tangent_dim {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    M.rank + finrank k (tangentSpace M) = n := by
  unfold tangentSpace Matrix.rank
  have h := finrank_range_add_finrank_ker M.mulVecLin
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

theorem jacobian_rank_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    M.rank ≤ n := by
  have h := jacobian_rank_add_tangent_dim M
  omega

lemma tangentSpace_jacobian_eq_tangentSpaceIdeal {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k)
    (hP : ∀ g ∈ Ideal.span (Set.range f), MvPolynomial.eval P g = 0) :
    tangentSpace (jacobianMatrix n m f P) =
    tangentSpaceIdeal (Ideal.span (Set.range f)) P := by
  rw [tangentSpaceIdeal_eq_iInf_generators f P hP]
  exact (tangentSpace_eq_ker_jacobian f P).symm


theorem rank_le_one_of_single_row {n : ℕ} (M : Matrix (Fin 1) (Fin n) k) :
    M.rank ≤ 1 := by
  unfold Matrix.rank
  calc finrank k (LinearMap.range M.mulVecLin)
      ≤ finrank k (Fin 1 → k) := Submodule.finrank_le _
    _ = 1 := by simp [finrank_fintype_fun_eq_card]


end TangentSpaces

open IntermediateField Cardinal

theorem function_field_generated_by_n_plus_one
    (k : Type*) (F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (n : ℕ) (hfg : (⊤ : IntermediateField k F).FG)
    (htrdeg : Algebra.trdeg k F = n) :
    ∃ (α : Fin (n + 1) → F),
      AlgebraicIndependent k (fun i : Fin n => α (Fin.castSucc i)) ∧
      IntermediateField.adjoin k (Set.range α) = ⊤ := by

  haveI : Algebra.EssFiniteType k F := IntermediateField.fg_top_iff.mp hfg

  obtain ⟨t, α, ht_indep, _, ht_gen⟩ := function_field_generators k F n htrdeg

  refine ⟨Fin.snoc t α, ?_, ?_⟩

  · convert ht_indep using 1
    simp only [Fin.snoc_castSucc]

  · rw [Fin.range_snoc]
    exact ht_gen


open MvPolynomial in
def IsHypersurface (k : Type*) [Field k] (N : ℕ)
    (W : Set (AffineSpace_k k N)) : Prop :=
  IsAffineVariety k N W ∧
    (idealOfAlgebraicSet W).IsPrincipal ∧
    idealOfAlgebraicSet W ≠ ⊥

theorem coordinateRingBar_isDomain' (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    IsDomain (AffineCoordinateRingBar V) :=
  coordinateRingBar_isDomain k hV

def functionField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) : Type _ :=
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV

  FractionRing (AffineCoordinateRingBar V)

@[reducible] noncomputable def functionField.instField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := by
  unfold functionField
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV
  exact FractionRing.field (AffineCoordinateRingBar V)

noncomputable instance (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := functionField.instField k N V hV

@[reducible] noncomputable def functionField.instAlgebra (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Algebra (AlgebraicClosure k) (functionField k N V hV) := by
  letI : IsDomain (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) :=
    coordinateRingBar_isDomain' k N V hV
  show Algebra (AlgebraicClosure k) (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  infer_instance

noncomputable instance (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Algebra (AlgebraicClosure k) (functionField k N V hV) := functionField.instAlgebra k N V hV

def HasDimension (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (d : ℕ) : Prop :=
  ∃ (hV : IsAffineVariety k N V),
    Algebra.trdeg (AlgebraicClosure k) (functionField k N V hV) = d

theorem functionField_fg (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    (⊤ : IntermediateField (AlgebraicClosure k) (functionField k N V hV)).FG := by


  rw [IntermediateField.fg_top_iff]
  letI : IsDomain (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) :=
    coordinateRingBar_isDomain' k N V hV
  show Algebra.EssFiniteType (AlgebraicClosure k)
    (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V)
      (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors _)
  exact Algebra.EssFiniteType.comp (AlgebraicClosure k)
    (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) _















theorem irreducible_poly_vanishing_on_generators
    (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)
    (F : Type*) [Field F] [Algebra (AlgebraicClosure k) F]
    (α : Fin (n + 1) → F)
    (h_indep : AlgebraicIndependent (AlgebraicClosure k) (fun i : Fin n => α (Fin.castSucc i)))
    (h_gen : IntermediateField.adjoin (AlgebraicClosure k) (Set.range α) = ⊤)
    (h_not_indep : ¬ AlgebraicIndependent (AlgebraicClosure k) α) :
    ∃ (f : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)),
      Irreducible f ∧ MvPolynomial.aeval α f = 0 := by


  rw [algebraicIndependent_iff_injective_aeval] at h_not_indep

  have hker_ne_bot : RingHom.ker (MvPolynomial.aeval α :
      MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k] F) ≠ ⊥ := by
    intro h
    exact h_not_indep ((RingHom.injective_iff_ker_eq_bot _).mpr h)

  have hker_prime : (RingHom.ker (MvPolynomial.aeval α :
      MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k] F)).IsPrime :=
    RingHom.ker_isPrime _

  obtain ⟨f, hf_mem, hf_prime⟩ := hker_prime.exists_mem_prime_of_ne_bot hker_ne_bot

  exact ⟨f, hf_prime.irreducible, by rwa [RingHom.mem_ker] at hf_mem⟩

lemma nullstellensatz_irreducible
    (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (f : MvPolynomial (Fin N) (AlgebraicClosure k))
    (hf_irred : Irreducible f) :
    idealOfAlgebraicSet (AlgebraicSet k N ({f} : Set (MvPolynomial (Fin N) (AlgebraicClosure k)))) =
      Ideal.span {f} := by

  have hset : AlgebraicSet k N {f} = AlgebraicSet k N (Ideal.span {f} : Set _) := by
    ext P
    simp only [AlgebraicSet, Set.mem_setOf_eq]
    constructor
    · intro hP g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        simp only [Set.mem_singleton_iff] at hx
        rw [hx]; exact hP f (Set.mem_singleton f)
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | smul a x _ hx => simp [map_mul, hx]
    · intro hP g hg
      exact hP g (Ideal.subset_span hg)

  rw [hset, hilbert_nullstellensatz k]

  have hprime : (Ideal.span {f}).IsPrime := by
    rw [Ideal.span_singleton_prime (Irreducible.ne_zero hf_irred)]
    exact hf_irred.prime
  exact hprime.radical



theorem hypersurface_isAffineVariety
    (k : Type*) [Field k] (N : ℕ)
    (f : MvPolynomial (Fin N) (AlgebraicClosure k))
    (hf : Irreducible f) :
    IsAffineVariety k N (AlgebraicSet k N {f}) := by
  constructor
  ·
    exact algebraicSet_isAlgebraicSubset k {f}
  ·
    rw [isIrreducibleAlgebraicSet_iff_isPrime k (algebraicSet_isAlgebraicSubset k {f})]


    have hset : AlgebraicSet k N {f} = AlgebraicSet k N (Ideal.span {f} : Set _) := by
      ext P
      simp only [AlgebraicSet, Set.mem_setOf_eq]
      constructor
      · intro hP g hg
        induction hg using Submodule.span_induction with
        | mem x hx =>
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]; exact hP f (Set.mem_singleton f)
        | zero => simp
        | add x y _ _ hx hy => simp [map_add, hx, hy]
        | smul a x _ hx => simp [map_mul, hx]
      · intro hP g hg
        exact hP g (Ideal.subset_span hg)

    rw [hset, hilbert_nullstellensatz k]

    have hprime : (Ideal.span {f}).IsPrime := by
      rw [Ideal.span_singleton_prime (Irreducible.ne_zero hf)]
      exact hf.prime

    rw [hprime.radical]
    exact hprime

theorem isHypersurface_of_irreducible (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (f : MvPolynomial (Fin N) (AlgebraicClosure k))
    (hf : Irreducible f) :
    IsHypersurface k N (AlgebraicSet k N {f}) := by
  refine ⟨hypersurface_isAffineVariety k N f hf, ?_, ?_⟩
  ·
    rw [nullstellensatz_irreducible k N f hf]
    exact ⟨⟨f, rfl⟩⟩
  ·
    rw [nullstellensatz_irreducible k N f hf]
    intro h
    have : f ∈ (⊥ : Ideal (MvPolynomial (Fin N) (AlgebraicClosure k))) := by
      rw [← h]; exact Ideal.subset_span (Set.mem_singleton f)
    simp at this
    exact hf.ne_zero this

theorem IsHypersurface.exists_irreducible {k : Type*} [Field k] {N : ℕ}
    {W : Set (AffineSpace_k k N)} (hW : IsHypersurface k N W) :
    ∃ f : MvPolynomial (Fin N) (AlgebraicClosure k),
      Irreducible f ∧ W = AlgebraicSet k N {f} := by
  obtain ⟨hVar, hPrinc, hNe⟩ := hW

  obtain ⟨g, hg⟩ := hPrinc.principal

  have hg_ne : g ≠ 0 := by
    intro heq; apply hNe; rw [hg, heq]; simp [Submodule.span_singleton_eq_bot]

  have hprime := (isIrreducibleAlgebraicSet_iff_isPrime k hVar.1).mp hVar.2
  rw [hg] at hprime
  have hg_prime : Prime g := by
    have : (Ideal.span {g}).IsPrime := by convert hprime
    rwa [Ideal.span_singleton_prime hg_ne] at this
  have hg_irred : Irreducible g := hg_prime.irreducible

  refine ⟨g, hg_irred, ?_⟩
  have h_VIW : W = AlgebraicSet k N (idealOfAlgebraicSet W : Set _) :=
    (algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hVar.1).symm
  rw [hg] at h_VIW
  convert h_VIW using 1
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hP f hf
    have hfg : f ∈ (MvPolynomial (Fin N) (AlgebraicClosure k) ∙ g) := hf
    simp only [Submodule.mem_span_singleton] at hfg
    obtain ⟨c, rfl⟩ := hfg
    simp [MvPolynomial.eval_mul, hP g (Set.mem_singleton g)]
  · intro hP f hf
    have hfg : f = g := Set.mem_singleton_iff.mp hf
    rw [hfg]
    exact hP g (Submodule.mem_span_singleton_self g)






open ProjectiveVarietyDef AffinePatch
open scoped LinearAlgebra.Projectivization

def affinePartOfProjective (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)))
    (i : Fin (n + 1)) : Set (Fin n → AlgebraicClosure k) :=
  (affinePatchEquiv (AlgebraicClosure k) i) '' {p : affinePatch (AlgebraicClosure k) i | ↑p ∈ V}

def IsProjectiveHypersurface (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))) : Prop :=
  IsProjectiveVariety (AlgebraicClosure k) V ∧
    ∃ F : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k),
      Irreducible F ∧ (∃ d, F.IsHomogeneous d) ∧
      V = ProjectiveAlgebraicSet (AlgebraicClosure k) {F}

def HasProjectiveDimension (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))) (d : ℕ) : Prop :=
  IsProjectiveVariety (AlgebraicClosure k) V ∧
    ∃ (i : Fin (n + 1)),
      HasDimension k n (affinePartOfProjective k V i) d







namespace SingularLocus

variable (k : Type*) [Field k]

open MvPolynomial Matrix

theorem rank_lt_iff_all_minors_det_eq_zero
    {k' : Type*} [Field k'] {m n r : ℕ}
    (M : Matrix (Fin m) (Fin n) k') :
    M.rank < r ↔
      ∀ (ri : Fin r → Fin m) (ci : Fin r → Fin n),
        (M.submatrix ri ci).det = 0 := by
  constructor
  ·
    intro hrank ri ci
    by_contra hne
    have hdet : IsUnit (M.submatrix ri ci).det := isUnit_iff_ne_zero.mpr hne
    have hU : IsUnit (M.submatrix ri ci) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    have hrank_sub : (M.submatrix ri ci).rank = r := by
      apply le_antisymm
      · calc (M.submatrix ri ci).rank ≤ Fintype.card (Fin r) :=
              (M.submatrix ri ci).rank_le_card_width
          _ = r := Fintype.card_fin r
      · calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
          _ = (1 : Matrix (Fin r) (Fin r) k').rank := by simp [Matrix.rank_one]
          _ = ((M.submatrix ri ci)⁻¹ * (M.submatrix ri ci)).rank := by
              rw [Matrix.nonsing_inv_mul _ hdet]
          _ ≤ (M.submatrix ri ci).rank := Matrix.rank_mul_le_right _ _
    have hsub : (M.submatrix ri ci).rank ≤ M.rank := by
      let P : Matrix (Fin r) (Fin m) k' := Matrix.of fun i j => if j = ri i then (1:k') else 0
      let Q : Matrix (Fin n) (Fin r) k' := Matrix.of fun i j => if i = ci j then (1:k') else 0
      have hPMQ : M.submatrix ri ci = P * M * Q := by
        ext i j
        simp only [P, Q, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
        have h1 : ∀ x, (∑ x_1, (if x_1 = ri i then (1:k') else 0) * M x_1 x) =
            M (ri i) x := by
          intro x; rw [Finset.sum_eq_single (ri i)]; simp; intro b _ hb; simp [hb]
          exact fun h => absurd (Finset.mem_univ _) h
        simp_rw [h1]; rw [Finset.sum_eq_single (ci j)]; simp; intro b _ hb; simp [hb]
        exact fun h => absurd (Finset.mem_univ _) h
      rw [hPMQ, Matrix.mul_assoc]
      exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)
    omega
  ·
    intro hMinors
    by_contra h
    simp only [not_lt] at h

    obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' k' M.col
    haveI : Fintype κ := Fintype.ofInjective a ha_inj
    have hcard : Fintype.card κ = M.rank := by
      have h1 := finrank_span_eq_card ha_li
      rw [ha_span] at h1; rw [← Matrix.rank_eq_finrank_span_cols] at h1; omega
    classical
    let ci := a ∘ (Fintype.equivFin κ).symm ∘ Fin.castLE (hcard ▸ h)
    have hci : LinearIndependent k' (M.col ∘ ci) :=
      ha_li.comp _ ((Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective _))

    let N := M.submatrix _root_.id ci
    have hN_rank : N.rank = r := by
      rw [Matrix.rank_eq_finrank_span_cols]
      have : N.col = M.col ∘ ci := by
        ext j i; simp [N, Matrix.submatrix_apply, Matrix.col_apply]
      rw [this, finrank_span_eq_card hci, Fintype.card_fin]

    have hNt : N.transpose.rank = r := by rw [Matrix.rank_transpose]; exact hN_rank
    obtain ⟨κ₂, a₂, ha2_inj, ha2_span, ha2_li⟩ := exists_linearIndependent' k' N.transpose.col
    haveI : Fintype κ₂ := Fintype.ofInjective a₂ ha2_inj
    have hcard₂ : Fintype.card κ₂ = r := by
      have h2 := finrank_span_eq_card ha2_li
      rw [ha2_span, ← Matrix.rank_eq_finrank_span_cols, hNt] at h2; omega
    let ri := a₂ ∘ (Fintype.equivFin κ₂).symm ∘ Fin.castLE hcard₂.ge
    have hri : LinearIndependent k' (N.transpose.col ∘ ri) :=
      ha2_li.comp _ ((Fintype.equivFin κ₂).symm.injective.comp (Fin.castLE_injective _))

    have hrows : LinearIndependent k' (M.submatrix ri ci).row := by
      have key : (M.submatrix ri ci).row = N.transpose.col ∘ ri := by
        ext i j
        simp [Matrix.row_apply, Matrix.submatrix_apply, Matrix.col_apply,
              Matrix.transpose_apply, N]
      rw [key]; exact hri
    have hU := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (hMinors ri ci)

def jacobianPolyMatrix (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  Matrix.of fun i j => (MvPolynomial.pderiv j) (f i)

def minorDetPolys (n m r : ℕ)
    (M : Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  { d | ∃ (ri : Fin r → Fin m) (ci : Fin r → Fin n),
    d = (M.submatrix ri ci).det }

lemma eval_minor_det_eq (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k)
    (ri : Fin r → Fin m) (ci : Fin r → Fin n) :
    MvPolynomial.eval P (((jacobianPolyMatrix k n m f).submatrix ri ci).det) =
    ((TangentSpaces.jacobianMatrix n m f P).submatrix ri ci).det := by
  rw [RingHom.map_det]
  congr 1

def singularLocusIntrinsic (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  { P | P ∈ AlgebraicSet k n (Set.range f) ∧
        (TangentSpaces.jacobianMatrix n m f P).rank < r }

def singularLocusPolys (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  Set.range f ∪ minorDetPolys k n m r (jacobianPolyMatrix k n m f)

def singularLocusAlgebraic (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  AlgebraicSet k n (singularLocusPolys k n m r f)

theorem mem_singularLocusAlgebraic_iff (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : AffineSpace_k k n) :
    P ∈ singularLocusAlgebraic k n m r f ↔
      (∀ i, MvPolynomial.eval P (f i) = 0) ∧
      (∀ (ri : Fin r → Fin m) (ci : Fin r → Fin n),
        ((TangentSpaces.jacobianMatrix n m f P).submatrix ri ci).det = 0) := by
  constructor
  · intro hP
    constructor
    · intro i
      exact hP (f i) (Set.mem_union_left _ (Set.mem_range_self i))
    · intro ri ci
      have hd := hP _ (Set.mem_union_right _ ⟨ri, ci, rfl⟩)
      rwa [eval_minor_det_eq] at hd
  · intro ⟨hV, hminors⟩ g hg
    rcases hg with ⟨i, rfl⟩ | ⟨ri, ci, rfl⟩
    · exact hV i
    · rw [eval_minor_det_eq]
      exact hminors ri ci

theorem singularLocus_eq_algebraicSet (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    singularLocusIntrinsic k n m r f = singularLocusAlgebraic k n m r f := by
  ext P
  simp only [singularLocusIntrinsic, Set.mem_setOf_eq]
  rw [mem_singularLocusAlgebraic_iff]
  constructor
  · intro ⟨hPV, hrank⟩
    refine ⟨fun i => hPV (f i) (Set.mem_range_self i), ?_⟩
    exact (rank_lt_iff_all_minors_det_eq_zero _).mp hrank
  · intro ⟨hPolys, hMinors⟩
    refine ⟨fun g hg => ?_, (rank_lt_iff_all_minors_det_eq_zero _).mpr hMinors⟩
    obtain ⟨i, rfl⟩ := hg
    exact hPolys i

theorem singular_locus_is_closed_subset
    (k : Type*) [Field k] (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    IsAlgebraicSubset k n (singularLocusIntrinsic k n m r f) ∧
    singularLocusIntrinsic k n m r f ⊆ AlgebraicSet k n (Set.range f) := by
  constructor
  ·
    rw [singularLocus_eq_algebraicSet]
    exact algebraicSet_isAlgebraicSubset k _
  ·
    intro P hP
    exact hP.1









end SingularLocus

open IsLocalRing Module

section Corollary_17_14

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]
variable [IsScalarTower k R k]

theorem cotangent_finrank_eq_derivation_finrank
    (e : Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k) :
    finrank k (CotangentSpace R) = finrank k (Derivation k R k) := by
  have h1 : finrank k (Dual k (CotangentSpace R)) = finrank k (CotangentSpace R) :=
    Subspace.dual_finrank_eq
  have h2 : finrank k (Dual k (CotangentSpace R)) = finrank k (Derivation k R k) :=
    LinearEquiv.finrank_eq e
  linarith


end Corollary_17_14


def IsSmoothPoint (k : Type*) [Field k] (n m d : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) : Prop :=
  P ∈ AlgebraicSet k n (Set.range f) ∧
    Module.finrank (AlgebraicClosure k)
      (TangentSpaces.tangentSpace (TangentSpaces.jacobianMatrix n m f P)) = d


