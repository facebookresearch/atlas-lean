/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

open Module Algebra Polynomial IntermediateField

section NormTraceDefinition

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem norm_eq_det_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : Basis ι A B) (b : B) :
    Algebra.norm A b = (Algebra.leftMulMatrix basis b).det :=
  Algebra.norm_eq_matrix_det basis b

theorem trace_eq_trace_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : Basis ι A B) (b : B) :
    Algebra.trace A B b = (Algebra.leftMulMatrix basis b).trace :=
  Algebra.trace_eq_matrix_trace basis b

end NormTraceDefinition

section NormTraceBaseChange

open TensorProduct

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
variable {B : Type*} [CommRing B] [Algebra A B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma leftMulMatrix_baseChange (bB : Basis ι A B) (b : B) :
    @Algebra.leftMulMatrix A' (A' ⊗[A] B) _ _
      (Algebra.TensorProduct.leftAlgebra) ι _ _
      (bB.baseChange A')
      (Algebra.TensorProduct.includeRight b) =
    (algebraMap A A').mapMatrix (Algebra.leftMulMatrix bB b) := by
  ext i j
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, Basis.baseChange_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', TensorProduct.tmul_mul_tmul, mul_one,
    Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one, mul_one]

theorem norm_baseChange (bB : Basis ι A B) (b : B) :
    algebraMap A A' (Algebra.norm A b) =
    @Algebra.norm A' (A' ⊗[A] B) _ _
      (Algebra.TensorProduct.leftAlgebra)
      (Algebra.TensorProduct.includeRight b) := by
  rw [Algebra.norm_eq_matrix_det bB,
    @Algebra.norm_eq_matrix_det A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) ι _ _
      (bB.baseChange A'),
    leftMulMatrix_baseChange bB b, RingHom.map_det]

theorem trace_baseChange (bB : Basis ι A B) (b : B) :
    algebraMap A A' (Algebra.trace A B b) =
    @Algebra.trace A' (A' ⊗[A] B) _ _
      (Algebra.TensorProduct.leftAlgebra)
      (Algebra.TensorProduct.includeRight b) := by
  rw [Algebra.trace_eq_matrix_trace bB,
    @Algebra.trace_eq_matrix_trace A' (A' ⊗[A] B) _ _ (Algebra.TensorProduct.leftAlgebra) ι _ _
      (bB.baseChange A'),
    leftMulMatrix_baseChange bB b]
  simp only [RingHom.mapMatrix_apply]
  exact AddMonoidHom.map_trace (algebraMap A A') _

theorem free_norm_trace_baseChange (bB : Basis ι A B) :

    Nonempty (Basis ι A' (A' ⊗[A] B)) ∧

    (∀ b : B, algebraMap A A' (Algebra.norm A b) =
      @Algebra.norm A' (A' ⊗[A] B) _ _
        (Algebra.TensorProduct.leftAlgebra)
        (Algebra.TensorProduct.includeRight b)) ∧

    (∀ b : B, algebraMap A A' (Algebra.trace A B b) =
      @Algebra.trace A' (A' ⊗[A] B) _ _
        (Algebra.TensorProduct.leftAlgebra)
        (Algebra.TensorProduct.includeRight b)) :=
  ⟨⟨bB.baseChange A'⟩, norm_baseChange bB, trace_baseChange bB⟩

end NormTraceBaseChange

section NormTraceEmbeddings

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (E : Type*) [Field E] [Algebra K E]

theorem norm_eq_prod_embeddings' [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsAlgClosed E] (x : L) :
    algebraMap K E (Algebra.norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
  Algebra.norm_eq_prod_embeddings K E x

theorem trace_eq_sum_embeddings' [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsAlgClosed E] (x : L) :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x :=
  trace_eq_sum_embeddings E

end NormTraceEmbeddings

noncomputable section

theorem norm_eq_prod_roots_pow {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : Type*) [Field F] [Algebra K F]
    {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.norm K x) =
      ((minpoly K x).aroots F).prod ^ Module.finrank K⟮x⟯ L :=
  Algebra.norm_eq_prod_roots F hF

theorem trace_eq_smul_sum_roots {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K L]
    {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.trace K L x) =
      Module.finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum :=
  trace_eq_sum_roots hF

theorem norm_eq_neg_one_pow_mul_coeff_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      (-1) ^ ((minpoly K x).natDegree * Module.finrank K⟮x⟯ L) *
        ((minpoly K x).coeff 0) ^ Module.finrank K⟮x⟯ L := by
  have hx : IsIntegral K x := .of_finite K x
  rw [Algebra.norm_eq_norm_adjoin K x]
  have key := PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen] at key
  rw [key, mul_pow, ← pow_mul]

theorem trace_eq_neg_finrank_mul_nextCoeff {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x =
      -(↑(Module.finrank K⟮x⟯ L) : K) * (minpoly K x).nextCoeff := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff]
  ring

section NormTraceIntegrality

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra A L] [IsScalarTower A K L]

omit [IsDomain A] [FiniteDimensional K L] in
theorem norm_mem_of_isIntegral {x : L} (hx : IsIntegral A x) :
    ∃ a : A, algebraMap A K a = Algebra.norm K x :=
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hx)

omit [IsDomain A] in
theorem trace_mem_of_isIntegral {x : L} (hx : IsIntegral A x) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L x :=
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hx)

end NormTraceIntegrality

section NormTraceTransitivity

theorem norm_tower {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] [Module.Free A B] [Module.Free B C]
    (x : C) :
    Algebra.norm A (Algebra.norm B x) = Algebra.norm A x :=
  Algebra.norm_norm

theorem trace_tower {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C]
    [Module.Free A B] [Module.Finite A B]
    [Module.Free B C] [Module.Finite B C]
    (x : C) :
    Algebra.trace A B (Algebra.trace B C x) = Algebra.trace A C x :=
  Algebra.trace_trace x

end NormTraceTransitivity

end
