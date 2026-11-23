/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic

open Polynomial AlgebraicGeometry

noncomputable section

namespace BlowupAtPoint

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The `n`-th graded piece of the Rees algebra `R[It] = ⨁ Iⁿ tⁿ`: monomials `a · tⁿ` with
`a ∈ Iⁿ`, packaged as an additive subgroup of the Rees algebra. -/
def reesGrading (n : ℕ) : AddSubgroup (reesAlgebra I) where
  carrier := {f | ∃ a ∈ I ^ n, (f : R[X]) = monomial n a}
  add_mem' := by
    rintro ⟨fa, hfa⟩ ⟨fb, hfb⟩ ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    exact ⟨a + b, (I ^ n).add_mem ha hb, by
      show (⟨fa, hfa⟩ : reesAlgebra I).val + (⟨fb, hfb⟩ : reesAlgebra I).val = _
      rw [ha', hb']; simp [map_add]⟩
  zero_mem' := ⟨0, (I ^ n).zero_mem, by simp⟩
  neg_mem' := by
    rintro ⟨fv, hfv⟩ ⟨a, ha, ha'⟩
    exact ⟨-a, (I ^ n).neg_mem_iff.mpr ha, by
      show -(⟨fv, hfv⟩ : reesAlgebra I).val = _
      rw [ha']; simp [map_neg]⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- Each graded piece `reesGrading I n` carries the inherited `AddCommMonoid` structure. -/
instance reesGrading_addCommMonoid (n : ℕ) : AddCommMonoid ↥(reesGrading I n) := inferInstance

/-- The component of `f ∈ R[It]` in the `n`-th graded piece, namely the monomial
`f.coeff n · tⁿ`. -/
def reesDecomposeComponent (f : reesAlgebra I) (n : ℕ) :
    ↥(reesGrading I n) := by
  refine ⟨⟨monomial n (f.val.coeff n), ?_⟩, ?_⟩
  · exact reesAlgebra.monomial_mem.mpr (((mem_reesAlgebra_iff I f.val).mp f.property) n)
  · exact ⟨f.val.coeff n, ((mem_reesAlgebra_iff I f.val).mp f.property) n, rfl⟩

/-- The underlying polynomial of `reesDecomposeComponent I f n` is the monomial of degree `n`
with coefficient `f.coeff n`. -/
lemma reesDecomposeComponent_coe_coe (f : reesAlgebra I) (n : ℕ) :
    ((reesDecomposeComponent I f n : ↥(reesAlgebra I)) : R[X]) =
    monomial n (f.val.coeff n) := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- The `n`-th coefficient of the polynomial assembled from a direct-sum element coincides with
the `n`-th coefficient of the component in degree `n`. -/
lemma coeff_coeAddMonoidHom
    (x : DirectSum ℕ (fun n => ↥(reesGrading I n))) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (reesGrading I) x).val : R[X]).coeff n =
    ((x n).val : R[X]).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i xi =>
    simp only [DirectSum.coeAddMonoidHom_of]
    by_cases hin : i = n
    · subst hin; simp [DirectSum.of_eq_same]
    · have h1 := DirectSum.of_eq_of_ne
        (β := fun n => ↥(reesGrading I n)) i n xi (Ne.symm hin)
      rw [h1]; simp only [ZeroMemClass.coe_zero, coeff_zero]
      obtain ⟨a, ha, hxi⟩ := xi.property
      rw [hxi, coeff_monomial, if_neg hin]
  | add x y hx hy =>
    rw [map_add]
    have lhs_eq : ((DirectSum.coeAddMonoidHom (reesGrading I) x +
      DirectSum.coeAddMonoidHom (reesGrading I) y).val : R[X]) =
      (DirectSum.coeAddMonoidHom (reesGrading I) x).val +
      (DirectSum.coeAddMonoidHom (reesGrading I) y).val := rfl
    rw [lhs_eq, coeff_add, hx, hy]
    have rhs_eq : (((x + y) n).val : R[X]) =
      ((x n).val : R[X]) + ((y n).val : R[X]) := rfl
    rw [rhs_eq, coeff_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- The graded pieces `reesGrading I n` give an internal direct sum decomposition of the Rees
algebra. -/
lemma reesGrading_isInternal : DirectSum.IsInternal (reesGrading I) := by
  constructor
  · intro x y hxy
    ext n
    rename_i m
    obtain ⟨ax, hax, hxn⟩ := (x n).property
    obtain ⟨ay, hay, hyn⟩ := (y n).property
    rw [hxn, hyn, coeff_monomial, coeff_monomial]
    split_ifs with h
    · have hc := congr_arg (fun f => (f.val : R[X]).coeff n) hxy
      dsimp at hc
      rw [coeff_coeAddMonoidHom I x n, coeff_coeAddMonoidHom I y n] at hc
      simp only [hxn, hyn, coeff_monomial] at hc
      exact hc
    · rfl
  · intro f
    use f.val.support.sum (fun n =>
      DirectSum.of (fun n => ↥(reesGrading I n)) n
        (reesDecomposeComponent I f n))
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, reesDecomposeComponent_coe_coe]
    exact (as_sum_support f.val).symm

/-- The multiplicative identity of the Rees algebra lies in the degree-zero piece. -/
theorem reesGrading_one_mem : (1 : reesAlgebra I) ∈ reesGrading I 0 := by
  refine ⟨1, ?_, ?_⟩
  · simp [Ideal.one_eq_top]
  · show (1 : reesAlgebra I).val = monomial 0 1
    simp

/-- Multiplication of homogeneous elements of degrees `i` and `j` lands in degree `i + j`. -/
theorem reesGrading_mul_mem {i j : ℕ} {fi fj : reesAlgebra I}
    (hi : fi ∈ reesGrading I i) (hj : fj ∈ reesGrading I j) :
    fi * fj ∈ reesGrading I (i + j) := by
  obtain ⟨a, ha, ha'⟩ := hi
  obtain ⟨b, hb, hb'⟩ := hj
  refine ⟨a * b, ?_, ?_⟩
  · rw [pow_add]; exact Ideal.mul_mem_mul ha hb
  · show (fi * fj : reesAlgebra I).val = monomial (i + j) (a * b)
    change fi.val * fj.val = _
    rw [ha', hb', monomial_mul_monomial]

set_option synthInstance.maxHeartbeats 400000 in
/-- The Rees algebra together with `reesGrading` is a graded ring. -/
instance reesGradedRing : GradedRing (reesGrading I) :=
  { (reesGrading_isInternal I).chooseDecomposition with
    one_mem := reesGrading_one_mem I
    mul_mem := fun {_i} {_j} {_fi} {_fj} hi hj => reesGrading_mul_mem I hi hj }

/-- The blow-up scheme of `Spec R` along the ideal `I`, defined as `Proj` of the Rees algebra. -/
def blowupScheme : Scheme :=
  Proj (reesGrading I)

/-- The natural projection from the blow-up to `Spec` of the degree-zero piece (canonically
identified with `Spec R`). -/
def blowupProjection :
    blowupScheme I ⟶ Spec (.of ↥(reesGrading I 0)) :=
  Proj.toSpecZero (reesGrading I)

/-- Proper transform of a closed subscheme `Z` along a morphism `π : X ⟶ Y`, removing the
center `C`: take the closure of the preimage of `Z \ C` in `X`. -/
def properTransform {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  TopologicalSpace.Closeds.closure (π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)))

/-- Exceptional locus of a morphism `π : X ⟶ Y` over a closed subscheme `C ⊂ Y`: the preimage
of `C` in `X`. -/
def exceptionalLocus {X Y : Scheme} (π : X ⟶ Y)
    (C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  ⟨π.base ⁻¹' (C : Set Y.toTopCat), C.isClosed'.preimage π.base.hom'.continuous⟩

/-- The blow-up of the closed subscheme `Z ⊂ Spec R` at the center `C`: the proper transform
along the blow-up projection. -/
def blowupAtPoint
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupScheme I).toTopCat :=
  properTransform (blowupProjection I) Z C

/-- The exceptional locus of the blow-up of `Z` at the center `C`: the intersection of the
proper transform with the preimage of `C`. -/
def blowupExceptionalLocus
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupScheme I).toTopCat :=
  ⟨(blowupAtPoint I Z C : Set _) ∩ (exceptionalLocus (blowupProjection I) C : Set _),
   IsClosed.inter (blowupAtPoint I Z C).isClosed'
     (exceptionalLocus (blowupProjection I) C).isClosed'⟩

/-- The proper transform contains the preimage of the open part `Z \ C`. -/
theorem properTransform_contains_preimage_away {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)) ⊆
      (properTransform π Z C : Set X.toTopCat) :=
  subset_closure

/-- A monomial `a · Xⁿ` lies in the Rees algebra iff `a ∈ Iⁿ`. -/
theorem reesAlgebra_monomial_mem {n : ℕ} {a : R} :
    monomial n a ∈ reesAlgebra I ↔ a ∈ I ^ n :=
  reesAlgebra.monomial_mem

/-- Characterisation of membership in the Rees algebra: a polynomial `f` belongs to `R[It]` iff
`f.coeff i ∈ Iⁱ` for every `i`. -/
theorem mem_reesAlgebra_char (f : R[X]) :
    f ∈ reesAlgebra I ↔ ∀ i, f.coeff i ∈ I ^ i :=
  mem_reesAlgebra_iff I f

end BlowupAtPoint
