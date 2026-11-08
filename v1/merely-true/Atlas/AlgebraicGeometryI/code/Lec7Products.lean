/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Lec7Products

section Goal62

/-- Helper: the tensor product of two surjective algebra homomorphisms
is surjective (used for products of closed immersions). -/
theorem tensor_product_map_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f : A →ₐ[S] B) (g : C →ₐ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (Algebra.TensorProduct.map f g) :=
  Algebra.TensorProduct.map_surjective f g hf hg

/-- Product of a closed immersion with the identity on the right is a
closed immersion (Lec 7, used for Prop 8). -/
noncomputable instance isClosedImmersion_prod_map_id_right
    {X₁ Y₁ Z : Scheme} (f : X₁ ⟶ Y₁) [IsClosedImmersion f] :
    IsClosedImmersion (Limits.prod.map f (𝟙 Z)) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_prod_fst_with_id f Z) ‹_›

/-- Product of the identity on the left with a closed immersion is a
closed immersion (Lec 7, used for Prop 8). -/
noncomputable instance isClosedImmersion_prod_map_id_left
    {X₂ Y₂ Z : Scheme} (g : X₂ ⟶ Y₂) [IsClosedImmersion g] :
    IsClosedImmersion (Limits.prod.map (𝟙 Z) g) := by
  have h_eq : Limits.prod.map (𝟙 Z) g =
    (Limits.prod.braiding Z X₂).hom ≫ Limits.prod.map g (𝟙 Z) ≫
    (Limits.prod.braiding Y₂ Z).hom := by
    apply prod.hom_ext
    all_goals simp [prod.braiding_hom, prod.lift_fst, prod.lift_snd, prod.map_fst,
      prod.map_snd, ← Category.assoc]
  rw [h_eq]
  have : IsClosedImmersion (Limits.prod.map g (𝟙 Z)) :=
    isClosedImmersion_prod_map_id_right g
  exact IsClosedImmersion.comp _ _

/-- The product of two closed immersions is a closed immersion
(Lec 7, Lem 16 / used in Prop 8). -/
theorem isClosedImmersion_prod_map
    {X₁ X₂ Y₁ Y₂ : Scheme} (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] :
    IsClosedImmersion (Limits.prod.map i₁ i₂) := by
  have h_eq : Limits.prod.map i₁ i₂ =
    Limits.prod.map i₁ (𝟙 X₂) ≫ Limits.prod.map (𝟙 Y₁) i₂ := by
    simp [Limits.prod.map_map]
  rw [h_eq]
  exact IsClosedImmersion.comp _ _

end Goal62

section Goal63

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` of a graded ring (Lec 7, Prop 8 setting). -/
class Scheme.IsProjective (X : Scheme) : Prop where
  exists_closedImmersion_into_proj :
    ∃ (A : Type) (σ : Type) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (f : X ⟶ Proj 𝒜), IsClosedImmersion f

/-- `Proj 𝒜` is projective via the identity closed immersion. -/
noncomputable instance proj_isProjective
    {A : Type} {σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Scheme.IsProjective (Proj 𝒜) where
  exists_closedImmersion_into_proj :=
    ⟨A, σ, inferInstance, inferInstance, inferInstance, 𝒜, inferInstance,
     𝟙 (Proj 𝒜), inferInstance⟩

/-- A closed subscheme of a projective scheme is projective. -/
theorem isProjective_of_closedImmersion {X Y : Scheme}
    (f : X ⟶ Y) [IsClosedImmersion f] [Scheme.IsProjective Y] :
    Scheme.IsProjective X where
  exists_closedImmersion_into_proj := by
    obtain ⟨A, σ, hcr, hsl, hasg, 𝒜, hgr, g, hg⟩ :=
      Scheme.IsProjective.exists_closedImmersion_into_proj (X := Y)
    exact ⟨A, σ, hcr, hsl, hasg, 𝒜, hgr, f ≫ g, IsClosedImmersion.comp f g⟩

/-- The Segre algebra homomorphism sending `X_{(i,j)} ↦ X_i ⊗ X_j`,
underlying the Segre embedding for Lec 7, Prop 8. -/
noncomputable def segreAlgHom (R : Type*) [CommRing R] (n m : ℕ) :
    MvPolynomial (Fin n × Fin m) R →ₐ[R]
    MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin m) R :=
  MvPolynomial.aeval (fun p =>
    MvPolynomial.X p.1 ⊗ₜ[R] MvPolynomial.X p.2)

/-- The Segre map sends the generator `X_{(i,j)}` to `X_i ⊗ X_j`. -/
theorem segreAlgHom_X (R : Type*) [CommRing R] (n m : ℕ) (i : Fin n) (j : Fin m) :
    segreAlgHom R n m (MvPolynomial.X (i, j)) =
    MvPolynomial.X i ⊗ₜ[R] MvPolynomial.X j := by
  simp [segreAlgHom, MvPolynomial.aeval_X]

/-- The defining Segre relations
`X_{(i,j)} X_{(k,l)} - X_{(k,j)} X_{(i,l)}` lie in the kernel of the
Segre map. -/
theorem segreAlgHom_relation (R : Type*) [CommRing R] (n m : ℕ)
    (i k : Fin n) (j l : Fin m) :
    segreAlgHom R n m
      (MvPolynomial.X (i, j) * MvPolynomial.X (k, l) -
       MvPolynomial.X (k, j) * MvPolynomial.X (i, l)) = 0 := by
  simp only [map_sub, map_mul, segreAlgHom_X]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  ring_nf

/-- The Segre relations are homogeneous of degree 2 in the standard
grading on `R[X_{(i,j)}]`. -/
theorem segreRelation_isHomogeneous (R : Type*) [CommRing R] (n m : ℕ)
    (i k : Fin n) (j l : Fin m) :
    letI := @MvPolynomial.gradedAlgebra (Fin n × Fin m) R _
    (MvPolynomial.X (i, j) * MvPolynomial.X (k, l) -
     MvPolynomial.X (k, j) * MvPolynomial.X (i, l) :
     MvPolynomial (Fin n × Fin m) R).IsHomogeneous 2 := by
  letI := @MvPolynomial.gradedAlgebra (Fin n × Fin m) R _
  apply MvPolynomial.IsHomogeneous.sub
  · exact (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
  · exact (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)


end Goal63

section Goal68

/-- The graph morphism `Γ_f : X ⟶ X × Y` of `f : X ⟶ Y`
(Lec 7, Def 18). -/
noncomputable def graphMorphism {X Y : Scheme} (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  Limits.prod.lift (𝟙 X) f

/-- The first projection of the graph morphism is the identity on `X`. -/
theorem graphMorphism_fst {X Y : Scheme} (f : X ⟶ Y) :
    graphMorphism f ≫ Limits.prod.fst = 𝟙 X := by
  simp [graphMorphism, prod.lift_fst]

/-- The second projection of the graph morphism recovers `f`. -/
theorem graphMorphism_snd {X Y : Scheme} (f : X ⟶ Y) :
    graphMorphism f ≫ Limits.prod.snd = f := by
  simp [graphMorphism, prod.lift_snd]

/-- The graph morphism of `𝟙 X` is the diagonal `X ⟶ X × X`. -/
theorem graphMorphism_id (X : Scheme) :
    graphMorphism (𝟙 X) = Limits.prod.lift (𝟙 X) (𝟙 X) := by
  rfl

end Goal68

end Lec7Products
