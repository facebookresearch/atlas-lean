/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section33
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection

open Matrix

namespace SymmetricBilinearForms

/-- Two square matrices `M`, `N` over a commutative ring are *congruent* if
there exists an invertible matrix `A` such that `A * M * Aᵀ = N`. This is the
matrix-level equivalence relation underlying isometry of bilinear forms. -/
def MatrixCongruent {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M N : Matrix n n R) : Prop :=
  ∃ A : Matrix n n R, IsUnit A.det ∧ A * M * Aᵀ = N

/-- The matrix `H ⊕ ⟨1⟩` over `F₂`, formed by the hyperbolic plane and a
rank-one form with diagonal entry `1`. This is the model form used in
Claim 30.7. -/
def hyperbolicPlusIdentity : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Claim 30.7: the form `H ⊕ ⟨1⟩` is congruent over `F₂` to the identity
form `⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨1⟩`. -/
theorem hyperbolicPlusIdentity_matrixCongruent_one :
    MatrixCongruent hyperbolicPlusIdentity (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  refine ⟨!![1, 1, 1; 1, 0, 1; 0, 1, 1], ?_, ?_⟩
  ·
    decide
  ·
    decide

end SymmetricBilinearForms

namespace AlgebraicTopologyI

/-- Definition 30.1: a *topological manifold* is a Hausdorff space that is
locally homeomorphic to some Euclidean space at every point (the dimension
may a priori depend on the point). -/
class IsTopologicalManifold (M : Type*) [TopologicalSpace M] : Prop where
  hausdorff : T2Space M
  locally_euclidean : ∀ x : M, ∃ n : ℕ, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))

/-- A *topological `n`-manifold*: a Hausdorff space equipped with a charted
space structure modelled on `ℝⁿ`. This is the dimension-fixed variant of
`IsTopologicalManifold`. -/
class TopologicalManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    extends ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  [hausdorff : T2Space M]

attribute [instance] TopologicalManifold.hausdorff

/-- A Hausdorff charted space modelled on `ℝⁿ` automatically gets the
`TopologicalManifold n` instance. -/
instance (priority := 100) instTopologicalManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] :
    TopologicalManifold n M where
  hausdorff := inferInstance

end AlgebraicTopologyI

section PoincareDuality

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology

/-- Singular cohomology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev SingularCohomology.CohomZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularCohomology (ZMod 2) X (ModuleCat.of (ZMod 2) (ZMod 2)) n : Type)

/-- Singular homology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev HomolZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularHomologyModule (ZMod 2) X n : Type)





end PoincareDuality

noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

/-- A *compact surface*: a compact, connected, Hausdorff topological space
with a charted-space structure on `ℝ²` that makes it a `C⁰` manifold. This
is the geometric setting for the classification of surfaces. -/
structure CompactSurface where
  toTopCat : TopCat.{0}
  compact : CompactSpace toTopCat
  connected : ConnectedSpace toTopCat
  t2 : T2Space toTopCat
  charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) toTopCat
  isManifold : letI := charted;
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 toTopCat

/-- Coerce a `CompactSurface` to its underlying `TopCat` object. -/
instance : CoeSort CompactSurface TopCat.{0} := ⟨CompactSurface.toTopCat⟩

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

/-- Make the `C⁰`-manifold structure of a `CompactSurface` available
automatically through typeclass inference. -/
instance (S : CompactSurface) :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 S.toTopCat :=
  S.isManifold
















/-- The orthogonal direct sum `B₁ ⊥ B₂` of two `F₂`-bilinear forms on the
product space `V₁ × V₂`, defined by `((x₁, x₂), (y₁, y₂)) ↦ B₁(x₁, y₁) + B₂(x₂, y₂)`. -/
def orthogonalDirectSumForm
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (B₁ : LinearMap.BilinForm (ZMod 2) V₁)
    (B₂ : LinearMap.BilinForm (ZMod 2) V₂) :
    LinearMap.BilinForm (ZMod 2) (V₁ × V₂) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => B₁ x.1 y.1 + B₂ x.2 y.2)
    (fun x₁ x₂ y => by
      simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Prod.smul_fst,
        Prod.smul_snd]; ring)
    (fun x y₁ y₂ => by
      simp only [map_add, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]; ring)

/-- The *punctured surface* `S ∖ B`: remove a small open disk from `S`
using a chart centred at an arbitrary point. -/
def puncturedSurface (S : CompactSurface) : TopCat.{0} :=
  let x : S.toTopCat := Classical.arbitrary _
  let φ := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let U : Set S.toTopCat := φ.source ∩ ⇑φ ⁻¹' Metric.ball (φ x) 1
  TopCat.of ↥Uᶜ

/-- The continuous inclusion `S ∖ B ↪ S` of the punctured surface into
the original surface. -/
def puncturedSurfaceInclusion (S : CompactSurface) :
    puncturedSurface S ⟶ S.toTopCat :=
  ⟨Subtype.val, continuous_subtype_val⟩














/-- The Mayer–Vietoris restriction map in degree zero, which on
`F₂ × F₂ → F₂` simply adds the two components. -/
def connectedSum_mv_restrictionMap₀ (_S₁ _S₂ : CompactSurface) :
    ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun p => p.1 + p.2
    map_add' := fun x y => by
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    map_smul' := fun r x => by
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
      ring }



/-- The degree-zero restriction map `F₂ × F₂ → F₂` (addition) is
surjective. -/
theorem connectedSum_mv_restrictionMap₀_surjective (S₁ S₂ : CompactSurface) :
    Function.Surjective (connectedSum_mv_restrictionMap₀ S₁ S₂) := by
  intro x
  exact ⟨(x, 0), by simp [connectedSum_mv_restrictionMap₀]⟩























/-- Two compact surfaces are *homeomorphic* if there exists a homeomorphism
between their underlying topological spaces. -/
def CompactSurface.Homeomorphic (S₁ S₂ : CompactSurface) : Prop :=
  Nonempty (S₁.toTopCat ≃ₜ S₂.toTopCat)

/-- The set of *homeomorphism classes* of compact surfaces, as a quotient
of `CompactSurface` by the homeomorphism relation. -/
def SurfaceClass : Type 1 := Quot CompactSurface.Homeomorphic

/-- The canonical map sending a compact surface to its homeomorphism class. -/
def SurfaceClass.mk : CompactSurface → SurfaceClass := Quot.mk _



/-- A *nondegenerate symmetric bilinear form over `F₂`* packaged with its
underlying finite-dimensional `F₂`-vector space. -/
structure NondegenSymmBilinFormF2 where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod 2) V]
  [instFiniteDimensional : FiniteDimensional (ZMod 2) V]
  form : @LinearMap.BilinForm (ZMod 2) _ V instAddCommGroup.toAddCommMonoid instModule
  isSymm : form.IsSymm
  isNondeg : form.Nondegenerate

attribute [instance] NondegenSymmBilinFormF2.instAddCommGroup
  NondegenSymmBilinFormF2.instModule NondegenSymmBilinFormF2.instFiniteDimensional

/-- Two nondegenerate symmetric bilinear forms over `F₂` are *isometric* if
there is a linear isomorphism of the underlying vector spaces that takes
one form to the other. -/
def NondegenSymmBilinFormF2.Isometric (B₁ B₂ : NondegenSymmBilinFormF2) : Prop :=
  ∃ (f : B₁.V ≃ₗ[ZMod 2] B₂.V),
    ∀ (x y : B₁.V), B₂.form (f x) (f y) = B₁.form x y

/-- The set of *isometry classes* of nondegenerate symmetric bilinear forms
over `F₂`. -/
def BilinFormClass : Type 1 := Quot NondegenSymmBilinFormF2.Isometric



/-- The canonical map sending a nondegenerate symmetric `F₂`-bilinear form
to its isometry class. -/
def BilinFormClass.mk : NondegenSymmBilinFormF2 → BilinFormClass := Quot.mk _















end SurfacesAndBilinearForms

section

open LinearMap.BilinForm

namespace BilinearForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For a reflexive bilinear form `B`, the restriction `B|_W` is
nondegenerate iff `W` and its orthogonal complement intersect only at zero. -/
theorem restrict_nondegenerate_iff_disjoint_orthogonal
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    (W : Submodule K V) :
    (B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W) := by
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
      isCompl_orthogonal_iff_disjoint hB_refl]

/-- If `B` is nondegenerate and reflexive and `B|_W` is nondegenerate, then
the restriction of `B` to the orthogonal complement `W^⊥` is also
nondegenerate. -/
theorem restrict_orthogonal_nondegenerate
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) :
    (B.restrict (B.orthogonal W)).Nondegenerate := by
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
      orthogonal_orthogonal hB hB_refl W]
  exact (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW).symm

/-- When `B|_W` is nondegenerate, `V` decomposes as the internal direct
sum `W ⊕ W^⊥`, giving a linear equivalence `W × W^⊥ ≃ₗ V`. -/
noncomputable def orthogonalProdEquiv
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) :
    (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl W (B.orthogonal W)
    (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW)

/-- Under the direct-sum decomposition `V ≃ W × W^⊥`, the form `B` becomes
the orthogonal direct sum of `B|_W` and `B|_{W^⊥}`; the cross terms vanish
because they lie in the orthogonal complement. -/
theorem orthogonalProdEquiv_respects_form
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate)
    (x y : ↥W × ↥(B.orthogonal W)) :
    B (orthogonalProdEquiv B hB_refl hW x)
      (orthogonalProdEquiv B hB_refl hW y) =
    B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2) := by
  simp only [orthogonalProdEquiv, Submodule.coe_prodEquivOfIsCompl',
    map_add, LinearMap.add_apply]
  have h1 : B (↑x.1) (↑y.2) = 0 := (y.2).2 x.1 (x.1).2
  have h2 : B (↑x.2) (↑y.1) = 0 := hB_refl _ _ ((x.2).2 y.1 (y.1).2)
  simp [h1, h2]

/-- Lemma 30.5 (packaged form): a triple characterisation of nondegeneracy
of the restriction `B|_W` of a nondegenerate reflexive bilinear form,
combining the disjointness criterion, the nondegeneracy of the restriction
to the orthogonal complement, and the orthogonal-direct-sum decomposition
of `V` together with the corresponding factorisation of `B`. -/
theorem restrict_nondegenerate_characterization
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hB_refl : B.IsRefl)
    (W : Submodule K V) :
    ((B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W)) ∧
    ((B.restrict W).Nondegenerate →
      (B.restrict (B.orthogonal W)).Nondegenerate) ∧
    ((B.restrict W).Nondegenerate →
      ∃ (e : (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V),
        ∀ (x y : ↥W × ↥(B.orthogonal W)),
          B (e x) (e y) = B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2)) :=
  ⟨restrict_nondegenerate_iff_disjoint_orthogonal B hB_refl W,
   fun hW => restrict_orthogonal_nondegenerate B hB hB_refl hW,
   fun hW => ⟨orthogonalProdEquiv B hB_refl hW,
              orthogonalProdEquiv_respects_form B hB_refl hW⟩⟩

end BilinearForm

end
