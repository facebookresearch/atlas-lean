/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Atlas.GeometryOfManifolds.code.ConnectionsCurvature
import Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Orientation

set_option autoImplicit false

open SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The intertwiner $T = \tfrac{1}{2}(\mathrm{id} - J_1 J_0)$ between two complex structures
$J_0, J_1$ on $V$, satisfying $T \circ J_0 = J_1 \circ T$. -/
noncomputable def complexStrIntertwiner (J₀ J₁ : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1/2 : ℝ) • (LinearMap.id - J₁.comp J₀)

/-- The intertwiner $T = \tfrac{1}{2}(\mathrm{id} - J_1 J_0)$ commutes the complex structures:
$T \circ J_0 = J_1 \circ T$. -/
theorem complexStr_intertwiner_commutes
    (J₀ J₁ : V →ₗ[ℝ] V)
    (hJ₀ : IsComplexStructure J₀)
    (hJ₁ : IsComplexStructure J₁) :
    (complexStrIntertwiner J₀ J₁).comp J₀ = J₁.comp (complexStrIntertwiner J₀ J₁) := by
  ext v
  simp only [complexStrIntertwiner, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_smul]
  congr 1
  have hJ₀v : J₀ (J₀ v) = -v := hJ₀.apply_apply v
  have hJ₁J₀v : J₁ (J₁ (J₀ v)) = -(J₀ v) := hJ₁.apply_apply (J₀ v)
  rw [hJ₀v, map_neg, map_sub, hJ₁J₀v]
  abel

section TensorAdditivity

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
variable {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H₀ M]


variable (Ω₂ : Type*) [AddCommGroup Ω₂] [Module ℝ Ω₂]

/-- A representative of the first Chern class $c_1(L) = \tfrac{1}{2\pi} R^\nabla$ obtained from a
curvature 2-form. -/
noncomputable def firstChernClassRepManifold (curvature : Ω₂) : Ω₂ :=
  (1 / (2 * Real.pi)) • curvature

/-- Additivity of $c_1$ under tensor products: $c_1(L \otimes L') = c_1(L) + c_1(L')$, expressed
on representatives as $\tfrac{1}{2\pi}(R + R') = \tfrac{1}{2\pi} R + \tfrac{1}{2\pi} R'$. -/
theorem firstChernClass_tensor_product_additivity
    (R_L R_L' : Ω₂) :
    firstChernClassRepManifold Ω₂ (R_L + R_L') =
      firstChernClassRepManifold Ω₂ R_L + firstChernClassRepManifold Ω₂ R_L' := by
  simp only [firstChernClassRepManifold]
  exact smul_add _ R_L R_L'

end TensorAdditivity

section TopChernEuler

variable {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
variable {HModel : Type*} [TopologicalSpace HModel]
variable {I : ModelWithCorners ℝ EModel HModel}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace HModel M] [IsManifold I ⊤ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {E : M → Type*} [TopologicalSpace (Bundle.TotalSpace F E)]
variable [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
variable [∀ x, TopologicalSpace (E x)]
variable [FiberBundle F E] [VectorBundle ℂ F E]
variable {Ω : ℕ → Type*} [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
variable {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
variable {d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0}
variable {r : ℕ} {totalAlg : Type*} [CommRing totalAlg]

/-- Data certifying that the manifold $M$ is compact, oriented, of even real dimension $2 \dim$,
and carries a non-exact volume form. -/
structure IsCompactOriented
    {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
    {HModel : Type*} [TopologicalSpace HModel]
    (I : ModelWithCorners ℝ EModel HModel)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HModel M]
    [IsManifold I ⊤ M] [CompactSpace M]
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1)) where
  dim : ℕ
  dim_pos : 0 < dim
  orientation : Orientation ℝ EModel (Fin (2 * dim))
  vol : Ω (2 * dim - 1 + 1)
  vol_not_exact : ¬ (∃ β : Ω (2 * dim - 1), d β = vol)

/-- An abstract notion of integrality of de Rham cohomology classes: a predicate `isIntegral` on
forms closed under sums and negation, with $0$ integral and integral forms automatically closed. -/
structure IsIntegralCohomologyClass
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1)) where
  isIntegral : {k : ℕ} → Ω k → Prop
  integral_closed : ∀ {k : ℕ} (α : Ω k), isIntegral α → d α = 0
  integral_zero : ∀ (k : ℕ), isIntegral (0 : Ω k)
  integral_add : ∀ {k : ℕ} (α β : Ω k), isIntegral α → isIntegral β → isIntegral (α + β)
  integral_neg : ∀ {k : ℕ} (α : Ω k), isIntegral α → isIntegral (-α)

/-- Data packaging a complex vector bundle $E \to M$ of rank $r$ with a connection and curvature
matrix, plus the Chern–Weil machinery (`embed`, `extract`, `chernWeilParam`) producing the
top Chern form $c_r(E, \nabla)$ as an integral cohomology class. -/
structure ComplexVectorBundleData
    {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
    {HModel : Type*} [TopologicalSpace HModel]
    (I : ModelWithCorners ℝ EModel HModel)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HModel M] [IsManifold I ⊤ M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (E : M → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℂ F E]
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1))
    (d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0)
    (intCoh : IsIntegralCohomologyClass Ω d)
    (r : ℕ) (totalAlg : Type*) [CommRing totalAlg] where
  rank_pos : 0 < r
  connectionForm : Ω 1
  curvatureRep : Ω 2
  curvature_eq : d connectionForm = curvatureRep
  curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)
  curvatureMatrix_closed : ∀ i j, d (curvatureMatrix i j) = 0
  embed : Ω 2 → totalAlg
  extract : totalAlg → Ω (2 * r - 1 + 1)
  chernWeilParam : totalAlg
  embed_add : ∀ (a b : Ω 2), embed (a + b) = embed a + embed b
  extract_add : ∀ (a b : totalAlg), extract (a + b) = extract a + extract b
  extract_one : extract 1 = 0
  chernWeil_zero :
    extract (totalChernForm
      ((0 : Matrix (Fin r) (Fin r) (Ω 2)).map embed) chernWeilParam) = 0
  chernWeil_closed :
    ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)),
      (∀ i j, d (A i j) = 0) →
      d (extract (totalChernForm (A.map embed) chernWeilParam)) = 0
  chernWeil_smul :
    ∀ (c : ℝ) (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm ((c • A).map embed) chernWeilParam) =
      c ^ r • extract (totalChernForm (A.map embed) chernWeilParam)
  chernWeil_nontrivial :
    ∃ (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm (A.map embed) chernWeilParam) ≠ 0
  chernWeil_perm :
    ∀ (σ : Equiv.Perm (Fin r)) (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm ((A.submatrix σ σ).map embed) chernWeilParam) =
      extract (totalChernForm (A.map embed) chernWeilParam)
  chernWeil_alternating :
    ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)) (i j : Fin r),
      i ≠ j → (∀ k, A i k = A j k) →
      extract (totalChernForm (A.map embed) chernWeilParam) = 0
  topChernRep_integral :
    intCoh.isIntegral
      (extract (totalChernForm (curvatureMatrix.map embed) chernWeilParam))

/-- Data carrying a representative of the Euler class $e(E) \in H^{2r}(M, \mathbb{Z})$ via the
Pfaffian of the curvature matrix, together with the signed count of zeros of a generic section. -/
structure EulerClassData
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1))
    (intCoh : IsIntegralCohomologyClass Ω d)
    (r : ℕ)
    (curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)) where
  pfaffianMap : Matrix (Fin r) (Fin r) (Ω 2) → Ω (2 * r - 1 + 1)
  eulerRep : Ω (2 * r - 1 + 1)
  eulerRep_eq_pfaffian : eulerRep = pfaffianMap curvatureMatrix
  eulerRep_closed : d eulerRep = 0
  pfaffian_zero : pfaffianMap 0 = 0
  pfaffian_homogeneous : ∀ (c : ℝ) (A : Matrix (Fin r) (Fin r) (Ω 2)),
    pfaffianMap (c • A) = c ^ r • pfaffianMap A
  pfaffian_closed : ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)),
    (∀ i j, d (A i j) = 0) → d (pfaffianMap A) = 0
  eulerRep_integral : intCoh.isIntegral eulerRep
  sectionZeroCount : ℤ
  sectionZeroCount_spec :
    curvatureMatrix = 0 → sectionZeroCount = 0

/-- If the curvature matrix vanishes then the Euler representative vanishes:
$\mathrm{Pf}(0) = 0$. -/
theorem EulerClassData.eulerRep_trivial
    {Ω : ℕ → Type*} [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
    {intCoh : IsIntegralCohomologyClass Ω d}
    {r : ℕ} {curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)}
    (euler : EulerClassData Ω d intCoh r curvatureMatrix)
    (h : curvatureMatrix = 0) : euler.eulerRep = 0 := by
  subst h
  rw [euler.eulerRep_eq_pfaffian, euler.pfaffian_zero]

/-- The Chern–Weil map applied to a curvature-like matrix $A$, producing the corresponding
characteristic form via `embed` and `extract`. -/
def ComplexVectorBundleData.chernWeilMapDef
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg)
    (A : Matrix (Fin r) (Fin r) (Ω 2)) : Ω (2 * r - 1 + 1) :=
  bundle.extract (totalChernForm (A.map bundle.embed) bundle.chernWeilParam)

/-- The top Chern form representative $c_r(E, \nabla)$ obtained from the bundle's curvature
matrix via Chern–Weil. -/
def ComplexVectorBundleData.topChernRep
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg) :
    Ω (2 * r - 1 + 1) :=
  bundle.chernWeilMapDef bundle.curvatureMatrix

/-- The top Chern form $c_r(E, \nabla)$ is closed, $d c_r = 0$. -/
theorem ComplexVectorBundleData.topChernRep_closed
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg) :
    d bundle.topChernRep = 0 := by
  simp only [ComplexVectorBundleData.topChernRep, ComplexVectorBundleData.chernWeilMapDef]
  exact bundle.chernWeil_closed bundle.curvatureMatrix bundle.curvatureMatrix_closed

/-- The curvature 2-form $R^\nabla$ is closed: since $R = d \omega$ and $d^2 = 0$. -/
theorem ComplexVectorBundleData.curvature_closed
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg) :
    d bundle.curvatureRep = 0 := by
  rw [← bundle.curvature_eq]
  exact d_squared bundle.connectionForm




end TopChernEuler
