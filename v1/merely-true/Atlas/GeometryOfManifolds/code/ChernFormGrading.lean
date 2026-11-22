/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.ConnectionsCurvature

open Bundle NormedSpace Matrix Complex

/-- A $\mathbb{C}$-algebra $R$ realizing the graded algebra of complex differential forms:
each $\Omega^p$ embeds $\mathbb{R}$-linearly into a homogeneous component of degree $p$ in
$R$, with an inverse extraction map. -/
structure ComplexDifferentialFormAlgebra
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R] where
  embed : ∀ (p : ℕ), Ω p → R
  embed_linear : ∀ (p : ℕ), ∀ (a b : Ω p) (c : ℝ),
    embed p (c • a + b) = (algebraMap ℝ R c) * embed p a + embed p b
  embed_homog : ∀ (p : ℕ) (α : Ω p), IsGradedFormAlgebra.IsHomog (embed p α) p
  extract : ∀ (p : ℕ), R → Ω p
  extract_embed : ∀ (p : ℕ) (α : Ω p), extract p (embed p α) = α

/-- All geometric data needed to define the Chern forms of a rank-$r$ vector bundle
$V \to M$ with connection $\nabla$: the connection, its curvature $R^\nabla$ (antisymmetric
in tangent vectors), an embedding of the form algebra into a $\mathbb{C}$-algebra $R$, the
$r \times r$ curvature matrix realised in $R$ (with each entry homogeneous of degree $2$),
and a "degree-$0$ scalar" hypothesis on the leading Chern scalar. -/
structure ChernFormGeometricData

    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E_mod : Type*) [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E_mod H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]

    (r : ℕ)

    (Ω : ℕ → Type*) (VF : Type*) [DifferentialFormSpace Ω VF]

    (R : Type*) [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    where
  connection : CovariantDerivative I F V
  curvature : ∀ (x : M), TangentSpace I x → TangentSpace I x → (V x →L[𝕜] V x)
  curvature_antisymm : ∀ (x : M) (X Y : TangentSpace I x),
    curvature x X Y = -curvature x Y X
  formAlgebra : ComplexDifferentialFormAlgebra Ω VF R
  curvatureMatrix : Matrix (Fin r) (Fin r) R
  curvatureMatrix_deg2 : CurvatureMatrixDegreeTwo curvatureMatrix
  chernScalar_deg0 : ChernScalarHomogZero (R := R)

/-- The **total Chern form** of $(E, \nabla)$:
$$c(E, \nabla) = \det\!\left(I + \frac{i}{2\pi} R^\nabla\right) \in \Omega^\bullet(M, \mathbb{C}),$$
defined via the curvature matrix and the appropriate scalar normalization. -/
noncomputable def totalChernFormGeometric
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E_mod : Type*} [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E_mod H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ}
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (data : ChernFormGeometricData 𝕜 E_mod H I M F V r Ω VF R) : R :=
  totalChernFormWithScalar data.curvatureMatrix

/-- The **$j$-th Chern form** $c_j(E, \nabla) \in \Omega^{2j}(M, \mathbb{C})$, obtained as
the degree-$2j$ component of the total Chern form
$\det(I + \frac{i}{2\pi} R^\nabla) = \sum_j c_j$. -/
noncomputable def chernFormDegree
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E_mod : Type*} [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E_mod H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ}
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (data : ChernFormGeometricData 𝕜 E_mod H I M F V r Ω VF R)
    (j : ℕ) : R :=
  chernClassWithScalar data.curvatureMatrix j
