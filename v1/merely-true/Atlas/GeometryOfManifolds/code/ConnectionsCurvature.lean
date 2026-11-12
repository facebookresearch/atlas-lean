/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Atlas.GeometryOfManifolds.code.DifferentialForms

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

/-- Generating polynomial for Chern forms: $\det(I + t\,\Omega)$ where $\Omega$ is the
curvature matrix. -/
def ChernForm
    {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  (1 + t • curvMatrix).det


open DifferentialFormSpace

/-- A connection $\nabla: C^\infty(M, E) \to \Omega^1(M, E)$ on a vector bundle: an $\mathbb{R}$-linear
map satisfying the Leibniz rule $\nabla(f\sigma) = df \cdot \sigma + f \nabla \sigma$. -/
structure Connection (Sections FormsWithValues Functions : Type*)
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    (dfSmul : Functions → Sections → FormsWithValues) where
  nabla : Sections → FormsWithValues
  nabla_add : ∀ σ τ, nabla (σ + τ) = nabla σ + nabla τ
  nabla_smul_real : ∀ (c : ℝ) (σ : Sections), nabla (c • σ) = c • nabla σ
  leibniz : ∀ (f : Functions) (σ : Sections),
    nabla (f • σ) = dfSmul f σ + f • nabla σ

/-- The trivial zero connection on $\mathbb{R}$, serving as a base example. -/
noncomputable def Connection.trivial : Connection ℝ ℝ ℝ (fun _ _ => 0) where
  nabla := fun _ => 0
  nabla_add := by simp
  nabla_smul_real := by simp
  leibniz := by simp [smul_eq_mul]

/-- The space of connections is an affine space: adding an $\mathrm{End}(E)$-valued one-form $B$
to a connection $\nabla$ gives a new connection $\nabla + B$. -/
def Connection.add
    {Sections FormsWithValues Functions : Type*}
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    {dfSmul : Functions → Sections → FormsWithValues}
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (B : Sections → FormsWithValues)
    (B_add : ∀ σ τ, B (σ + τ) = B σ + B τ)
    (B_smul_real : ∀ (c : ℝ) (σ : Sections), B (c • σ) = c • B σ)
    (B_linear : ∀ (f : Functions) (σ : Sections), B (f • σ) = f • B σ) :
    Connection Sections FormsWithValues Functions dfSmul where
  nabla := fun σ => conn.nabla σ + B σ
  nabla_add := by intro σ τ; rw [conn.nabla_add, B_add]; abel
  nabla_smul_real := by intro c σ; rw [conn.nabla_smul_real, B_smul_real, smul_add]
  leibniz := by
    intro f σ
    simp only [conn.leibniz, B_linear]
    rw [smul_add]
    abel

/-- The covariant derivative $\nabla_v \sigma$ of a section $\sigma$ along a vector field $v$,
obtained by evaluating $\nabla\sigma \in \Omega^1(M, E)$ on $v$. -/
def Connection.covariantDeriv
    {Sections FormsWithValues Functions VectorFields : Type*}
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    {dfSmul : Functions → Sections → FormsWithValues}
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (eval : VectorFields → FormsWithValues → Sections)
    (v : VectorFields) (σ : Sections) : Sections :=
  eval v (conn.nabla σ)

section MetricCompatibility

variable {Sections FormsWithValues Functions OneForm : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
  [Ring Functions] [AddCommGroup OneForm]
  [Module Functions Sections] [Module Functions FormsWithValues]
  {dfSmul : Functions → Sections → FormsWithValues}

/-- A connection $\nabla$ is metric-compatible with a metric $\langle\cdot,\cdot\rangle$ iff
$d\langle \sigma, \sigma'\rangle = \langle \nabla\sigma, \sigma'\rangle + \langle \sigma, \nabla\sigma'\rangle$. -/
def MetricCompatible
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (metric : Sections → Sections → Functions)
    (dFunctions : Functions → OneForm)
    (pairNablaLeft : FormsWithValues → Sections → OneForm)
    (pairNablaRight : Sections → FormsWithValues → OneForm) : Prop :=
  ∀ σ σ',
    dFunctions (metric σ σ') =
      pairNablaLeft (conn.nabla σ) σ' + pairNablaRight σ (conn.nabla σ')

end MetricCompatibility

/-- A ring $R$ equipped with a differential $d$ satisfying $d \circ d = 0$, abstracting the
exterior derivative on matrix-valued forms. -/
class MatrixFormAlgebra (R : Type*) extends Ring R where
  d : R → R
  d_add : ∀ a b, d (a + b) = d a + d b
  d_zero : d 0 = 0
  d_squared : ∀ a, d (d a) = 0

/-- The curvature tensor $R^\nabla: \mathfrak{X}(M) \times \mathfrak{X}(M) \to \mathrm{End}(E)$,
which is antisymmetric in its two vector-field arguments. -/
structure CurvatureTensor
    (Sections VectorFields EndSections : Type*)
    [AddCommGroup Sections] [AddCommGroup EndSections] where
  R : VectorFields → VectorFields → EndSections
  antisymm : ∀ U V, R U V = -(R V U)

/-- Gauge transformation law for curvature (Proposition 2): under a change of frame $g$ with
$g \cdot A' = A \cdot g + dg$, the curvature transforms as
$dA' + A' \wedge A' = g^{-1}(dA + A \wedge A) g$. -/
theorem gauge_transformation_curvature
    {R : Type*} [Ring R]
    (d : R → R) (g g_inv A A' dg : R)

    (hg_left : g_inv * g = 1)
    (_hg_right : g * g_inv = 1)

    (h_gauge : g * A' = A * g + dg)

    (h_d_add : ∀ a b, d (a + b) = d a + d b)

    (h_leib_gA : d (g * A') = dg * A' + g * d A')

    (h_leib_Ag : d (A * g) = d A * g - A * dg)

    (h_dd_g : d dg = 0) :
    d A' + A' * A' = g_inv * (d A + A * A) * g := by

  have step1 : g * d A' = d A * g - A * dg - dg * A' := by
    have h1 : dg * A' + g * d A' = d A * g - A * dg := by
      have h2 : d (g * A') = d (A * g + dg) := by rw [h_gauge]
      rw [h_leib_gA] at h2
      rw [h_d_add, h_leib_Ag, h_dd_g, add_zero] at h2
      exact h2
    calc g * d A' = dg * A' + g * d A' - dg * A' := by noncomm_ring
      _ = (d A * g - A * dg) - dg * A' := by rw [h1]
      _ = d A * g - A * dg - dg * A' := by noncomm_ring

  have step2 : g * (d A' + A' * A') = (d A + A * A) * g := by
    calc g * (d A' + A' * A')
        = g * d A' + g * A' * A' := by rw [mul_add, mul_assoc]
      _ = (d A * g - A * dg - dg * A') + (A * g + dg) * A' := by rw [step1, h_gauge]
      _ = d A * g - A * dg + A * (g * A') := by noncomm_ring
      _ = d A * g - A * dg + A * (A * g + dg) := by rw [h_gauge]
      _ = (d A + A * A) * g := by noncomm_ring

  calc d A' + A' * A'
      = g_inv * (g * (d A' + A' * A')) := by
        rw [← mul_assoc, hg_left, one_mul]
    _ = g_inv * ((d A + A * A) * g) := by rw [step2]
    _ = g_inv * (d A + A * A) * g := by rw [mul_assoc]

/-- The Chern normalization constant $\frac{i}{2\pi}$ appearing in $c(E,\nabla) = \det(I + \frac{i}{2\pi} R^\nabla)$. -/
noncomputable def chernScalar : ℂ := Complex.I / (2 * ↑Real.pi)

/-- The total Chern form generating polynomial: $\det(I + t\,\Omega)$ for a curvature matrix $\Omega$. -/
def totalChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  (1 + t • curvMatrix).det

/-- Unfolding lemma: the total Chern form equals $\det(I + t\,\Omega)$ by definition. -/
@[simp]
theorem totalChernForm_def {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) :
    totalChernForm curvMatrix t = (1 + t • curvMatrix).det := rfl

/-- The total Chern form $c(E,\nabla) = \det(I + \frac{i}{2\pi} R^\nabla)$, using the standard
normalization constant $\frac{i}{2\pi}$. -/
noncomputable def totalChernFormWithScalar {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) : R :=
  totalChernForm curvMatrix (algebraMap ℂ R chernScalar)

/-- Definitional equality between `totalChernFormWithScalar` and `totalChernForm` evaluated at $\frac{i}{2\pi}$. -/
theorem totalChernFormWithScalar_eq_totalChernForm {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) :
    totalChernFormWithScalar curvMatrix = totalChernForm curvMatrix (algebraMap ℂ R chernScalar) :=
  rfl

/-- Bundle of data required to define Chern forms on a vector bundle of rank $r$: a connection,
its curvature 2-form (antisymmetric in $X, Y$), and the local curvature matrix in some frame. -/
structure VectorBundleChernData
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    (r : ℕ)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    where
  connection : CovariantDerivative I F V
  curvature : ∀ (x : M), TangentSpace I x → TangentSpace I x → (V x →L[𝕜] V x)
  curvatureMatrix : Matrix (Fin r) (Fin r) R
  curvature_antisymm : ∀ (x : M) (X Y : TangentSpace I x),
    curvature x X Y = -curvature x Y X

/-- The total Chern form of a connection, computed from its curvature matrix via the
$\frac{i}{2\pi}$-normalized $\det(I + \cdot)$ formula. -/
noncomputable def chernFormOfConnection
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (data : VectorBundleChernData 𝕜 E H I M F V r R) : R :=
  totalChernFormWithScalar data.curvatureMatrix

/-- For a line bundle (rank 1), the total Chern form reduces to $1 + \frac{i}{2\pi} R^\nabla$. -/
theorem totalChernFormWithScalar_rank_one {R : Type*} [CommRing R] [Algebra ℂ R]
    (curvMatrix : Matrix (Fin 1) (Fin 1) R) :
    totalChernFormWithScalar curvMatrix =
      1 + algebraMap ℂ R chernScalar * curvMatrix 0 0 := by
  simp only [totalChernFormWithScalar, totalChernForm, Matrix.det_fin_one, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul]

/-- A graded form algebra: a commutative ring with a notion of homogeneous degree-$p$ elements,
projection maps onto each degree, and the usual graded multiplication property. Used to encode
the bidegree structure of $\Omega^\bullet(M)$. -/
class IsGradedFormAlgebra (R : Type*) [CommRing R] where
  IsHomog : R → ℕ → Prop
  one_homog : IsHomog 1 0
  zero_homog : ∀ p, IsHomog 0 p
  neg_homog : ∀ {a : R} {p : ℕ}, IsHomog a p → IsHomog (-a) p
  add_homog : ∀ {a b : R} {p : ℕ}, IsHomog a p → IsHomog b p → IsHomog (a + b) p
  mul_homog : ∀ {a b : R} {p q : ℕ}, IsHomog a p → IsHomog b q → IsHomog (a * b) (p + q)
  proj : ℕ → R → R
  proj_self : ∀ {a : R} {p : ℕ}, IsHomog a p → proj p a = a
  proj_other : ∀ {a : R} {p q : ℕ}, IsHomog a p → p ≠ q → proj q a = 0
  proj_homog : ∀ (p : ℕ) (a : R), IsHomog (proj p a) p

/-- Assertion that the curvature matrix has every entry of homogeneous degree 2 (i.e., a 2-form). -/
def CurvatureMatrixDegreeTwo {r : ℕ} {R : Type*} [CommRing R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) : Prop :=
  ∀ i j, IsGradedFormAlgebra.IsHomog (curvMatrix i j) 2

/-- The $j$-th Chern class form $c_j$: the degree-$2j$ component of the total Chern form. -/
def chernClass {r : ℕ} {R : Type*} [CommRing R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) (j : ℕ) : R :=
  IsGradedFormAlgebra.proj (2 * j) (totalChernForm curvMatrix t)

/-- The $j$-th Chern class form is homogeneous of degree $2j$. -/
theorem chernClass_homog {r : ℕ} {R : Type*} [CommRing R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) (j : ℕ)
    (_ht : IsGradedFormAlgebra.IsHomog t 0)
    (_hR : CurvatureMatrixDegreeTwo curvMatrix) :
    IsGradedFormAlgebra.IsHomog (chernClass curvMatrix t j) (2 * j) := by
  unfold chernClass
  exact IsGradedFormAlgebra.proj_homog (2 * j) _



/-- Assertion that the Chern normalization scalar $\frac{i}{2\pi}$ has graded degree 0. -/
def ChernScalarHomogZero {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R] : Prop :=
  IsGradedFormAlgebra.IsHomog (algebraMap ℂ R chernScalar) 0


/-- The $j$-th Chern class form with the $\frac{i}{2\pi}$ normalization: the degree-$2j$ part
of $\det(I + \frac{i}{2\pi} R^\nabla)$. -/
noncomputable def chernClassWithScalar {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (j : ℕ) : R :=
  chernClass curvMatrix (algebraMap ℂ R chernScalar) j


/-- The normalized $j$-th Chern class form is homogeneous of degree $2j$. -/
theorem chernClassWithScalar_homog
    {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (j : ℕ)
    (ht : ChernScalarHomogZero (R := R))
    (hR : CurvatureMatrixDegreeTwo curvMatrix) :
    IsGradedFormAlgebra.IsHomog (chernClassWithScalar curvMatrix j) (2 * j) :=
  chernClass_homog curvMatrix _ j ht hR

/-- The first Chern form $c_1 = t \cdot \mathrm{tr}(\Omega)$, the linear-in-$t$ term of $\det(I + t\,\Omega)$. -/
def firstChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  t * curvMatrix.trace


/-- The top Chern form $c_r = t^r \det(\Omega)$, which on a compact oriented manifold equals the
Euler class $e(E) \in H^{2r}(M, \mathbb{Z})$. -/
def topChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  t ^ r * curvMatrix.det


/-- A connection on a line bundle, given locally by a connection 1-form $A \in \Omega^1$ with
curvature $R^\nabla = dA \in \Omega^2$ automatically closed. -/
structure LineBundleConnection (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  A : Ω 1
  curvature : Ω 2
  curvature_eq_dA : curvature = inst.d A
  curvature_closed : inst.d curvature = 0


/-- A representative of the first Chern class of a line bundle: $c_1(L) = [\frac{1}{2\pi} R^\nabla]$. -/
noncomputable def firstChernClassRep
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (curvature : Ω 2) : Ω 2 :=
  (1 / (2 * Real.pi)) • curvature

/-- Unfolding lemma: $c_1$ representative equals $\frac{1}{2\pi} R^\nabla$ by definition. -/
@[simp]
theorem firstChernClassRep_def
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (curvature : Ω 2) :
    firstChernClassRep (VF := VF) curvature = (1 / (2 * Real.pi)) • curvature := rfl

/-- The first Chern class representative of a line bundle connection: $\frac{1}{2\pi} R^\nabla$. -/
noncomputable def firstChernClassOfLineBundle
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (conn : LineBundleConnection Ω VF) : Ω 2 :=
  firstChernClassRep (VF := VF) conn.curvature

/-- The first Chern class form $\frac{1}{2\pi} R^\nabla$ is closed if the curvature is closed. -/
theorem first_chern_form_closed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (curvature : Ω 2)
    (hcurv : inst.d curvature = 0) :
    inst.d (firstChernClassRep (VF := VF) curvature) = 0 := by
  simp only [firstChernClassRep_def]
  rw [inst.d_smul, hcurv, smul_zero]


/-- Data for the Chern connection in a holomorphic frame: a connection form $A$ with the
decomposition $d = \partial + \bar\partial$ and the identity $\partial A = -A \wedge A$. -/
structure HolomorphicFrameData (R : Type*) [Ring R] where
  A : R
  d : R → R
  del : R → R
  dbar : R → R
  d_eq_del_add_dbar : ∀ x, d x = del x + dbar x
  del_A_eq : del A = -(A * A)

/-- Construction of holomorphic frame data starting from a Hermitian metric, with connection
form $A = h^{-1} \partial h$. -/
def HolomorphicFrameData.mk_from_metric
    {R : Type*} [Ring R]
    (d del dbar : R → R) (h_inv del_h : R)

    (h_decomp : ∀ x, d x = del x + dbar x)

    (h_inv_deriv : del h_inv = -(h_inv * del_h * h_inv))

    (h_leib : del (h_inv * del_h) = del h_inv * del_h + h_inv * del del_h)

    (h_del_sq : del del_h = 0) :
    HolomorphicFrameData R where
  A := h_inv * del_h
  d := d
  del := del
  dbar := dbar
  d_eq_del_add_dbar := h_decomp
  del_A_eq := by

    rw [h_leib, h_del_sq, mul_zero, add_zero, h_inv_deriv]
    noncomm_ring








/-- A holomorphic vector bundle: a graded space of bundle-valued forms equipped with a Dolbeault
operator $\bar\partial_E$ satisfying $\bar\partial_E^2 = 0$. -/
structure HolomorphicVectorBundle
    (BundleValuedForms : ℕ → Type*) [∀ q, AddCommGroup (BundleValuedForms q)] where
  dbar_E : ∀ {q : ℕ}, BundleValuedForms q → BundleValuedForms (q + 1)
  dbar_add : ∀ {q : ℕ} (σ τ : BundleValuedForms q),
    dbar_E (σ + τ) = dbar_E σ + dbar_E τ
  dbar_squared : ∀ {q : ℕ} (σ : BundleValuedForms q), dbar_E (dbar_E σ) = 0

/-- A $\bar\partial_E$-closed form of bidegree $(0,q)$ with values in $E$, representing a
Dolbeault cohomology class in $H^{0,q}(M, E)$. -/
structure DolbeaultCohomologyWithCoefficients
    {BundleValuedForms : ℕ → Type*} [∀ q, AddCommGroup (BundleValuedForms q)]
    (E : HolomorphicVectorBundle BundleValuedForms)
    (q : ℕ) where
  representative : BundleValuedForms q
  is_closed : E.dbar_E representative = 0

/-- Cohomological equivalence: two $(0,q+1)$-forms represent the same Dolbeault class iff their
difference is $\bar\partial_E$-exact. -/
def DolbeaultCohomologyWithCoefficients.Equiv
    {BundleValuedForms : ℕ → Type*} [∀ q, AddCommGroup (BundleValuedForms q)]
    {E : HolomorphicVectorBundle BundleValuedForms}
    {q : ℕ}
    (c₁ c₂ : DolbeaultCohomologyWithCoefficients E (q + 1)) : Prop :=
  ∃ (β : BundleValuedForms q), c₁.representative - c₂.representative = E.dbar_E β

/-- The Chern connection on a Hermitian holomorphic bundle: the unique connection compatible
with the Hermitian metric $h$ whose $(0,1)$-part is $\bar\partial$, with connection form
$A = h^{-1} \partial h$. -/
structure ChernConnection (R : Type*) [Ring R] where
  del : R → R
  dbar : R → R
  d : R → R
  h : R
  h_inv : R
  h_inv_left : h_inv * h = 1
  h_inv_right : h * h_inv = 1
  d_decomp : ∀ x, d x = del x + dbar x
  A : R
  A_eq : A = h_inv * del h
  metric_compat : h * A = del h
