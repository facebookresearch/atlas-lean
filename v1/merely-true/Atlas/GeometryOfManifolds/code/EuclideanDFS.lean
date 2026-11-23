/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Atlas.GeometryOfManifolds.code.DifferentialForms

noncomputable section

/-- Shorthand for $n$-dimensional Euclidean space $\mathbb{R}^n$ with its standard inner product. -/
abbrev Eℝ (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The space $\Omega^p(\mathbb{R}^n)$ of (not-necessarily-smooth) differential $p$-forms on
$\mathbb{R}^n$: pointwise alternating $\mathbb{R}$-multilinear maps
$(\mathbb{R}^n)^p \to \mathbb{R}$. -/
def EuclideanΩ (n : ℕ) (p : ℕ) :=
  Eℝ n → (Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ)

/-- The space of vector fields $\mathfrak{X}(\mathbb{R}^n)$ on Euclidean space: arbitrary maps
$\mathbb{R}^n \to \mathbb{R}^n$. -/
def EuclideanVF (n : ℕ) :=
  Eℝ n → Eℝ n

namespace EuclideanΩ

variable {n p : ℕ}

/-- Pointwise abelian-group structure on $\Omega^p(\mathbb{R}^n)$. -/
instance instAddCommGroup : AddCommGroup (EuclideanΩ n p) := Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on $\Omega^p(\mathbb{R}^n)$. -/
instance instModule : Module ℝ (EuclideanΩ n p) := Pi.module _ _ _

/-- Extensionality for Euclidean $p$-forms: two forms agreeing pointwise are equal. -/
@[ext]
theorem ext {α β : EuclideanΩ n p} (h : ∀ x, α x = β x) : α = β :=
  funext h

/-- Pointwise evaluation of an addition of forms. -/
@[simp]
theorem add_apply (α β : EuclideanΩ n p) (x : Eℝ n) : (α + β) x = α x + β x := rfl

/-- Pointwise evaluation of a negated form. -/
@[simp]
theorem neg_apply' (α : EuclideanΩ n p) (x : Eℝ n) : (-α) x = -(α x) := rfl

/-- Pointwise evaluation of a scalar multiple. -/
@[simp]
theorem smul_apply' (r : ℝ) (α : EuclideanΩ n p) (x : Eℝ n) : (r • α) x = r • (α x) := rfl

/-- Pointwise evaluation of the zero form. -/
@[simp]
theorem zero_apply' (x : Eℝ n) : (0 : EuclideanΩ n p) x = 0 := rfl

/-- Continuous-fibre version of `EuclideanΩ`: pointwise *continuous* alternating multilinear maps.
This is the regularity needed for the differential to be defined via `fderiv`. -/
abbrev CEuclideanΩ (n : ℕ) (p : ℕ) := Eℝ n → (Eℝ n [⋀^Fin p]→L[ℝ] ℝ)

section ExteriorDerivative

variable {n p : ℕ}

/-- Identify a $0$-form $\alpha : \mathbb{R}^n \to \mathrm{Alt}^0(\mathbb{R}^n;\mathbb{R})$ with
its underlying scalar function $x \mapsto \alpha(x)()$. -/
def zeroFormScalar (α : EuclideanΩ n 0) : Eℝ n → ℝ := fun x => α x Fin.elim0

/-- Exterior derivative of a $0$-form: $d f$ as the $1$-form whose value at $x$ is the linear
map $v \mapsto Df(x)(v)$. -/
def euclideanD0 (α : EuclideanΩ n 0) : EuclideanΩ n 1 :=
  fun x =>
    (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1))
      ((fderiv ℝ (zeroFormScalar α) x).toLinearMap)

/-- Auxiliary helper: the Fréchet derivative $D\alpha(x)$ of a continuous-fibre $p$-form viewed
as a linear map $\mathbb{R}^n \to \mathrm{Alt}^p(\mathbb{R}^n; \mathbb{R})$. -/
def fderivToAltMap (α : CEuclideanΩ n p) (x : Eℝ n) :
    Eℝ n →ₗ[ℝ] (Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) :=
  (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ) (A := ℝ)).comp
    (fderiv ℝ α x).toLinearMap

/-- Variant of `fderivToAltMap` landing in plain `MultilinearMap`s, used in the explicit
`uncurryMid` construction of $d\alpha$. -/
def fderivToMMap (α : CEuclideanΩ n p) (x : Eℝ n) :
    Eℝ n →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin p => Eℝ n) ℝ :=
  ((AlternatingMap.toMultilinearMapLM (S := ℝ)).comp
    (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ) (A := ℝ))).comp
    (fderiv ℝ α x).toLinearMap

/-- Intermediate non-alternated $(p+1)$-multilinear map obtained by uncurrying the derivative
$D\alpha(x)$ in the first slot. -/
def euclideanD_M0 (α : CEuclideanΩ n p) (x : Eℝ n) :
    MultilinearMap ℝ (fun _ : Fin (p + 1) => Eℝ n) ℝ :=
  LinearMap.uncurryMid (0 : Fin (p + 1)) (fderivToMMap α x)

/-- Exterior derivative $d : \Omega^p \to \Omega^{p+1}$ on continuous-fibre forms, defined
pointwise as the antisymmetrisation of the uncurried Fréchet derivative. -/
def euclideanD (α : CEuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  fun x => AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x)

end ExteriorDerivative

section ContinuousLift

/-- Every alternating multilinear form $f : (\mathbb{R}^n)^p \to \mathbb{R}$ is automatically
continuous, since on the finite-dimensional Euclidean space $\mathbb{R}^n$ it is a finite
polynomial in the coordinates of its arguments. -/
lemma AlternatingMap.continuous_of_euclidean {n p : ℕ}
    (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) : Continuous (⇑f : (Fin p → Eℝ n) → ℝ) := by

  have key : ∀ m : Fin p → Eℝ n,
      f m = ∑ r : Fin p → Fin n,
        (∏ i : Fin p, (m i (r i) : ℝ)) *
          f (fun i => EuclideanSpace.single (r i) (1 : ℝ)) := by
    intro m
    have hdecomp : m = fun i => ∑ j : Fin n, m i j • EuclideanSpace.single j (1 : ℝ) := by
      ext i k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]

    change f.toMultilinearMap _ = _
    rw [f.toMultilinearMap.map_sum]
    congr 1; ext r

    change f.toMultilinearMap _ = _
    rw [show (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ)) =
      (fun i => (m i (r i) : ℝ) • (fun i => EuclideanSpace.single (r i) (1 : ℝ)) i) from rfl]
    rw [f.toMultilinearMap.map_smul_univ]
    simp [smul_eq_mul]

  rw [show ⇑f = (fun m => ∑ r : Fin p → Fin n,
      (∏ i : Fin p, (m i (r i) : ℝ)) *
        f (fun i => EuclideanSpace.single (r i) (1 : ℝ))) from funext key]
  apply continuous_finset_sum _ (fun r _ => ?_)
  apply Continuous.mul
  · apply continuous_finset_prod _ (fun i _ => ?_)
    exact ((EuclideanSpace.proj (r i)).continuous).comp (continuous_apply i)
  · exact continuous_const

/-- Lift an algebraic alternating map on $\mathbb{R}^n$ to its continuous counterpart, using the
automatic continuity established above. -/
def toCAlt {n p : ℕ} (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) : Eℝ n [⋀^Fin p]→L[ℝ] ℝ where
  toContinuousMultilinearMap :=
    { f.toMultilinearMap with cont := AlternatingMap.continuous_of_euclidean f }
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

/-- Forget continuity of an alternating multilinear map. -/
def fromCAlt {n p : ℕ} (g : Eℝ n [⋀^Fin p]→L[ℝ] ℝ) : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ :=
  g.toAlternatingMap

/-- Round-trip identity: forgetting continuity after adding it returns the original map. -/
@[simp]
theorem fromCAlt_toCAlt {n p : ℕ} (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) :
    fromCAlt (toCAlt f) = f := by
  ext v; rfl

/-- Round-trip identity: re-adding continuity after forgetting it recovers the original map. -/
@[simp]
theorem toCAlt_fromCAlt {n p : ℕ} (g : Eℝ n [⋀^Fin p]→L[ℝ] ℝ) :
    toCAlt (fromCAlt g) = g := by
  ext v; rfl

/-- Evaluating the continuous lift of $f$ on a tuple gives the same value as evaluating $f$. -/
@[simp]
theorem toCAlt_apply {n p : ℕ} (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) (v : Fin p → Eℝ n) :
    toCAlt f v = f v := rfl

/-- Pointwise lift of $\alpha \in \Omega^p(\mathbb{R}^n)$ to a continuous-fibre form. -/
def toCEuclideanΩ {n p : ℕ} (α : EuclideanΩ n p) : CEuclideanΩ n p :=
  fun x => toCAlt (α x)



/-- Pointwise forgetful map from continuous-fibre forms back to algebraic ones. -/
def CEuclideanΩ.toEuclideanΩ' {n p : ℕ} (α : EuclideanΩ.CEuclideanΩ n p) : EuclideanΩ n p :=
  fun x => fromCAlt (α x)

/-- Round-trip: lifting back to continuous-fibre after forgetting gives the original form. -/
theorem EuclideanΩ_toCEuclideanΩ_toEuclideanΩ' {n p : ℕ}
    (α : EuclideanΩ.CEuclideanΩ n p) :
    toCEuclideanΩ (CEuclideanΩ.toEuclideanΩ' α) = α := by
  apply funext; intro x
  simp [CEuclideanΩ.toEuclideanΩ', toCEuclideanΩ]

/-- Exterior derivative on $\Omega^p(\mathbb{R}^n)$: lift $\alpha$ to a continuous-fibre form,
take $d$ there, and forget continuity. This is the exterior derivative used by the Euclidean
differential form space instance. -/
def euclideanD_lifted {n p : ℕ} (α : EuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  euclideanD (toCEuclideanΩ α)

end ContinuousLift

end EuclideanΩ

/-- Pointwise multiplication of a $p$-form by a $0$-form (scalar function):
$(f \cdot \alpha)(x) = f(x) \cdot \alpha(x)$. -/
def euclideanFMul {n p : ℕ} (f : EuclideanΩ n 0) (α : EuclideanΩ n p) : EuclideanΩ n p :=
  fun x => (f x Fin.elim0) • (α x)

/-- Definitional pointwise formula for function-form multiplication. -/
@[simp]
theorem euclideanFMul_apply {n p : ℕ} (f : EuclideanΩ n 0) (α : EuclideanΩ n p) (x : Eℝ n) :
    euclideanFMul f α x = (f x Fin.elim0) • (α x) := rfl

/-- The constant coordinate $1$-form $dx_i$ on $\mathbb{R}^n$: at every point $x$ it sends
$v \in \mathbb{R}^n$ to its $i$-th component $v_i$. -/
def dx_i {n : ℕ} (i : Fin n) : EuclideanΩ n 1 :=
  fun _ => (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1)) (EuclideanSpace.projₗ i)

/-- Interior product (contraction) $\iota_X \alpha$ of a $(p+1)$-form with a vector field
$X$: at each point $x$, it is the $p$-form $v \mapsto \alpha(x)(X(x), v_1, \ldots, v_p)$. -/
def euclideanIota {n : ℕ} (X : EuclideanVF n) {p : ℕ} (α : EuclideanΩ n (p + 1)) :
    EuclideanΩ n p :=
  fun x => (α x).curryLeft (X x)

/-- Contraction is additive in the form argument: $\iota_X(\alpha + \beta) = \iota_X\alpha + \iota_X\beta$. -/
theorem euclideanIota_add {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (α β : EuclideanΩ n (p + 1)) :
    euclideanIota X (α + β) = euclideanIota X α + euclideanIota X β := by
  ext x
  simp [euclideanIota]

/-- Contraction commutes with scalar multiplication: $\iota_X(r\,\alpha) = r\,\iota_X\alpha$. -/
theorem euclideanIota_smul {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (r : ℝ) (α : EuclideanΩ n (p + 1)) :
    euclideanIota X (r • α) = r • euclideanIota X α := by
  ext x
  simp [euclideanIota]

/-- Identify a pointwise $1$-form with the underlying linear functional $\mathbb{R}^n \to \mathbb{R}$. -/
def oneFormLinear {n : ℕ} (ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ) : Eℝ n →ₗ[ℝ] ℝ :=
  (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1)).symm ω_x

/-- Pointwise wedge product $\omega \wedge \alpha$ where $\omega$ is a $1$-form and $\alpha$ is
a $p$-form: antisymmetrise the tensor product $\omega \otimes \alpha$ via the uncurry-and-alternate
construction. -/
def wedgePointwise {n p : ℕ}
    (ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ) (α_x : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) :
    Eℝ n [⋀^Fin (p + 1)]→ₗ[ℝ] ℝ :=
  AlternatingMap.alternatizeUncurryFin ((oneFormLinear ω_x).smulRight α_x)

/-- Wedge product of a Euclidean $1$-form $\omega$ with a $p$-form $\alpha$, defined pointwise
via `wedgePointwise`. -/
def euclideanWedge1 {n : ℕ} (ω : EuclideanΩ n 1) {p : ℕ}
    (α : EuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  fun x => wedgePointwise (ω x) (α x)

/-- Wedge with a fixed $1$-form is additive on the right: $\omega \wedge (\alpha + \beta) =
\omega \wedge \alpha + \omega \wedge \beta$. -/
theorem euclideanWedge1_add_right {n : ℕ} (ω : EuclideanΩ n 1) {p : ℕ}
    (α β : EuclideanΩ n p) :
    euclideanWedge1 ω (α + β) = euclideanWedge1 ω α + euclideanWedge1 ω β := by
  funext x
  show wedgePointwise (ω x) ((α + β) x) =
    wedgePointwise (ω x) (α x) + wedgePointwise (ω x) (β x)
  simp only [EuclideanΩ.add_apply]
  unfold wedgePointwise
  have h : (oneFormLinear (ω x)).smulRight (α x + β x) =
      (oneFormLinear (ω x)).smulRight (α x) + (oneFormLinear (ω x)).smulRight (β x) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.smulRight_apply, LinearMap.add_apply, smul_add]
  rw [h, AlternatingMap.alternatizeUncurryFin_add]

/-- Wedge with a fixed $1$-form commutes with scalar multiplication on the right:
$\omega \wedge (r\,\alpha) = r\,(\omega \wedge \alpha)$. -/
theorem euclideanWedge1_smul_right {n : ℕ} (ω : EuclideanΩ n 1) {p : ℕ}
    (r : ℝ) (α : EuclideanΩ n p) :
    euclideanWedge1 ω (r • α) = r • euclideanWedge1 ω α := by
  funext x
  show wedgePointwise (ω x) ((r • α) x) = r • wedgePointwise (ω x) (α x)
  simp only [EuclideanΩ.smul_apply']
  unfold wedgePointwise
  have h : (oneFormLinear (ω x)).smulRight (r • α x) =
      r • (oneFormLinear (ω x)).smulRight (α x) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]
    rw [smul_comm]
  rw [h, AlternatingMap.alternatizeUncurryFin_smul]

/-- Pointwise scalar-function multiplication on continuous-fibre forms: $(g \cdot \alpha)(x) =
g(x) \cdot \alpha(x)$. -/
def cFMul {n p : ℕ} (g : Eℝ n → ℝ) (α : EuclideanΩ.CEuclideanΩ n p) :
    EuclideanΩ.CEuclideanΩ n p :=
  g • α

/-- Forget the continuity data of a continuous-fibre form to get an algebraic Euclidean form. -/
def CEuclideanΩ.toEΩ {n p : ℕ} (α : EuclideanΩ.CEuclideanΩ n p) : EuclideanΩ n p :=
  fun x => (α x).toAlternatingMap

/-- Exterior derivative of a *raw* scalar function $g : \mathbb{R}^n \to \mathbb{R}$, returning
the $1$-form $dg$ with $dg(x)(v) = Dg(x)(v)$. -/
def euclideanD_scalar {n : ℕ} (g : Eℝ n → ℝ) : EuclideanΩ n 1 :=
  fun x => (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1))
    ((fderiv ℝ g x).toLinearMap)

/-- Interior product $\iota_X$ on continuous-fibre forms (the same construction as
`euclideanIota` but preserving continuity of the fibres). -/
def euclideanIotaC {n : ℕ} (X : EuclideanVF n) {p : ℕ} (α : EuclideanΩ.CEuclideanΩ n (p + 1)) :
    EuclideanΩ.CEuclideanΩ n p :=
  fun x => (α x).curryLeft (X x)

/-- Additivity of contraction on continuous-fibre forms. -/
theorem euclideanIotaC_add {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (α β : EuclideanΩ.CEuclideanΩ n (p + 1)) :
    euclideanIotaC X (α + β) = euclideanIotaC X α + euclideanIotaC X β := by
  ext x v
  simp only [euclideanIotaC, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Compatibility of contraction with scalar multiplication on continuous-fibre forms. -/
theorem euclideanIotaC_smul {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (r : ℝ) (α : EuclideanΩ.CEuclideanΩ n (p + 1)) :
    euclideanIotaC X (r • α) = r • euclideanIotaC X α := by
  ext x v
  simp only [euclideanIotaC, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]

namespace EuclideanΩ

/-- Additivity of the exterior derivative on continuous-fibre forms (assuming differentiability):
$d(\alpha + \beta) = d\alpha + d\beta$. -/
theorem euclideanD_add {n p : ℕ} (α β : CEuclideanΩ n p)
    (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) :
    euclideanD (α + β) = euclideanD α + euclideanD β := by
  funext x
  show AlternatingMap.alternatizeUncurryFin (fderivToAltMap (α + β) x) =
    AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x) +
    AlternatingMap.alternatizeUncurryFin (fderivToAltMap β x)
  have hfA : fderivToAltMap (α + β) x = fderivToAltMap α x + fderivToAltMap β x := by
    ext h w
    simp only [fderivToAltMap, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearMap.add_apply, fderiv_add (hα x) (hβ x), ContinuousLinearMap.add_apply,
      map_add]
  rw [hfA, AlternatingMap.alternatizeUncurryFin_add]

/-- Scalar compatibility of the exterior derivative on continuous-fibre forms:
$d(r\,\alpha) = r\,d\alpha$. -/
theorem euclideanD_smul {n p : ℕ} (r : ℝ) (α : CEuclideanΩ n p)
    (hα : Differentiable ℝ α) :
    euclideanD (r • α) = r • euclideanD α := by
  funext x
  show AlternatingMap.alternatizeUncurryFin (fderivToAltMap (r • α) x) =
    r • AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x)
  have hfA : fderivToAltMap (r • α) x = r • fderivToAltMap α x := by
    ext h w
    simp only [fderivToAltMap, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearMap.smul_apply, fderiv_const_smul (hα x) r, ContinuousLinearMap.smul_apply,
      map_smul]
  rw [hfA, AlternatingMap.alternatizeUncurryFin_smul]

end EuclideanΩ

/-- Lie derivative of a $(p+1)$-form along a vector field $X$ via Cartan's magic formula:
$\mathcal{L}_X \alpha = d(\iota_X \alpha) + \iota_X(d\alpha)$. -/
def euclideanL {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (α : EuclideanΩ.CEuclideanΩ n (p + 1)) : EuclideanΩ n (p + 1) :=
  EuclideanΩ.euclideanD (euclideanIotaC X α) + euclideanIota X (EuclideanΩ.euclideanD α)

/-- Lie derivative on $0$-forms: $\mathcal{L}_X f = Df \cdot X$, the directional derivative of
the scalar function underlying $f$ in the direction $X(x)$. -/
def euclideanL0 {n : ℕ} (X : EuclideanVF n) (f : EuclideanΩ n 0) : EuclideanΩ n 0 :=
  fun x => AlternatingMap.constOfIsEmpty ℝ (Eℝ n) (Fin 0)
    (fderiv ℝ (EuclideanΩ.zeroFormScalar f) x (X x))

end

section DFSInstance

variable {n : ℕ}

open EuclideanΩ

/-- Lie derivative $\mathcal{L}_X : \Omega^p \to \Omega^p$ on Euclidean forms, defined via
Cartan's magic formula. On $0$-forms it reduces to $\iota_X d\alpha$, and on $(p+1)$-forms to
$d(\iota_X\alpha) + \iota_X(d\alpha)$. -/
noncomputable def euclideanLie (X : EuclideanVF n) {p : ℕ}
    (α : EuclideanΩ n p) : EuclideanΩ n p :=
  match p with
  | 0 => euclideanIota X (euclideanD_lifted α)
  | _ + 1 => euclideanD_lifted (euclideanIota X α) + euclideanIota X (euclideanD_lifted α)

/-- Function-form multiplication is additive in the function: $(f + g)\,\alpha = f\,\alpha + g\,\alpha$. -/
theorem euclideanFMul_add_left {p : ℕ} (f g : EuclideanΩ n 0) (α : EuclideanΩ n p) :
    euclideanFMul (f + g) α = euclideanFMul f α + euclideanFMul g α := by
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.add_apply, AlternatingMap.add_apply,
    AlternatingMap.smul_apply]
  exact add_smul _ _ _

/-- Function-form multiplication is additive in the form: $f\,(\alpha + \beta) = f\,\alpha + f\,\beta$. -/
theorem euclideanFMul_add_right {p : ℕ} (f : EuclideanΩ n 0) (α β : EuclideanΩ n p) :
    euclideanFMul f (α + β) = euclideanFMul f α + euclideanFMul f β := by
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.add_apply, AlternatingMap.add_apply,
    AlternatingMap.smul_apply]
  rw [smul_add]

/-- Scalar multiplication of the function commutes with function-form multiplication:
$(r\,f)\,\alpha = r\,(f\,\alpha)$. -/
theorem euclideanFMul_smul {p : ℕ} (r : ℝ) (f : EuclideanΩ n 0) (α : EuclideanΩ n p) :
    euclideanFMul (r • f) α = r • euclideanFMul f α := by
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.smul_apply', AlternatingMap.smul_apply]
  exact smul_assoc _ _ _

/-- Contraction commutes with multiplication by a scalar function:
$\iota_X(f \cdot \alpha) = f \cdot \iota_X \alpha$. -/
theorem euclideanIota_fMul (X : EuclideanVF n) {p : ℕ}
    (f : EuclideanΩ n 0) (α : EuclideanΩ n (p + 1)) :
    euclideanIota X (euclideanFMul f α) = euclideanFMul f (euclideanIota X α) := by
  funext x; ext v
  simp only [euclideanIota, euclideanFMul_apply, AlternatingMap.smul_apply]
  rfl





/-- The pointwise value of `euclideanD α` agrees with `extDeriv α x` after forgetting continuity.
This bridges the local definition here with Mathlib's `extDeriv`. -/
lemma euclideanD_eq_extDeriv_toAlternatingMap {p : ℕ}
    (α : CEuclideanΩ n p) (x : Eℝ n) :
    euclideanD α x = (extDeriv α x).toAlternatingMap := by
  unfold euclideanD fderivToAltMap extDeriv
  rw [ContinuousAlternatingMap.toAlternatingMap_alternatizeUncurryFin]

/-- The continuous-fibre lift of `euclideanD α` is exactly Mathlib's `extDeriv α`. -/
lemma toCEuclideanΩ_euclideanD {p : ℕ} (α : CEuclideanΩ n p) :
    toCEuclideanΩ (euclideanD α) = extDeriv α := by
  funext x
  simp only [toCEuclideanΩ, euclideanD_eq_extDeriv_toAlternatingMap]
  exact toCAlt_fromCAlt (extDeriv α x)


/-- Technical identity describing how `curryLeft` interacts with the antisymmetrisation of
`L.smulRight β` for a linear functional $L$ and an alternating $(m+1)$-multilinear map $\beta$.
Used to prove the Cartan formula relating $\iota_X$ and wedge product. -/
lemma curryLeft_alternatizeUncurryFin_smulRight
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {m : ℕ} (L : M →ₗ[R] R) (β : M [⋀^Fin (m + 1)]→ₗ[R] N) (v : M) :
    (AlternatingMap.alternatizeUncurryFin (L.smulRight β)).curryLeft v =
      L v • β - AlternatingMap.alternatizeUncurryFin (L.smulRight (β.curryLeft v)) := by
  ext w
  simp only [AlternatingMap.curryLeft_apply_apply, AlternatingMap.alternatizeUncurryFin_apply,
    AlternatingMap.sub_apply, AlternatingMap.smul_apply, LinearMap.smulRight_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero]
  have h0 : Fin.removeNth 0 (Matrix.vecCons v w) = w := by
    ext k; simp [Fin.removeNth, Matrix.cons_val_succ]
  rw [h0]
  have hsucc : ∀ i : Fin (m + 1), (Matrix.vecCons v w) i.succ = w i :=
    fun i => Matrix.cons_val_succ v w i
  have hrem : ∀ i : Fin (m + 1),
      Fin.removeNth i.succ (Matrix.vecCons v w) = Matrix.vecCons v (Fin.removeNth i w) := by
    intro i; ext k
    simp only [Fin.removeNth, Matrix.vecCons]
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [Fin.succ_succAbove_zero, Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ]; rfl
  simp_rw [hsucc, hrem, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Evaluation formula for `oneFormLinear`: applying it to $v$ equals applying the original
$1$-form $\omega_x$ to the length-$1$ tuple containing $v$. -/
lemma oneFormLinear_apply_eq {n : ℕ} (ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ) (v : Eℝ n) :
    oneFormLinear ω_x v = ω_x (Matrix.vecCons v Fin.elim0) := by
  simp only [oneFormLinear, AlternatingMap.ofSubsingleton_symm_apply_apply]
  congr 1
  ext ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  simp [Matrix.vecCons]

/-- Leibniz rule for contraction across a wedge with a $1$-form (the degree-$1$ case of
$\iota_X(\omega \wedge \alpha) = (\iota_X\omega) \wedge \alpha - \omega \wedge (\iota_X\alpha)$,
with the leading wedge becoming function-form multiplication since $\iota_X\omega$ is a
$0$-form). -/
theorem euclideanIota_wedge1 {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (ω : EuclideanΩ n 1) (α : EuclideanΩ n (p + 1)) :
    euclideanIota X (euclideanWedge1 ω α) =
      euclideanFMul (euclideanIota X ω) α - euclideanWedge1 ω (euclideanIota X α) := by
  funext x
  show (wedgePointwise (ω x) (α x)).curryLeft (X x) =
    ((ω x).curryLeft (X x) Fin.elim0) • (α x) - wedgePointwise (ω x) ((α x).curryLeft (X x))
  unfold wedgePointwise
  rw [curryLeft_alternatizeUncurryFin_smulRight]
  congr 1
  rw [oneFormLinear_apply_eq]
  simp [AlternatingMap.curryLeft_apply_apply]





end DFSInstance
