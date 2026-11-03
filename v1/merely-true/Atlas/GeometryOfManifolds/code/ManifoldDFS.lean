/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.VectorField
import Atlas.GeometryOfManifolds.code.DifferentialForms
import Atlas.GeometryOfManifolds.code.OmitIndex

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff

/-- Differential $p$-forms on a smooth manifold $M$ (modeled on $E$ via `I`), realized
concretely as functions $M \to \Lambda^p E^*$ from points of $M$ to alternating $p$-forms
on the model space $E$. -/
@[reducible]
def ManifoldΩ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (p : ℕ) : Type _ :=
  M → (E [⋀^Fin p]→L[ℝ] ℝ)

/-- Vector fields on $M$ (modeled on $E$), realized concretely as functions $M \to E$
assigning to each point an element of the model space. -/
@[reducible]
def ManifoldVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  M → E

section Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
variable [ChartedSpace H M]

/-- Pointwise addition gives the space of differential $p$-forms an abelian group structure. -/
noncomputable instance instAddCommGroupManifoldΩ (p : ℕ) :
    AddCommGroup (ManifoldΩ I M p) :=
  inferInstance

/-- Pointwise scalar multiplication gives differential $p$-forms an $\mathbb{R}$-module structure. -/
noncomputable instance instModuleManifoldΩ (p : ℕ) :
    Module ℝ (ManifoldΩ I M p) :=
  inferInstance

end Instances

namespace ManifoldWedgeHelpers

section WedgeHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convert a continuous alternating $1$-form $w \in \Lambda^1 E^*$ to a continuous linear
functional $E \to \mathbb{R}$, using the canonical identification of singleton-indexed
alternating maps with linear maps. -/
noncomputable def oneFormToCL
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm w

/-- Pointwise wedge product of a $1$-form $w$ with a $p$-form $a$, producing a $(p+1)$-form
$w \wedge a$ via antisymmetrization of $(v_0, v_1, \dots, v_p) \mapsto w(v_0) \cdot a(v_1, \dots, v_p)$. -/
noncomputable def wedgePointwiseGeneral {p : ℕ}
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) (a : E [⋀^Fin p]→L[ℝ] ℝ) :
    E [⋀^Fin (p + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin ((oneFormToCL w).smulRight a)

/-- Evaluating `oneFormToCL w` at a vector $v$ is the same as evaluating the original
$1$-form on the one-element tuple $[v]$. -/
lemma oneFormToCL_apply_eq
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    oneFormToCL w v = w (Matrix.vecCons v Fin.elim0) := by
  simp only [oneFormToCL, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
  congr 1; ext ⟨i, hi⟩; interval_cases i; simp [Matrix.vecCons]

/-- Currying-on-the-left commutes with antisymmetrization in the following sense:
$$\iota_v (L \wedge \beta) = (Lv) \cdot \beta - L \wedge (\iota_v \beta),$$
the basic Leibniz identity for $\iota_v$ acting on a wedge product $L \wedge \beta$. -/
lemma curryLeft_alternatizeUncurryFin_smulRight
    {m : ℕ} (L : E →L[ℝ] ℝ) (β : E [⋀^Fin (m + 1)]→L[ℝ] ℝ) (v : E) :
    (ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight β)).curryLeft v =
      L v • β - ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight (β.curryLeft v)) := by
  ext w
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
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

end WedgeHelpers

end ManifoldWedgeHelpers

open ManifoldWedgeHelpers

section Operations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Multiplication of a $p$-form $\alpha$ by a scalar function $f \in \Omega^0$:
$(f \cdot \alpha)_x = f(x) \cdot \alpha_x$. -/
noncomputable def manifoldFMul {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) : ManifoldΩ I M p :=
  fun x => (f x Fin.elim0) • (α x)

/-- Interior product $\iota_X \alpha$: contracts a vector field $X$ into the first slot of
a $(p+1)$-form $\alpha$, producing a $p$-form. -/
noncomputable def manifoldIota (X : ManifoldVF I M) {p : ℕ}
    (α : ManifoldΩ I M (p + 1)) : ManifoldΩ I M p :=
  fun x => (α x).curryLeft (X x)


/-- Wedge product of a $1$-form $w$ with a $p$-form $\alpha$, producing a $(p+1)$-form
$w \wedge \alpha$ defined pointwise. -/
noncomputable def manifoldWedge1 {p : ℕ}
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M p) : ManifoldΩ I M (p + 1) :=
  fun x => wedgePointwiseGeneral (w x) (α x)





/-- Interior product against the zero form vanishes: $\iota_X 0 = 0$. -/
lemma manifoldIota_zero (X : ManifoldVF I M) {p : ℕ} :
    manifoldIota I X (0 : ManifoldΩ I M (p + 1)) = 0 := by
  ext x
  simp [manifoldIota]

/-- The interior product is additive in the form argument: $\iota_X(\alpha + \beta) = \iota_X \alpha + \iota_X \beta$. -/
lemma manifoldIota_add (X : ManifoldVF I M) {p : ℕ}
    (α β : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (α + β) = manifoldIota I X α + manifoldIota I X β := by
  ext x
  simp [manifoldIota]

/-- The interior product is $\mathbb{R}$-linear: $\iota_X(r \cdot \alpha) = r \cdot \iota_X \alpha$. -/
lemma manifoldIota_smul (X : ManifoldVF I M) {p : ℕ}
    (r : ℝ) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (r • α) = r • manifoldIota I X α := by
  ext x
  simp [manifoldIota]


/-- $\iota_X$ commutes with multiplication by a scalar function: $\iota_X(f \cdot \alpha) = f \cdot \iota_X \alpha$. -/
lemma manifoldIota_fMul (X : ManifoldVF I M) {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (manifoldFMul I f α) =
    manifoldFMul I f (manifoldIota I X α) := by
  ext x; simp [manifoldIota, manifoldFMul]

/-- **Graded Leibniz rule** for $\iota_X$ on a wedge $w \wedge \alpha$ with $w$ a $1$-form:
$$\iota_X(w \wedge \alpha) = (\iota_X w) \cdot \alpha - w \wedge \iota_X \alpha.$$ -/
lemma manifoldIota_wedge1 (X : ManifoldVF I M) {p : ℕ}
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (manifoldWedge1 I w α) =
    manifoldFMul I (manifoldIota I X w) α - manifoldWedge1 I w (manifoldIota I X α) := by
  funext x
  show (wedgePointwiseGeneral (w x) (α x)).curryLeft (X x) =
    ((w x).curryLeft (X x) Fin.elim0) • (α x) - wedgePointwiseGeneral (w x) ((α x).curryLeft (X x))
  unfold wedgePointwiseGeneral
  rw [curryLeft_alternatizeUncurryFin_smulRight]
  congr 1
  rw [oneFormToCL_apply_eq]
  simp [ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Degenerate case of $\iota_X$ on $w \wedge g$ when $g \in \Omega^0$: the second
correction term vanishes, yielding $\iota_X(w \wedge g) = (\iota_X w) \cdot g$. -/
lemma manifoldIota_wedge1_zero (X : ManifoldVF I M)
    (w : ManifoldΩ I M 1) (g : ManifoldΩ I M 0) :
    manifoldIota I X (manifoldWedge1 I w g) =
    manifoldFMul I (manifoldIota I X w) g := by
  funext x; ext u
  show (wedgePointwiseGeneral (w x) (g x)).curryLeft (X x) u =
    ((w x).curryLeft (X x) Fin.elim0) • (g x) u
  unfold wedgePointwiseGeneral
  rw [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, Matrix.cons_val_zero]
  rw [oneFormToCL_apply_eq]
  have hrem : Fin.removeNth 0 (Matrix.vecCons (X x) u) = u := by
    ext ⟨k, hk⟩; exact Fin.elim0 ⟨k, by omega⟩
  rw [hrem, ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Multiplication by a function distributes over form addition: $f \cdot (\alpha + \beta) = f \cdot \alpha + f \cdot \beta$. -/
lemma manifoldFMul_add_right {p : ℕ} (f : ManifoldΩ I M 0)
    (α β : ManifoldΩ I M p) :
    manifoldFMul I f (α + β) = manifoldFMul I f α + manifoldFMul I f β := by
  ext x
  simp [manifoldFMul, smul_add]






/-- Auxiliary scalar function: fix the slot $i$ and the remaining vectors `Fin.removeNth i vs`,
viewing $\alpha$ as a function of the base point $y$ that evaluates to a real number. Useful
for differentiating $\alpha$ in the base variable. -/
noncomputable def fixOtherSlots {p : ℕ} (α : ManifoldΩ I M p)
    (i : Fin (p + 1)) (vs : Fin (p + 1) → E) : M → ℝ :=
  fun y => (α y) (Fin.removeNth i vs)

end Operations



section TermB

open VectorField

/-- **The Lie bracket of two constant vector fields is zero**: $[V, W] = 0$ when $V, W$
are constant functions on $E$, since their derivatives vanish. -/
theorem lieBracket_constVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (x : E) :
    lieBracket ℝ (fun _ : E => v) (fun _ : E => w) x = 0 := by
  simp [lieBracket, fderiv_const_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The "Lie-bracket term" appearing in the invariant Cartan formula for $d\alpha$:
$$\sum_{i < j} (-1)^{i+j} \, \alpha([V_i, V_j], V_0, \dots, \hat V_i, \dots, \hat V_j, \dots).$$
For constant vector fields this term vanishes by `lieBracket_constVF`. -/
noncomputable def termB {p : ℕ} (α : ManifoldΩ I M (p + 1))
    (x : M) (vs : Fin (p + 2) → E) : ℝ :=
  ∑ ij ∈ Finset.filter (fun ij : Fin (p + 2) × Fin (p + 2) => ij.1 < ij.2) Finset.univ,
    (-1 : ℝ) ^ ((ij.1 : ℕ) + (ij.2 : ℕ)) *
      (α x) (Fin.cons
        (lieBracket ℝ (fun _ : E => vs ij.1) (fun _ : E => vs ij.2) 0)
        (fun _ => (0 : E)))

end TermB
