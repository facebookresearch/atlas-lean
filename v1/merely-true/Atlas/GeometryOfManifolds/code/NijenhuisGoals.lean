/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.KahlerManifolds

set_option autoImplicit false
set_option maxHeartbeats 800000

open DifferentialFormSpace


/-- Existence of holomorphic coordinates for an almost complex structure $J$: a chart $\varphi$
in which $J$ intertwines with a pointwise complex structure $J_{\mathrm{loc}}^*$ on 1-forms,
Lie brackets of vector fields pull back to act trivially on pulled-back forms, and pulled-back
forms separate vector fields. -/
structure HasHolomorphicCoords
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst)) : Prop where
  holo_coords :
    ∃ (Ω_loc : ℕ → Type) (VF_loc : Type)
      (inst_loc : DifferentialFormSpace Ω_loc VF_loc)
      (_J_loc : @AlmostComplexStr Ω_loc VF_loc inst_loc)
      (φ : @DFSMorphism Ω VF Ω_loc VF_loc inst inst_loc)
      (J_loc_star : Ω_loc 1 → Ω_loc 1),

      (∀ (X : VF) (α : Ω_loc 1),
        inst.ι (J.J X) (φ.pullback α) = inst.ι X (φ.pullback (J_loc_star α))) ∧

      (∀ (α : Ω_loc 1), J_loc_star (J_loc_star α) = -α) ∧


      (∀ (X Y : VF) (α_loc : Ω_loc 1),
        inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0) ∧


      (∀ (Z : VF),
        (∀ (α_loc : Ω_loc 1), inst.ι Z (φ.pullback α_loc) = 0) →
        ∀ (β : Ω 1), inst.ι Z β = 0)

/-- Computation lemma: in holomorphic coordinates, the Nijenhuis-tensor expression
$[JX, JY] - J[JX, Y] - J[X, JY] - [X, Y]$ pulls back to zero against any local 1-form. -/
theorem nijenhuis_expr_vanishes_on_pullback
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    {Ω_loc : ℕ → Type} {VF_loc : Type}
    {inst_loc : DifferentialFormSpace Ω_loc VF_loc}
    (φ : @DFSMorphism Ω VF Ω_loc VF_loc inst inst_loc)
    (J_loc_star : Ω_loc 1 → Ω_loc 1)
    (h_holo : ∀ (X : VF) (α : Ω_loc 1),
      inst.ι (J.J X) (φ.pullback α) = inst.ι X (φ.pullback (J_loc_star α)))
    (h_flat : ∀ (X Y : VF) (α_loc : Ω_loc 1),
      inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0)
    (X Y : VF) (α_loc : Ω_loc 1) :
    inst.ι (hbr.bracket (J.J X) (J.J Y)) (φ.pullback α_loc)
    - inst.ι (J.J (hbr.bracket (J.J X) Y)) (φ.pullback α_loc)
    - inst.ι (J.J (hbr.bracket X (J.J Y))) (φ.pullback α_loc)
    - inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0 := by

  have h1 : inst.ι (hbr.bracket (J.J X) (J.J Y)) (φ.pullback α_loc) = 0 :=
    h_flat (J.J X) (J.J Y) α_loc


  have h2 : inst.ι (J.J (hbr.bracket (J.J X) Y)) (φ.pullback α_loc) = 0 := by
    rw [h_holo (hbr.bracket (J.J X) Y) α_loc]
    exact h_flat (J.J X) Y (J_loc_star α_loc)


  have h3 : inst.ι (J.J (hbr.bracket X (J.J Y))) (φ.pullback α_loc) = 0 := by
    rw [h_holo (hbr.bracket X (J.J Y)) α_loc]
    exact h_flat X (J.J Y) (J_loc_star α_loc)

  have h4 : inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0 :=
    h_flat X Y α_loc

  rw [h1, h2, h3, h4]
  simp


/-- Proposition 3 (one direction): if $J$ admits holomorphic coordinates then $J$ is integrable,
i.e. the Nijenhuis tensor vanishes, $N_J = 0$. -/
theorem isIntegrable_of_hasHolomorphicCoords
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J)
    (h_nij : IsNijenhuisOf J nij)
    (hJ : HasHolomorphicCoords J) :
    IsIntegrable J nij := by
  constructor
  intro u v β

  obtain ⟨Ω_loc, VF_loc, inst_loc, _J_loc, φ, J_loc_star,
         h_holo, _h_sq, h_flat, h_nondeg⟩ := hJ.holo_coords


  have h_pullback_zero : ∀ (α_loc : Ω_loc 1),
      inst.ι (nij.N u v) (φ.pullback α_loc) = 0 := by
    intro α_loc

    rw [h_nij.nijenhuis_eq u v (φ.pullback α_loc)]

    exact nijenhuis_expr_vanishes_on_pullback J φ J_loc_star h_holo h_flat u v α_loc

  exact h_nondeg (nij.N u v) h_pullback_zero β


section MfdGoal39

namespace MfdNijenhuis

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An almost complex structure on a manifold: a pointwise endomorphism $J_x: T_x M \to T_x M$
with $J_x^2 = -\mathrm{id}$. -/
structure ACSOnMfd (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  J : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  sq_neg : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v

/-- The Nijenhuis tensor on a manifold: $N_J(U, V) = [JU, JV] - J[U, JV] - J[JU, V] - [U, V]$. -/
noncomputable def nijenhuisTensorMfd (Jstr : ACSOnMfd I M) (U V : ∀ x : M, TangentSpace I x)
    (x : M) : TangentSpace I x :=
  VectorField.mlieBracket I (fun y => Jstr.J y (U y)) (fun y => Jstr.J y (V y)) x
    - Jstr.J x (VectorField.mlieBracket I U (fun y => Jstr.J y (V y)) x)
    - Jstr.J x (VectorField.mlieBracket I (fun y => Jstr.J y (U y)) V x)
    - VectorField.mlieBracket I U V x

/-- A $(0,1)$-form on a manifold with almost complex structure $J$: real and imaginary parts
$\alpha = \mathrm{re} + i\, \mathrm{im}$ satisfying the type condition
$\mathrm{im}(X) = \mathrm{re}(JX)$, so $\alpha \in \wedge^{0,1} T^*M$. -/
structure Form01OnMfd (Jstr : ACSOnMfd I M) where
  re : ∀ x : M, TangentSpace I x →L[ℝ] ℝ
  im : ∀ x : M, TangentSpace I x →L[ℝ] ℝ
  type_cond : ∀ (X : ∀ x : M, TangentSpace I x) (x : M),
    (im x) (X x) = (re x) (Jstr.J x (X x))

/-- Cartan-calculus data on a manifold: an evaluation map for $d\alpha(X, Y)$ via the Cartan
formula $d\alpha(X, Y) = X(\alpha(Y)) - Y(\alpha(X)) - \alpha([X, Y])$, the Lie derivative on
functions, and the $(2,0)$-component $(d\alpha)^{(2,0)}$ of $d$ applied to a $(0,1)$-form. -/
structure CartanDataOnMfd (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (Jstr : ACSOnMfd I M) where
  d_eval : (∀ x : M, TangentSpace I x →L[ℝ] ℝ) →
    (∀ x : M, TangentSpace I x) → (∀ x : M, TangentSpace I x) → M → ℝ
  lieD : (∀ x : M, TangentSpace I x) → (M → ℝ) → M → ℝ
  cartan : ∀ (α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : ∀ x : M, TangentSpace I x) (x : M),
    d_eval α X Y x =
      lieD X (fun y => (α y) (Y y)) x
      - lieD Y (fun y => (α y) (X y)) x
      - (α x) (VectorField.mlieBracket I X Y x)
  lieD_sub : ∀ (X : ∀ x : M, TangentSpace I x) (f g : M → ℝ) (x : M),
    lieD X (fun y => f y - g y) x = lieD X f x - lieD X g x
  lieD_neg : ∀ (X : ∀ x : M, TangentSpace I x) (f : M → ℝ) (x : M),
    lieD X (fun y => -(f y)) x = -(lieD X f x)
  d_antisymm : ∀ (α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : ∀ x : M, TangentSpace I x) (x : M),
    d_eval α X Y x = -(d_eval α Y X x)
  dForm20 : Form01OnMfd Jstr → ∀ x : M, TangentSpace I x [⋀^Fin 2]→ₗ[ℝ] ℝ
  dForm20_eval : ∀ (f : Form01OnMfd Jstr) (U V : ∀ x : M, TangentSpace I x) (x : M),
    (dForm20 f x) ![U x, V x] =
      d_eval f.re U V x
      - d_eval f.re (fun y => Jstr.J y (U y)) (fun y => Jstr.J y (V y)) x
      + d_eval f.im U (fun y => Jstr.J y (V y)) x
      + d_eval f.im (fun y => Jstr.J y (U y)) V x

/-- Evaluation of the dual Nijenhuis map $N^*\alpha(U, V) = \alpha(N_J(U, V))$ — pair the
$(0,1)$-form's real part with the Nijenhuis tensor. -/
noncomputable def nijDualEvalOnMfd (Jstr : ACSOnMfd I M)
    (f : Form01OnMfd Jstr) (U V : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  (f.re x) (nijenhuisTensorMfd Jstr U V x)

/-- Proposition 4: the dual Nijenhuis map equals the $(2,0)$-component of the exterior derivative
on $(0,1)$-forms, $N^*\alpha = (d\alpha)^{(2,0)}$, i.e.
$\alpha(N_J(U, V)) = (d\alpha)^{(2,0)}(U, V)$. -/
theorem nijenhuis_dual_map_is_d_20_typed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (Jstr : ACSOnMfd I M) (ops : CartanDataOnMfd I M Jstr)
    (f : Form01OnMfd Jstr) (U V : ∀ x : M, TangentSpace I x) (x : M) :
    (ops.dForm20 f x) ![U x, V x] = nijDualEvalOnMfd Jstr f U V x := by

  rw [ops.dForm20_eval]
  unfold nijDualEvalOnMfd

  set JU := fun y => Jstr.J y (U y)
  set JV := fun y => Jstr.J y (V y)

  rw [ops.cartan f.re U V x, ops.cartan f.re JU JV x,
      ops.cartan f.im U JV x, ops.cartan f.im JU V x]


  have tc1 : ∀ y, (f.im y) (JV y) = -(f.re y) (V y) := by
    intro y; rw [f.type_cond JV y, Jstr.sq_neg, map_neg]
  have tc2 : ∀ y, (f.im y) (U y) = (f.re y) (Jstr.J y (U y)) :=
    fun y => f.type_cond U y
  have tc3 : ∀ y, (f.im y) (V y) = (f.re y) (Jstr.J y (V y)) :=
    fun y => f.type_cond V y
  have tc4 : ∀ y, (f.im y) (JU y) = -(f.re y) (U y) := by
    intro y; rw [f.type_cond JU y, Jstr.sq_neg, map_neg]

  have h_im_JV : (fun y => (f.im y) (JV y)) = (fun y => -(f.re y) (V y)) := funext tc1
  have h_im_U : (fun y => (f.im y) (U y)) = (fun y => (f.re y) (Jstr.J y (U y))) := funext tc2
  have h_im_V : (fun y => (f.im y) (V y)) = (fun y => (f.re y) (Jstr.J y (V y))) := funext tc3
  have h_im_JU : (fun y => (f.im y) (JU y)) = (fun y => -(f.re y) (U y)) := funext tc4
  have h_re_JV : (fun y => (f.re y) (JV y)) = (fun y => (f.re y) (Jstr.J y (V y))) := rfl
  have h_re_JU : (fun y => (f.re y) (JU y)) = (fun y => (f.re y) (Jstr.J y (U y))) := rfl
  rw [h_im_JV, h_im_U, h_im_V, h_im_JU, h_re_JV, h_re_JU]

  simp only [ops.lieD_neg]

  have tc_br1 : (f.im x) (VectorField.mlieBracket I U JV x) =
      (f.re x) (Jstr.J x (VectorField.mlieBracket I U JV x)) :=
    f.type_cond (fun z => VectorField.mlieBracket I U JV z) x
  have tc_br2 : (f.im x) (VectorField.mlieBracket I JU V x) =
      (f.re x) (Jstr.J x (VectorField.mlieBracket I JU V x)) :=
    f.type_cond (fun z => VectorField.mlieBracket I JU V z) x
  rw [tc_br1, tc_br2]

  unfold nijenhuisTensorMfd
  simp only [map_sub]

  ring

end MfdNijenhuis

end MfdGoal39
