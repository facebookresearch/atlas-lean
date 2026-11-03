/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
import Atlas.GeometryOfManifolds.code.ArnoldConjecture
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false

noncomputable section

open scoped Manifold


section MfdKahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A symplectic form on a manifold: a smoothly varying nondegenerate antisymmetric bilinear form $\omega_x$ on each tangent space $T_x M$. -/
structure SymplecticFormOnMfd
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  ω : ∀ (x : M), TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  antisymm : ∀ (x : M) (u v : TangentSpace I x), ω x u v = -(ω x v u)
  nondegenerate : ∀ (x : M) (u : TangentSpace I x),
    (∀ v : TangentSpace I x, ω x u v = 0) → u = 0
  closed : True

variable {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Nijenhuis tensor field of an almost complex structure $J$: $N_J(U,V) = [JU, JV] - J[U, JV] - J[JU, V] - [U, V]$. -/
def nijenhuisTensorField [IsManifold I ⊤ M]
    (Jstr : AlmostComplexStructure I M)
    (U V : ∀ (x : M), TangentSpace I x) (x : M) : TangentSpace I x :=
  let JU : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (U y)
  let JV : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (V y)
  VectorField.mlieBracket I JU JV x
    - Jstr.J x (VectorField.mlieBracket I U JV x)
    - Jstr.J x (VectorField.mlieBracket I JU V x)
    - VectorField.mlieBracket I U V x

/-- An almost complex structure is integrable (i.e., a complex structure) when its Nijenhuis tensor vanishes identically. -/
structure IsIntegrableACS [IsManifold I ⊤ M]
    (Jstr : AlmostComplexStructure I M) : Prop where
  nijenhuis_vanishes : ∀ (U V : ∀ x : M, TangentSpace I x) (x : M),
    nijenhuisTensorField Jstr U V x = 0

/-- $J$ is compatible with $\omega$: $\omega(JU, JV) = \omega(U, V)$ and $\omega(u, Ju) > 0$ for $u \ne 0$ (taming). -/
structure IsCompatibleMfd [IsManifold I ⊤ M]
    (ω : SymplecticFormOnMfd I M) (Jstr : AlmostComplexStructure I M) : Prop where
  preserves : ∀ (x : M) (u v : TangentSpace I x),
    ω.ω x (Jstr.J x u) (Jstr.J x v) = ω.ω x u v
  taming : ∀ (x : M) (u : TangentSpace I x), u ≠ 0 → ω.ω x u (Jstr.J x u) > 0

/-- A Kähler structure on $M$: a symplectic form $\omega$ and an integrable almost complex structure $J$ that are compatible. -/
structure KahlerStructure
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] where
  ω : SymplecticFormOnMfd I M
  J : AlmostComplexStructure I M
  integrable : IsIntegrableACS J
  compatible : IsCompatibleMfd ω J

end MfdKahler


section DFSKahler
open DifferentialFormSpace


/-- The Nijenhuis tensor of an almost complex structure $J$, packaged as a bilinear vector-field-valued operation $N(U, V)$ that is antisymmetric on $1$-forms. -/
structure NijenhuisTensor
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  N : VF → VF → VF
  antisymm : ∀ (u v : VF) (α : Ω 1),
    inst.ι (N u v) α = -(inst.ι (N v u) α)


/-- `nij` represents the Nijenhuis tensor of $J$, i.e. it equals $[JX, JY] - J[JX, Y] - J[X, JY] - [X, Y]$ as evaluated on $1$-forms. -/
structure IsNijenhuisOf
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) : Prop where
  nijenhuis_eq : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (nij.N X Y) α =
      inst.ι (hbr.bracket (J.J X) (J.J Y)) α
      - inst.ι (J.J (hbr.bracket (J.J X) Y)) α
      - inst.ι (J.J (hbr.bracket X (J.J Y))) α
      - inst.ι (hbr.bracket X Y) α
  nijenhuis_eq_J : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (J.J (nij.N X Y)) α =
      inst.ι (J.J (hbr.bracket (J.J X) (J.J Y))) α
      - inst.ι (J.J (J.J (hbr.bracket (J.J X) Y))) α
      - inst.ι (J.J (J.J (hbr.bracket X (J.J Y)))) α
      - inst.ι (J.J (hbr.bracket X Y)) α


/-- The almost complex structure $J$ is integrable when its Nijenhuis tensor vanishes when paired with any $1$-form. -/
structure IsIntegrable
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) : Prop where
  vanishes : ∀ (u v : VF) (α : Ω 1), inst.ι (nij.N u v) α = 0


/-- A symplectic manifold $(M, \omega)$ together with $J$ is Kähler when $J$ is an integrable almost complex structure compatible with $\omega$. -/
structure IsKahler
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst)) : Prop where
  integrable : ∃ nij : NijenhuisTensor J, IsNijenhuisOf J nij ∧ IsIntegrable J nij
  compatible : IsCompatibleACS S J


/-- The Dolbeault operators $\partial$ and $\bar\partial$ on a complex manifold, satisfying $d = \partial + \bar\partial$, $\partial^2 = 0$, $\bar\partial^2 = 0$. -/
structure DolbeaultOps
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  del : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  delbar : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  decomp : ∀ {p : ℕ} (α : Ω p), inst.d α = del α + delbar α
  del_sq : ∀ {p : ℕ} (α : Ω p), del (del α) = 0
  delbar_sq : ∀ {p : ℕ} (α : Ω p), delbar (delbar α) = 0
  delbar_add : ∀ {p : ℕ} (α β : Ω p), delbar (α + β) = delbar α + delbar β
  delbar_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), delbar (r • α) = r • delbar α


/-- A function $\varphi$ is strictly plurisubharmonic when the $(1,1)$-form $\partial\bar\partial\varphi$ is nondegenerate as a pairing on vector fields. -/
class IsStrictlyPlurisubharmonic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) (φ : Ω 0) : Prop where
  nondeg : Function.Injective (fun (X : VF) => inst.ι X (dol.del (dol.delbar φ)))


/-- Interior product distributes over subtraction: $\iota_X(a - b) = \iota_X a - \iota_X b$. -/
lemma DifferentialFormSpace.ι_sub
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (X : VF) {p : ℕ} (a b : Ω (p + 1)) :
    inst.ι X (a - b) = inst.ι X a - inst.ι X b := by
  have h1 : a - b = a + (-1 : ℝ) • b := by rw [neg_one_smul]; abel
  rw [h1, inst.ι_add X a ((-1 : ℝ) • b), inst.ι_smul X (-1 : ℝ) b]
  rw [neg_one_smul, sub_eq_add_neg]

/-- The exterior derivative on $0$-forms commutes with negation: $d(-f) = -df$. -/
lemma DifferentialFormSpace.d_neg_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (f : Ω 0) : inst.d (-f) = -(inst.d f) := by
  have h1 : -f = (-1 : ℝ) • f := by rw [neg_one_smul]
  rw [h1, inst.d_smul (-1) f, neg_one_smul]

/-- Interior product commutes with negation: $\iota_X(-g) = -\iota_X g$. -/
lemma DifferentialFormSpace.ι_neg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (X : VF) {p : ℕ} (g : Ω (p + 1)) : inst.ι X (-g) = -(inst.ι X g) := by
  have h1 : -g = (-1 : ℝ) • g := by rw [neg_one_smul]
  rw [h1, inst.ι_smul X (-1 : ℝ) g, neg_one_smul]


/-- Raw form of the key identity: a particular combination of $\iota_X\iota_Y(d\alpha)$ and $\iota_X\iota_Y(d\beta)$ equals $\iota_{N(u,v)}\alpha$, expressing $d|_{(2,0)}$ as the Nijenhuis dual. -/
theorem nijenhuis_dual_eq_dForm_20_re_raw
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) (h : IsNijenhuisOf J nij)
    (α β : Ω 1)
    (htype : ∀ (X : VF), inst.ι X β = inst.ι (J.J X) α)
    (u v : VF) :
    inst.ι v (inst.ι u (inst.d α)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d α))
    + inst.ι (J.J v) (inst.ι u (inst.d β)) + inst.ι v (inst.ι (J.J u) (inst.d β))
    = inst.ι (nij.N u v) α := by
  have key : ∀ (X Y : VF) (ω : Ω 1),
      inst.ι Y (inst.ι X (inst.d ω)) =
        inst.ι X (inst.d (inst.ι Y ω)) - inst.ι Y (inst.d (inst.ι X ω))
        - inst.ι (hbr.bracket X Y) ω := by
    intro X Y ω
    have hcartan : inst.ι X (inst.d ω) = inst.L X ω - inst.d (inst.ι X ω) := by
      have hc := cartan_formula X ω; rw [hc]; abel
    rw [hcartan, DifferentialFormSpace.ι_sub]
    have hbracket : inst.ι Y (inst.L X ω) =
        inst.L X (inst.ι Y ω) - inst.ι (hbr.bracket X Y) ω := by
      have hb := hbr.bracket_ι_eq X Y ω; rw [hb]; abel
    rw [hbracket, inst.L_zero_eq_ι_d X (inst.ι Y ω)]
    abel
  rw [key u v α, key (J.J u) (J.J v) α, key u (J.J v) β, key (J.J u) v β]
  simp only [htype]
  simp only [J.sq_neg_id]
  simp only [DifferentialFormSpace.d_neg_zero, DifferentialFormSpace.ι_neg]
  rw [h.nijenhuis_eq u v α]
  abel


/-- A $(0,1)$-form represented by real and imaginary $1$-forms $(\mathrm{re}, \mathrm{im})$ satisfying the type condition $\iota_X \mathrm{im} = \iota_{JX} \mathrm{re}$. -/
structure Form01
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  re : Ω 1
  im : Ω 1
  type_cond : ∀ (X : VF), inst.ι X im = inst.ι (J.J X) re

/-- The real part of the $(2,0)$-projection of $df$ for a $(0,1)$-form $f$, evaluated on a pair of vector fields $(u, v)$. -/
def dForm_20_proj
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι v (inst.ι u (inst.d f.re)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d f.re))
  + inst.ι (J.J v) (inst.ι u (inst.d f.im)) + inst.ι v (inst.ι (J.J u) (inst.d f.im))

/-- The imaginary part of the $(2,0)$-projection of $df$ for a $(0,1)$-form $f$, evaluated on a pair of vector fields $(u, v)$. -/
def dForm_20_proj_im
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι v (inst.ι u (inst.d f.im)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d f.im))
  - inst.ι v (inst.ι (J.J u) (inst.d f.re)) - inst.ι (J.J v) (inst.ι u (inst.d f.re))

/-- Evaluation of the Nijenhuis dual on the real part of $f$: $\iota_{N(u,v)} f_{\mathrm{re}}$. -/
def nijenhuis_dual_eval
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (nij : NijenhuisTensor J) (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι (nij.N u v) f.re

/-- Evaluation of the Nijenhuis dual on the imaginary part of $f$: $\iota_{N(u,v)} f_{\mathrm{im}}$. -/
def nijenhuis_dual_eval_im
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (nij : NijenhuisTensor J) (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι (nij.N u v) f.im

/-- For a $(0,1)$-form $f$, the real part of the $(2,0)$-projection of $df$ equals the Nijenhuis dual evaluation on $f_{\mathrm{re}}$. -/
theorem nijenhuis_dual_eq_dForm_20_proj_re
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) (h : IsNijenhuisOf J nij)
    (f : Form01 J) (u v : VF) :
    dForm_20_proj J f u v = nijenhuis_dual_eval nij f u v :=
  nijenhuis_dual_eq_dForm_20_re_raw J nij h f.re f.im f.type_cond u v


/-- Raw form of the imaginary identity expressing the $(2,0)$-projection in terms of $\iota_{J\,N(u,v)}\alpha$. -/
theorem nijenhuis_dual_eq_dForm_20_im_raw
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) (h : IsNijenhuisOf J nij)
    (α β : Ω 1)
    (htype : ∀ (X : VF), inst.ι X β = inst.ι (J.J X) α)
    (u v : VF) :
    inst.ι v (inst.ι u (inst.d β)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d β))
    - inst.ι v (inst.ι (J.J u) (inst.d α)) - inst.ι (J.J v) (inst.ι u (inst.d α))
    = inst.ι (J.J (nij.N u v)) α := by
  have key : ∀ (X Y : VF) (ω : Ω 1),
      inst.ι Y (inst.ι X (inst.d ω)) =
        inst.ι X (inst.d (inst.ι Y ω)) - inst.ι Y (inst.d (inst.ι X ω))
        - inst.ι (hbr.bracket X Y) ω := by
    intro X Y ω
    have hcartan : inst.ι X (inst.d ω) = inst.L X ω - inst.d (inst.ι X ω) := by
      have hc := cartan_formula X ω; rw [hc]; abel
    rw [hcartan, DifferentialFormSpace.ι_sub]
    have hbracket : inst.ι Y (inst.L X ω) =
        inst.L X (inst.ι Y ω) - inst.ι (hbr.bracket X Y) ω := by
      have hb := hbr.bracket_ι_eq X Y ω; rw [hb]; abel
    rw [hbracket, inst.L_zero_eq_ι_d X (inst.ι Y ω)]
    abel
  rw [key u v β, key (J.J u) (J.J v) β, key (J.J u) v α, key u (J.J v) α]
  simp only [htype]
  simp only [J.sq_neg_id]
  simp only [DifferentialFormSpace.d_neg_zero, DifferentialFormSpace.ι_neg]
  rw [h.nijenhuis_eq_J u v α]
  simp only [J.sq_neg_id]
  abel

/-- The imaginary part of the $(2,0)$-projection of $df$ equals the Nijenhuis dual evaluation on $f_{\mathrm{im}}$. -/
theorem nijenhuis_dual_eq_dForm_20_proj_im
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) (h : IsNijenhuisOf J nij)
    (f : Form01 J) (u v : VF) :
    dForm_20_proj_im J f u v = nijenhuis_dual_eval_im nij f u v := by
  unfold dForm_20_proj_im nijenhuis_dual_eval_im
  rw [f.type_cond (nij.N u v)]
  exact nijenhuis_dual_eq_dForm_20_im_raw J nij h f.re f.im f.type_cond u v


/-- Typed version: the Nijenhuis dual map equals the $(2,0)$-projection of $d$ on a $(0,1)$-form. -/
theorem nijenhuis_dual_map_is_d_20_typed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) (h : IsNijenhuisOf J nij)
    (f : Form01 J) (u v : VF) :
    dForm_20_proj J f u v = nijenhuis_dual_eval nij f u v :=
  nijenhuis_dual_eq_dForm_20_proj_re J nij h f u v

end DFSKahler
