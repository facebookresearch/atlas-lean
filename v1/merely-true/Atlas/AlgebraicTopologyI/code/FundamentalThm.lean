/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution

noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A resolution of an object `Z` in an abelian category: a chain complex equipped with a
quasi-isomorphism to the chain complex concentrated in degree zero on `Z`. -/
structure Resolution (Z : C) where
  complex : ChainComplex C ℕ
  [hasHomology : ∀ (i : ℕ), complex.HasHomology i]
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  [quasiIso : QuasiIso π]

namespace Resolution

variable {Z : C}

/-- The underlying complex of a resolution has homology objects in every degree. -/
instance (Q : Resolution Z) (i : ℕ) : Q.complex.HasHomology i := Q.hasHomology i
/-- The augmentation map of a resolution is a quasi-isomorphism. -/
instance (Q : Resolution Z) : QuasiIso Q.π := Q.quasiIso

/-- The composite of the differential `d : E₁ ⟶ E₀` followed by the augmentation `E₀ ⟶ Z`
vanishes, since the augmentation is a chain map into the complex concentrated in degree zero. -/
@[simp]
lemma complex_d_comp_π_f_zero (Q : Resolution Z) :
    Q.complex.d 1 0 ≫ Q.π.f 0 = 0 := by
  rw [← Q.π.comm 1 0, single_obj_d, comp_zero]

/-- In positive degree the augmentation map of a resolution is zero, since the target chain
complex is concentrated in degree zero. -/
theorem π_f_succ (Q : Resolution Z) (n : ℕ) : Q.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

/-- The cokernel cofork on `d : E₁ ⟶ E₀` given by the augmentation `π : E₀ ⟶ Z`. -/
noncomputable def cokernelCofork (Q : Resolution Z) :
    CokernelCofork (Q.complex.d 1 0) :=
  CokernelCofork.ofπ _ Q.complex_d_comp_π_f_zero

/-- The augmentation `π : E₀ ⟶ Z` exhibits `Z` as the cokernel of `d : E₁ ⟶ E₀`, since the
underlying complex is exact in degree zero as a consequence of `π` being a quasi-isomorphism. -/
noncomputable def isColimitCokernelCofork (Q : Resolution Z) :
    IsColimit Q.cokernelCofork := by
  refine IsColimit.ofIsoColimit (Q.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (Q.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt Q.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp [cokernelCofork]
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

/-- The short complex `E₁ ⟶ E₀ ⟶ Z` formed by the differential and the augmentation is exact. -/
lemma exact₀ (Q : Resolution Z) :
    (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0) Q.complex_d_comp_π_f_zero).Exact := by
  have : (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0)
    Q.complex_d_comp_π_f_zero).HasHomology := inferInstance
  exact ShortComplex.exact_of_g_is_cokernel _ Q.isColimitCokernelCofork

set_option backward.isDefEq.respectTransparency false in
/-- Every component of the augmentation of a resolution is an epimorphism. -/
instance epi_π_f (Q : Resolution Z) (n : ℕ) : Epi (Q.π.f n) := by
  cases n with
  | zero => exact epi_of_isColimit_cofork Q.isColimitCokernelCofork
  | succ n => rw [π_f_succ]; infer_instance

/-- The underlying chain complex of a resolution is exact in every positive degree. -/
lemma complex_exactAt_succ (Q : Resolution Z) (n : ℕ) :
    Q.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' Q.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

/-- The short complex `E_{n+2} ⟶ E_{n+1} ⟶ E_n` formed by consecutive differentials is exact,
expressing exactness of the resolution in positive degrees. -/
lemma exact_succ (Q : Resolution Z) (n : ℕ) :
    (ShortComplex.mk _ _ (Q.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n)
    (by simp only [prev]; rfl) (by simp)).1 (Q.complex_exactAt_succ n)

end Resolution

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero component of the lift of `f : Y ⟶ Z` to a chain map between resolutions:
factor `P.π.f 0 ≫ f` through the epi `Q.π.f 0`, using projectivity of `P.complex.X 0`. -/
def liftFZero {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-one component of the lift of `f` to a chain map: use exactness of `Q` at degree
zero together with projectivity of `P.complex.X 1` to lift `d ≫ liftFZero f P Q` along `d`. -/
def liftFOne {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q)
    (by simp [liftFZero])

/-- Commutativity of the lifted square in degree 1 ↔ 0: `liftFOne` and `liftFZero` form a
commuting square against the differentials. -/
@[simp]
theorem liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q :=
  Q.exact₀.liftFromProjective_comp _ _

/-- Inductive step in constructing the lift: given commuting squares in degrees `n` and `n+1`,
produce a degree-`n+2` lift that fits into the next commuting square. This uses exactness of `Q`
together with projectivity in degree `n+2`. -/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : Resolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n)
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- Existence half of Theorem 22.1 (Fundamental Theorem of Homological Algebra):
given `f : Y ⟶ Z`, a projective resolution of `Y`, and a resolution of `Z`, we obtain a chain
map `P.complex ⟶ Q.complex` lifting `f`, by assembling the degree-zero, degree-one, and
inductive degree-`n+2` components. -/
def lift {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

/-- The lift `lift f P Q` is compatible with the augmentations: composing it with `Q.π`
recovers `P.π` followed by the chain map induced by `f`. -/
@[reassoc (attr := simp)]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext
  simp [lift, liftFZero, liftFOne]

/-- Degree-zero component of the chain homotopy to zero: if a chain map `f : P → Q` becomes
zero after composing with `Q.π`, lift `f.f 0` along the differential `d : Q₁ ⟶ Q₀` using
exactness of `Q` at degree zero and projectivity of `P.complex.X 0`. -/
def liftHomotopyZeroZero {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

/-- The defining identity of `liftHomotopyZeroZero`: composing with the differential
`d : Q₁ ⟶ Q₀` recovers `f.f 0`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroZero_comp {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

/-- Degree-one component of the chain homotopy to zero: lift the corrected morphism
`f.f 1 - d ≫ liftHomotopyZeroZero f comm` along `d : Q₂ ⟶ Q₁` using exactness of `Q` in
positive degree and projectivity of `P.complex.X 1`. -/
def liftHomotopyZeroOne {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective
    (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
            liftHomotopyZeroZero_comp, sub_self])

/-- The defining identity of `liftHomotopyZeroOne`: composing with `d : Q₂ ⟶ Q₁` recovers
the corrected morphism `f.f 1 - d ≫ liftHomotopyZeroZero f comm`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroOne_comp {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

/-- Inductive step in building the chain homotopy to zero: given chain homotopy data in degrees
`n` and `n+1`, produce the next degree-`n+2` piece via exactness of `Q` in positive degree and
projectivity of `P.complex.X (n+2)`. -/
def liftHomotopyZeroSucc {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective
    (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

/-- The defining identity of `liftHomotopyZeroSucc`: composing with the differential recovers
the corrected morphism `f.f (n+2) - d ≫ g'`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroSucc_comp {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - P.complex.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- Any chain map `f : P → Q` from a projective resolution to a resolution that becomes zero
after composing with the augmentation `Q.π` is chain-homotopic to zero, by assembling the
degree-zero, degree-one, and inductive degree-`n+2` components. -/
def liftHomotopyZero {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

/-- Uniqueness half of Theorem 22.1 (Fundamental Theorem of Homological Algebra):
any two chain maps `g, h : P.complex ⟶ Q.complex` lifting the same `f : Y ⟶ Z` are chain
homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z)
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (g h : P.complex ⟶ Q.complex)
    (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    Homotopy g h :=
  Homotopy.equivSubZero.symm (liftHomotopyZero _ (by simp [g_comm, h_comm]))

end FundamentalThm
