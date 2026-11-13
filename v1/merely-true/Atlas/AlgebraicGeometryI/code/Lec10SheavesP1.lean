/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Multiset.Sort
import Mathlib.AlgebraicGeometry.Modules.Tilde

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Definition 21 (Lec 10): a presheaf of objects of `C` on a topological space `X` is
a contravariant functor from `Opens X` to `C`. -/
def presheaf_def (C : Type u) [Category.{v} C] (X : TopCat.{w}) :=
  TopCat.Presheaf C X

/-- Definition 23 (Lec 10): the pushforward functor `f_*` on presheaves induced by a
continuous map `f : X → Y`, sending `F` to `U ↦ F(f⁻¹U)`. -/
def pushforward_presheaf_def (C : Type u) [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C Y :=
  TopCat.Presheaf.pushforward C f

/-- The pushforward of a sheaf is again a sheaf, so `f_*` restricts to a functor on
sheaves. -/
theorem pushforward_sheaf_of_sheaf {C : Type u} [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y) {F : TopCat.Presheaf C X}
    (h : F.IsSheaf) : ((TopCat.Presheaf.pushforward C f).obj F).IsSheaf :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf f h

/-- Presheaves of abelian groups on `X` form an abelian category. -/
instance presheaf_category_abelian (X : TopCat.{u}) :
    Abelian (TopCat.Presheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- Sheaves of abelian groups on `X` form an abelian category. -/
instance sheaf_category_abelian (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- Proposition 15 (Lec 11): sheafification is a left adjoint and therefore preserves
all colimits. -/
instance sheafification_preserves_colimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasWeakSheafify J D] :
    PreservesColimitsOfSize.{v, v} (presheafToSheaf J D) :=
  (sheafificationAdjunction J D).leftAdjoint_preservesColimits

/-- If `P` is already a sheaf, then the canonical map `P → P#` to its sheafification
is an isomorphism. -/
theorem sheafification_iso_of_isSheaf
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {D : Type*} [Category D]
    [HasWeakSheafify J D]
    {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    IsIso (toSheafify J P) :=
  isIso_toSheafify J hP

/-- Exactness of a short complex of sheaves can be tested stalkwise: it is exact iff
each induced complex of stalks is exact. -/
theorem stalk_functor_exact
    {C : Type v} [Category.{u} C] [HasColimits C] [HasLimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)]
    [Abelian C]
    {X : TopCat.{u}} (S : ShortComplex (TopCat.Sheaf C X)) :
    S.Exact ↔ ∀ x : X,
      (S.map (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/-- Sheafification is exact: in addition to preserving colimits, it also preserves
finite limits. -/
instance sheafification_preserves_finite_limits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasSheafify J D] :
    PreservesFiniteLimits (presheafToSheaf J D) :=
  inferInstance

/-- The adjunction `M ↦ M̃ ⊣ Γ` between the tilde construction and global sections on
`Spec R`. -/
def tilde_gamma_adjunction (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- The tilde functor `M ↦ M̃` from `R`-modules to quasi-coherent sheaves on `Spec R`
is fully faithful. -/
def tilde_fullyFaithful (R : CommRingCat.{u}) :
    (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

/-- Instance: `tilde.functor R` is a left adjoint (to global sections on `Spec R`). -/
instance tilde_isLeftAdjoint_inst (R : CommRingCat.{u}) :
    (tilde.functor R).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

/-- Abstract axiomatization of locally free sheaves (= vector bundles) on `P¹_k`,
packaging rank, twisting sheaves `O(d)`, finite direct sums, and an isomorphism
relation. Used to formulate Grothendieck–Birkhoff splitting. -/
class ProjectiveLineBundle (k : Type u) [Field k] where
  LocallyFreeSheaf : Type u
  rank : LocallyFreeSheaf → ℕ
  twistingSheaf : ℤ → LocallyFreeSheaf
  directSum : (ι : Type) → [Fintype ι] → (ι → LocallyFreeSheaf) → LocallyFreeSheaf
  iso : LocallyFreeSheaf → LocallyFreeSheaf → Prop
  twistingSheaf_rank : ∀ d : ℤ, rank (twistingSheaf d) = 1
  iso_refl : ∀ E, iso E E
  iso_symm : ∀ E F, iso E F → iso F E
  iso_trans : ∀ E F G, iso E F → iso F G → iso E G









/-- Witness data that a sheaf of modules `M` is locally free of rank `n` (Def 26,
Lec 10): a covering family `{Xᵢ}` and, on each `Xᵢ`, an isomorphism between `M|_{Xᵢ}`
and the free sheaf of rank `n`. -/
structure SheafOfModules.LocallyFreeData
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}}
    [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    (M : SheafOfModules.{v} R) (n : ℕ) where
  I : Type u
  X : I → C
  coversTop : J.CoversTop X
  iso (i : I) : M.over (X i) ≅ SheafOfModules.free (ULift.{v} (Fin n))

/-- A sheaf of modules `M` is locally free of rank `n` (Def 26, Lec 10) if local
trivialization data exists, i.e. `M.LocallyFreeData n` is nonempty. -/
class SheafOfModules.IsLocallyFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}}
    [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    (M : SheafOfModules.{v} R) (n : ℕ) : Prop where
  nonempty_locallyFreeData : Nonempty (M.LocallyFreeData n)

/-- Scheme-theoretic version of locally free: there exists an open cover of `X` on
each piece of which `F` is isomorphic to the free `O_X`-module of rank `n`. -/
def AlgebraicGeometry.Scheme.IsLocallyFreeSheaf (X : Scheme.{u})
    (F : X.Modules) (n : ℕ) : Prop :=
  ∃ (𝒰 : @Scheme.OpenCover.{u} X), Nonempty (∀ (i : 𝒰.I₀),
    F.restrict (𝒰.f i) ≅
      @SheafOfModules.free.{u} (Opens (𝒰.X i)) _ _ (𝒰.X i).ringCatSheaf _ _ _
        (ULift.{u} (Fin n)))
