/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite

set_option maxHeartbeats 800000

open CategoryTheory Category Limits

noncomputable section

universe v u

namespace Lec23

/-- A δ-functor `T = (Tⁿ)_{n ≥ 0} : A → B`: additive functors with `T⁰` left exact and
natural connecting homomorphisms `δⁿ` fitting into long exact sequences for every short
exact sequence of `A`. -/
structure DeltaFunctor (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type*) [Category B] [Abelian B] where
  T : ℕ → (A ⥤ B)
  additive : ∀ n, (T n).Additive
  leftExact : PreservesFiniteLimits (T 0)
  δ : ∀ (n : ℕ) (S : ShortComplex A), S.ShortExact →
    ((T n).obj S.X₃ ⟶ (T (n + 1)).obj S.X₁)
  δ_comp : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    δ n S hS ≫ (T (n + 1)).map S.f = 0
  comp_δ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (T n).map S.g ≫ δ n S hS = 0
  exact₁ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (ShortComplex.mk (δ n S hS) ((T (n + 1)).map S.f) (δ_comp n S hS)).Exact
  exact₂ : ∀ (n : ℕ) (S : ShortComplex A) (_hS : S.ShortExact),
    (ShortComplex.mk ((T n).map S.f) ((T n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₃ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (ShortComplex.mk ((T n).map S.g) (δ n S hS) (comp_δ n S hS)).Exact
  δ_natural : ∀ (n : ℕ) (S S' : ShortComplex A) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S ⟶ S'),
    (T n).map φ.τ₃ ≫ δ n S' hS' = δ n S hS ≫ (T (n + 1)).map φ.τ₁

attribute [instance] DeltaFunctor.additive

/-- A δ-functor `T` is universal if every natural transformation `S⁰ → T⁰` from another
δ-functor extends to a unique morphism of δ-functors `S → T`. -/
structure IsUniversalDeltaFunctor {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (T : DeltaFunctor A B) : Prop where
  exists_hom : ∀ (S : DeltaFunctor A B) (η₀ : S.T 0 ⟶ T.T 0),
    ∃ (η : ∀ n, S.T n ⟶ T.T n),
      η 0 = η₀ ∧
      ∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁
  unique : ∀ (S : DeltaFunctor A B) (η₀ : S.T 0 ⟶ T.T 0)
    (η η' : ∀ n, S.T n ⟶ T.T n),
    η 0 = η₀ → η' 0 = η₀ →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁) →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η' n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η' (n + 1)).app SC.X₁) →
    ∀ n, η n = η' n

/-- A δ-functor is effaceable if for every `n > 0` and every object `M`, there is a
monomorphism `M ↪ N` killed by `Tⁿ`. Grothendieck's criterion says effaceable δ-functors
are universal. -/
def DeltaFunctor.IsEffaceable {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (T : DeltaFunctor A B) : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (M : A),
    ∃ (N : A) (φ : M ⟶ N), Mono φ ∧ (T.T n).map φ = 0


/-- The higher right derived functors `R^{n+1}F` vanish on injective objects. -/
theorem rightDerived_vanishes_on_injectives
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    IsZero ((F.rightDerived (n + 1)).obj X) :=
  Functor.isZero_rightDerived_obj_injective_succ F n X

/-- In a category with enough injectives, the δ-functor `RF = (RⁿF)_{n ≥ 0}` is effaceable:
every object embeds into an injective on which `RⁿF` vanishes for `n > 0`. -/
theorem rightDerived_effaceable
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) (hn : 0 < n) (M : C) :
    ∃ (I : C) (φ : M ⟶ I), Mono φ ∧
      IsZero ((F.rightDerived n).obj I) := by
  obtain ⟨⟨J, _, f, _⟩⟩ := (inferInstance : EnoughInjectives C).presentation M
  refine ⟨J, f, ‹_›, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k J

/-- Proposition 42 (snake lemma): the connecting homomorphism
`Hⁱ(S.X₃) → Hʲ(S.X₁)` for a short exact sequence of complexes. -/
def prop42_connectingHom
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- Proposition 42 (long exact sequence): Exactness at `Hʲ(X₁)` in the homology long exact
sequence associated with a short exact sequence of complexes. -/
theorem prop42_exactness_at_X1
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (hS.δ i j hij) (HomologicalComplex.homologyMap S.f j)
      (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  hS.homology_exact₁ i j hij

/-- Proposition 42 (long exact sequence): Exactness at `Hⁱ(X₂)` in the homology long exact
sequence associated with a short exact sequence of complexes. -/
theorem prop42_exactness_at_X2
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp,
                S.zero, HomologicalComplex.homologyMap_zero])).Exact :=
  hS.homology_exact₂ i

/-- Proposition 42 (long exact sequence): Exactness at `Hⁱ(X₃)` in the homology long exact
sequence associated with a short exact sequence of complexes. -/
theorem prop42_exactness_at_X3
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.g i) (hS.δ i j hij)
      (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  hS.homology_exact₃ i j hij

/-- A (right) resolution of `M`: a cochain complex `K^•` together with a quasi-isomorphism
`(single₀ M) → K^•`. -/
structure Resolution {C : Type u} [Category.{v} C] [Abelian C] (M : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj M ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- Every injective resolution gives rise to a general resolution by forgetting injectivity. -/
def InjectiveResolution.toResolution
    {C : Type u} [Category.{v} C] [Abelian C] {M : C}
    (I : InjectiveResolution M) : Resolution M where
  cocomplex := I.cocomplex
  ι := I.ι

/-- `M` is adjusted to `F` (also called `F`-acyclic) if every higher right derived functor
of `F` vanishes on `M`. Such objects can replace injectives in computing `RⁿF`. -/
def IsAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) : Prop :=
  ∀ (i : ℕ), 0 < i → IsZero ((F.rightDerived i).obj M)

/-- Every injective object is `F`-acyclic for any additive functor `F`. -/
theorem injective_isAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) [Injective M] :
    IsAdjustedToFunctor F M := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k M

/-- The objects in an injective resolution are all `F`-acyclic. -/
theorem injRes_objects_adjusted
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M : C} (I : InjectiveResolution M) (n : ℕ) :
    IsAdjustedToFunctor F (I.cocomplex.X n) :=
  injective_isAdjustedToFunctor F (I.cocomplex.X n)



/-- The canonical identification `(RⁿF)(X) ≅ Hⁿ(F(I•))` for any injective resolution `I•` of `X`. -/
noncomputable def derived_functor_via_resolution
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

/-- An abelian category with enough injectives admits injective resolutions. -/
instance enoughInjectives_implies_hasInjectiveResolutions
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C] :
    HasInjectiveResolutions C :=
  inferInstance

/-- The zeroth right derived functor of a left exact additive functor `F` is naturally
isomorphic to `F` itself. -/
noncomputable def H0_iso_self
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F.rightDerived 0 ≅ F :=
  F.rightDerivedZeroIsoSelf

end Lec23
