/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory Category Limits Finset

set_option maxHeartbeats 1600000

noncomputable section

universe v u

namespace Lec23DeltaFunctorDefs

/-- Definition 43 (δ-functor): A sequence of additive functors `(Tⁿ : A → B)_{n ≥ 0}` with
`T⁰` left exact, equipped with connecting maps `δⁿ : Tⁿ(X₃) → T^{n+1}(X₁)` for every short
exact sequence in `A`, fitting into long exact sequences that are natural in the SES. -/
structure DeltaFunctorDef43 (A : Type u) [Category.{v} A] [Abelian A]
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

attribute [instance] DeltaFunctorDef43.additive

/-- Definition 44 (universal δ-functor): A δ-functor `T` is universal if every natural
transformation `S⁰ → T⁰` from another δ-functor extends uniquely to a morphism of
δ-functors `S → T` compatible with all connecting homomorphisms. -/
structure IsUniversalDeltaFunctorDef44 {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (T : DeltaFunctorDef43 A B) : Prop where
  exists_hom : ∀ (S : DeltaFunctorDef43 A B) (η₀ : S.T 0 ⟶ T.T 0),
    ∃ (η : ∀ n, S.T n ⟶ T.T n),
      η 0 = η₀ ∧
      ∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁
  unique : ∀ (S : DeltaFunctorDef43 A B) (η₀ : S.T 0 ⟶ T.T 0)
    (η η' : ∀ n, S.T n ⟶ T.T n),
    η 0 = η₀ → η' 0 = η₀ →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁) →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η' n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η' (n + 1)).app SC.X₁) →
    ∀ n, η n = η' n

/-- The truncated Euler characteristic `∑_{i=0}^{d} (-1)^i · dims i`, used to compute
sheaf Euler characteristics from cohomological dimensions. -/
def alternatingSum (d : ℕ) (dims : ℕ → ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i * (dims i : ℤ)

/-- Axiomatic data of a (truncated) sheaf cohomology theory: a class of "sheaves" with
finite cohomological dimensions and an additivity axiom for the Euler characteristic
along short exact sequences. -/
structure SheafCohomologyData where
  k : Type*
  [field : Field k]
  CohSheaf : Type*
  d : ℕ
  cohomDim : CohSheaf → ℕ → ℕ
  cohom_vanishing : ∀ (F : CohSheaf) (i : ℕ), d < i → cohomDim F i = 0
  ShortExactSeq : CohSheaf → CohSheaf → CohSheaf → Prop
  eulerChar_additive : ∀ (F' F F'' : CohSheaf),
    ShortExactSeq F' F F'' →
    alternatingSum d (cohomDim F) =
      alternatingSum d (cohomDim F') + alternatingSum d (cohomDim F'')

attribute [instance] SheafCohomologyData.field

/-- The Euler characteristic of a sheaf `F`, the alternating sum of its cohomology
dimensions truncated at the cohomological dimension `d`. -/
def SheafCohomologyData.eulerChar (data : SheafCohomologyData) (F : data.CohSheaf) : ℤ :=
  alternatingSum data.d (data.cohomDim F)

/-- Additivity of the Euler characteristic on short exact sequences:
`χ(F) = χ(F') + χ(F'')`. -/
theorem SheafCohomologyData.eulerChar_add (data : SheafCohomologyData)
    (F' F F'' : data.CohSheaf)
    (hses : data.ShortExactSeq F' F F'') :
    data.eulerChar F = data.eulerChar F' + data.eulerChar F'' :=
  data.eulerChar_additive F' F F'' hses

end Lec23DeltaFunctorDefs
