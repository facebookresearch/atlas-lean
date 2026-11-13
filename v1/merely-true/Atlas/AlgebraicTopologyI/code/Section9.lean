/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequence
import Atlas.AlgebraicTopologyI.code.Section11

open CategoryTheory

namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- The connecting (boundary) homomorphism `∂ : Hᵢ(C) ⟶ Hⱼ(A)` associated with a short exact
sequence `0 → A → B → C → 0` of chain complexes, where `j` is the index reached from `i`
under the complex shape. This is the key map appearing in the homology long exact sequence
(Theorem 9.1). -/
noncomputable def connectingHomomorphism
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  ShortComplex.ShortExact.δ hS i j hij

/-- Exactness of the long exact sequence at the middle term `Hᵢ(B)`: the image of
`Hᵢ(A) → Hᵢ(B)` equals the kernel of `Hᵢ(B) → Hᵢ(C)` for a short exact sequence of
chain complexes. -/
theorem exact_f_g (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ hS i

/-- Exactness of the long exact sequence at `Hᵢ(C)`: the image of `Hᵢ(B) → Hᵢ(C)` equals
the kernel of the connecting map `∂ : Hᵢ(C) → Hⱼ(A)`. -/
theorem exact_g_δ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ hS i j hij

/-- Exactness of the long exact sequence at `Hⱼ(A)`: the image of the connecting map
`∂ : Hᵢ(C) → Hⱼ(A)` equals the kernel of `Hⱼ(A) → Hⱼ(B)`. -/
theorem exact_δ_f (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ hS i j hij

/-- Packaged data for the homology long exact sequence (Theorem 9.1): the connecting
homomorphism `δ` and the three exactness statements (at `Hᵢ(B)`, at `Hᵢ(C)`, and at
`Hⱼ(A)`) for a short exact sequence of chain complexes. -/
structure HomologyLongExactSequenceData (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) where
  δ : S.X₃.homology i ⟶ S.X₁.homology j
  exact_at_X₂ : (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact
  exact_at_X₃ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact
  exact_at_X₁ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact

/-- **Theorem 9.1** (Homology long exact sequence). Given a short exact sequence
`0 → A → B → C → 0` of chain complexes, there is a natural connecting homomorphism
`∂ : Hₙ(C) → Hₙ₋₁(A)` such that
`⋯ → Hₙ(A) → Hₙ(B) → Hₙ(C) →∂ Hₙ₋₁(A) → ⋯`
is exact. This bundles the connecting map together with exactness at each spot. -/
noncomputable def homologyLongExactSequence
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    HomologyLongExactSequenceData hS i j hij where
  δ := connectingHomomorphism hS i j hij
  exact_at_X₂ := exact_f_g hS i
  exact_at_X₃ := exact_g_δ hS i j hij
  exact_at_X₁ := exact_δ_f hS i j hij

end HomologyLongExactSequence

namespace FiveLemma

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}
variable [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
  [AddCommGroup A₄] [AddCommGroup A₅]
variable [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  [AddCommGroup B₄] [AddCommGroup B₅]

/-- **Proposition 9.4** (Five lemma). In a commutative ladder of two exact sequences of
five abelian groups, if the outer four vertical maps `f₁, f₂, f₄, f₅` are suitably
surjective/bijective/injective (here `f₁` surjective, `f₂` and `f₄` bijective, `f₅`
injective), then the middle map `f₃` is bijective. -/
theorem five_lemma
    (α₁ : A₁ →+ A₂) (α₂ : A₂ →+ A₃) (α₃ : A₃ →+ A₄) (α₄ : A₄ →+ A₅)
    (β₁ : B₁ →+ B₂) (β₂ : B₂ →+ B₃) (β₃ : B₃ →+ B₄) (β₄ : B₄ →+ B₅)
    (f₁ : A₁ →+ B₁) (f₂ : A₂ →+ B₂) (f₃ : A₃ →+ B₃) (f₄ : A₄ →+ B₄) (f₅ : A₅ →+ B₅)
    (hc₁ : β₁.comp f₁ = f₂.comp α₁)
    (hc₂ : β₂.comp f₂ = f₃.comp α₂)
    (hc₃ : β₃.comp f₃ = f₄.comp α₃)
    (hc₄ : β₄.comp f₄ = f₅.comp α₄)
    (hα₁ : Function.Exact α₁ α₂)
    (hα₂ : Function.Exact α₂ α₃)
    (hα₃ : Function.Exact α₃ α₄)
    (hβ₁ : Function.Exact β₁ β₂)
    (hβ₂ : Function.Exact β₂ β₃)
    (hβ₃ : Function.Exact β₃ β₄)
    (hf₁ : Function.Surjective f₁)
    (hf₂ : Function.Bijective f₂)
    (hf₄ : Function.Bijective f₄)
    (hf₅ : Function.Injective f₅) :
    Function.Bijective f₃ :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ f₁ f₂ f₃ f₄ f₅
    hc₁ hc₂ hc₃ hc₄ hα₁ hα₂ hα₃ hβ₁ hβ₂ hβ₃ hf₁ hf₂ hf₄ hf₅

/-- A "homology ladder": a commutative ladder of two long exact sequences (with maps
`i`, `p`, `δ` on each row) of graded abelian groups indexed by `ℤ`, together with
vertical chain maps `fMap`, `gMap`, `hMap` between corresponding groups. This is the
algebraic setup used to apply the five lemma degree-by-degree (Proposition 9.4). -/
structure HomologyLadder where
  HA : ℤ → Type*
  HB : ℤ → Type*
  HC : ℤ → Type*
  HA' : ℤ → Type*
  HB' : ℤ → Type*
  HC' : ℤ → Type*
  [grpHA : ∀ n, AddCommGroup (HA n)]
  [grpHB : ∀ n, AddCommGroup (HB n)]
  [grpHC : ∀ n, AddCommGroup (HC n)]
  [grpHA' : ∀ n, AddCommGroup (HA' n)]
  [grpHB' : ∀ n, AddCommGroup (HB' n)]
  [grpHC' : ∀ n, AddCommGroup (HC' n)]
  iMap : ∀ n, HA n →+ HB n
  pMap : ∀ n, HB n →+ HC n
  δ : ∀ n, HC (n + 1) →+ HA n
  iMap' : ∀ n, HA' n →+ HB' n
  pMap' : ∀ n, HB' n →+ HC' n
  δ' : ∀ n, HC' (n + 1) →+ HA' n
  fMap : ∀ n, HA n →+ HA' n
  gMap : ∀ n, HB n →+ HB' n
  hMap : ∀ n, HC n →+ HC' n
  exact_ip : ∀ n, Function.Exact (iMap n) (pMap n)
  exact_pδ : ∀ n, Function.Exact (pMap (n + 1)) (δ n)
  exact_δi : ∀ n, Function.Exact (δ n) (iMap n)
  exact_i'p' : ∀ n, Function.Exact (iMap' n) (pMap' n)
  exact_p'δ' : ∀ n, Function.Exact (pMap' (n + 1)) (δ' n)
  exact_δ'i' : ∀ n, Function.Exact (δ' n) (iMap' n)
  comm_fi : ∀ n, (iMap' n).comp (fMap n) = (gMap n).comp (iMap n)
  comm_gp : ∀ n, (pMap' n).comp (gMap n) = (hMap n).comp (pMap n)
  comm_hδ : ∀ n, (δ' n).comp (hMap (n + 1)) = (fMap n).comp (δ n)

attribute [instance] HomologyLadder.grpHA HomologyLadder.grpHB HomologyLadder.grpHC
  HomologyLadder.grpHA' HomologyLadder.grpHB' HomologyLadder.grpHC'

/-- In a homology ladder, if `fMap` and `gMap` are bijective in every degree, then so is
`hMap` (proved via the five lemma applied to a window of the ladder). -/
theorem HomologyLadder.h_bijective_of_f_g_bijective (L : HomologyLadder)
    (hf : ∀ n, Function.Bijective (L.fMap n))
    (hg : ∀ n, Function.Bijective (L.gMap n))
    (n : ℤ) : Function.Bijective (L.hMap (n + 1)) :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.iMap (n + 1)) (L.pMap (n + 1)) (L.δ n) (L.iMap n)
    (L.iMap' (n + 1)) (L.pMap' (n + 1)) (L.δ' n) (L.iMap' n)
    (L.fMap (n + 1)) (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n) (L.gMap n)
    (L.comm_fi (n + 1)) (L.comm_gp (n + 1)) (L.comm_hδ n) (L.comm_fi n)
    (L.exact_ip (n + 1)) (L.exact_pδ n) (L.exact_δi n)
    (L.exact_i'p' (n + 1)) (L.exact_p'δ' n) (L.exact_δ'i' n)
    (hf (n + 1)).2 (hg (n + 1)) (hf n) (hg n).1

/-- In a homology ladder, if `fMap` and `hMap` are bijective in every degree, then so is
`gMap` (proved via the five lemma applied to a window of the ladder). -/
theorem HomologyLadder.g_bijective_of_f_h_bijective (L : HomologyLadder)
    (hf : ∀ n, Function.Bijective (L.fMap n))
    (hh : ∀ n, Function.Bijective (L.hMap n))
    (n : ℤ) : Function.Bijective (L.gMap (n + 1)) :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.δ (n + 1)) (L.iMap (n + 1)) (L.pMap (n + 1)) (L.δ n)
    (L.δ' (n + 1)) (L.iMap' (n + 1)) (L.pMap' (n + 1)) (L.δ' n)
    (L.hMap (n + 1 + 1)) (L.fMap (n + 1)) (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n)
    (L.comm_hδ (n + 1)) (L.comm_fi (n + 1)) (L.comm_gp (n + 1)) (L.comm_hδ n)
    (L.exact_δi (n + 1)) (L.exact_ip (n + 1)) (L.exact_pδ n)
    (L.exact_δ'i' (n + 1)) (L.exact_i'p' (n + 1)) (L.exact_p'δ' n)
    (hh (n + 1 + 1)).2 (hf (n + 1)) (hh (n + 1)) (hf n).1

/-- In a homology ladder, if `gMap` and `hMap` are bijective in every degree, then so is
`fMap` (proved via the five lemma applied to a window of the ladder). -/
theorem HomologyLadder.f_bijective_of_g_h_bijective (L : HomologyLadder)
    (hg : ∀ n, Function.Bijective (L.gMap n))
    (hh : ∀ n, Function.Bijective (L.hMap n))
    (n : ℤ) : Function.Bijective (L.fMap n) :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.pMap (n + 1)) (L.δ n) (L.iMap n) (L.pMap n)
    (L.pMap' (n + 1)) (L.δ' n) (L.iMap' n) (L.pMap' n)
    (L.gMap (n + 1)) (L.hMap (n + 1)) (L.fMap n) (L.gMap n) (L.hMap n)
    (L.comm_gp (n + 1)) (L.comm_hδ n) (L.comm_fi n) (L.comm_gp n)
    (L.exact_pδ n) (L.exact_δi n) (L.exact_ip n)
    (L.exact_p'δ' n) (L.exact_δ'i' n) (L.exact_i'p' n)
    (hg (n + 1)).2 (hh (n + 1)) (hg n) (hh n).1

/-- A ladder of two long exact sequences (with maps `ι`, `π`, `δ` on each row), connected
by vertical maps `fA`, `fB`, `fC`. This is a streamlined presentation of the data needed
for the 2-out-of-3 isomorphism principle in homology (Corollary 9.5 and Proposition 9.6). -/
structure LongExactLadder where
  A  : ℤ → Type*
  A' : ℤ → Type*
  B  : ℤ → Type*
  B' : ℤ → Type*
  C  : ℤ → Type*
  C' : ℤ → Type*
  [grpA  : ∀ n, AddCommGroup (A n)]
  [grpA' : ∀ n, AddCommGroup (A' n)]
  [grpB  : ∀ n, AddCommGroup (B n)]
  [grpB' : ∀ n, AddCommGroup (B' n)]
  [grpC  : ∀ n, AddCommGroup (C n)]
  [grpC' : ∀ n, AddCommGroup (C' n)]
  ι  : ∀ n, A n →+ B n
  π  : ∀ n, B n →+ C n
  δ  : ∀ n, C (n + 1) →+ A n
  ι' : ∀ n, A' n →+ B' n
  π' : ∀ n, B' n →+ C' n
  δ' : ∀ n, C' (n + 1) →+ A' n
  fA : ∀ n, A n →+ A' n
  fB : ∀ n, B n →+ B' n
  fC : ∀ n, C n →+ C' n
  exact_δι : ∀ n, Function.Exact (δ n) (ι n)
  exact_ιπ : ∀ n, Function.Exact (ι n) (π n)
  exact_πδ : ∀ n, Function.Exact (π (n + 1)) (δ n)
  exact_δ'ι' : ∀ n, Function.Exact (δ' n) (ι' n)
  exact_ι'π' : ∀ n, Function.Exact (ι' n) (π' n)
  exact_π'δ' : ∀ n, Function.Exact (π' (n + 1)) (δ' n)
  comm_ι : ∀ n, (ι' n).comp (fA n) = (fB n).comp (ι n)
  comm_π : ∀ n, (π' n).comp (fB n) = (fC n).comp (π n)
  comm_δ : ∀ n, (δ' n).comp (fC (n + 1)) = (fA n).comp (δ n)

attribute [instance] LongExactLadder.grpA LongExactLadder.grpA' LongExactLadder.grpB
  LongExactLadder.grpB' LongExactLadder.grpC LongExactLadder.grpC'

namespace LongExactLadder

variable (L : LongExactLadder)

/-- In a long exact ladder, if `fA` and `fB` are bijective in every degree, then so is
`fC` in every degree. -/
theorem two_of_three_fC
    (hfA : ∀ n, Function.Bijective (L.fA n))
    (hfB : ∀ n, Function.Bijective (L.fB n))
    (n : ℤ) : Function.Bijective (L.fC n) := by
  have h : n = (n - 1) + 1 := by omega
  rw [h]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.ι (n - 1 + 1)) (L.π (n - 1 + 1)) (L.δ (n - 1)) (L.ι (n - 1))
    (L.ι' (n - 1 + 1)) (L.π' (n - 1 + 1)) (L.δ' (n - 1)) (L.ι' (n - 1))
    (L.fA (n - 1 + 1)) (L.fB (n - 1 + 1)) (L.fC (n - 1 + 1)) (L.fA (n - 1)) (L.fB (n - 1))
    (L.comm_ι (n - 1 + 1)) (L.comm_π (n - 1 + 1)) (L.comm_δ (n - 1)) (L.comm_ι (n - 1))
    (L.exact_ιπ (n - 1 + 1)) (L.exact_πδ (n - 1)) (L.exact_δι (n - 1))
    (L.exact_ι'π' (n - 1 + 1)) (L.exact_π'δ' (n - 1)) (L.exact_δ'ι' (n - 1))
    (hfA (n - 1 + 1)).2 (hfB (n - 1 + 1)) (hfA (n - 1)) (hfB (n - 1)).1

/-- Injectivity half of the 2-out-of-3 principle: if `fA` and `fC` are bijective in
every degree, then `fB` is injective in every degree. -/
theorem two_of_three_fB_inj
    (hfA : ∀ n, Function.Bijective (L.fA n))
    (hfC : ∀ n, Function.Bijective (L.fC n))
    (n : ℤ) : Function.Injective (L.fB n) :=
  AddMonoidHom.injective_of_surjective_of_injective_of_injective
    (L.δ n) (L.ι n) (L.π n)
    (L.δ' n) (L.ι' n) (L.π' n)
    (L.fC (n + 1)) (L.fA n) (L.fB n) (L.fC n)
    (L.comm_δ n) (L.comm_ι n) (L.comm_π n)
    (L.exact_δι n) (L.exact_ιπ n)
    (L.exact_δ'ι' n)
    (hfC (n + 1)).2 (hfA n).1 (hfC n).1

/-- Surjectivity half of the 2-out-of-3 principle (shifted form): if `fA` and `fC` are
bijective in every degree, then `fB (n+1)` is surjective. -/
theorem two_of_three_fB_surj_aux
    (hfA : ∀ n, Function.Bijective (L.fA n))
    (hfC : ∀ n, Function.Bijective (L.fC n))
    (n : ℤ) : Function.Surjective (L.fB (n + 1)) :=
  AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (L.ι (n + 1)) (L.π (n + 1)) (L.δ n)
    (L.ι' (n + 1)) (L.π' (n + 1)) (L.δ' n)
    (L.fA (n + 1)) (L.fB (n + 1)) (L.fC (n + 1)) (L.fA n)
    (L.comm_ι (n + 1)) (L.comm_π (n + 1)) (L.comm_δ n)
    (L.exact_πδ n) (L.exact_ι'π' (n + 1)) (L.exact_π'δ' n)
    (hfA (n + 1)).2 (hfC (n + 1)).2 (hfA n).1

/-- In a long exact ladder, if `fA` and `fC` are bijective in every degree, then so is
`fB` in every degree (combining the injectivity and surjectivity halves). -/
theorem two_of_three_fB
    (hfA : ∀ n, Function.Bijective (L.fA n))
    (hfC : ∀ n, Function.Bijective (L.fC n))
    (n : ℤ) : Function.Bijective (L.fB n) := by
  refine ⟨two_of_three_fB_inj L hfA hfC n, ?_⟩
  have h : n = (n - 1) + 1 := by omega
  rw [h]
  exact two_of_three_fB_surj_aux L hfA hfC (n - 1)

/-- In a long exact ladder, if `fB` and `fC` are bijective in every degree, then so is
`fA` in every degree. -/
theorem two_of_three_fA
    (hfB : ∀ n, Function.Bijective (L.fB n))
    (hfC : ∀ n, Function.Bijective (L.fC n))
    (n : ℤ) : Function.Bijective (L.fA n) :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (L.π (n + 1)) (L.δ n) (L.ι n) (L.π n)
    (L.π' (n + 1)) (L.δ' n) (L.ι' n) (L.π' n)
    (L.fB (n + 1)) (L.fC (n + 1)) (L.fA n) (L.fB n) (L.fC n)
    (L.comm_π (n + 1)) (L.comm_δ n) (L.comm_ι n) (L.comm_π n)
    (L.exact_πδ n) (L.exact_δι n) (L.exact_ιπ n)
    (L.exact_π'δ' n) (L.exact_δ'ι' n) (L.exact_ι'π' n)
    (hfB (n + 1)).2 (hfC (n + 1)) (hfB n) (hfC n).1

/-- **Corollary 9.5** (2-out-of-3 for chain maps). For a map of short exact sequences of
chain complexes presented as a long exact ladder, if any two of the three vertical maps
`fA`, `fB`, `fC` are isomorphisms in homology (bijective in every degree), then so is
the third. The same statement underlies **Proposition 9.6** for a map of pairs. -/
theorem two_of_three_iso
    (h : (∀ n, Function.Bijective (L.fA n)) ∧ (∀ n, Function.Bijective (L.fB n))
       ∨ (∀ n, Function.Bijective (L.fA n)) ∧ (∀ n, Function.Bijective (L.fC n))
       ∨ (∀ n, Function.Bijective (L.fB n)) ∧ (∀ n, Function.Bijective (L.fC n))) :
    (∀ n, Function.Bijective (L.fA n)) ∧
    (∀ n, Function.Bijective (L.fB n)) ∧
    (∀ n, Function.Bijective (L.fC n)) := by
  rcases h with ⟨hA, hB⟩ | ⟨hA, hC⟩ | ⟨hB, hC⟩
  · exact ⟨hA, hB, fun n => two_of_three_fC L hA hB n⟩
  · exact ⟨hA, fun n => two_of_three_fB L hA hC n, hC⟩
  · exact ⟨fun n => two_of_three_fA L hB hC n, hB, hC⟩

end LongExactLadder

/-- 2-out-of-3 principle packaged for `HomologyLadder`: the three implications among
`{fMap, gMap, hMap}` saying that bijectivity of any two of the three vertical maps
forces bijectivity of the third. -/
theorem HomologyLadder.two_of_three_bijective (L : HomologyLadder) :
    ((∀ n, Function.Bijective (L.fMap n)) → (∀ n, Function.Bijective (L.gMap n)) →
      ∀ n, Function.Bijective (L.hMap n)) ∧
    ((∀ n, Function.Bijective (L.fMap n)) → (∀ n, Function.Bijective (L.hMap n)) →
      ∀ n, Function.Bijective (L.gMap n)) ∧
    ((∀ n, Function.Bijective (L.gMap n)) → (∀ n, Function.Bijective (L.hMap n)) →
      ∀ n, Function.Bijective (L.fMap n)) :=
  ⟨fun hf hg n => by
      have := L.h_bijective_of_f_g_bijective hf hg (n - 1)
      rwa [Int.sub_add_cancel] at this,
   fun hf hh n => by
      have := L.g_bijective_of_f_h_bijective hf hh (n - 1)
      rwa [Int.sub_add_cancel] at this,
   fun hg hh n => L.f_bijective_of_g_h_bijective hg hh n⟩

end FiveLemma

namespace EilenbergSteenrod

open FiveLemma

/-- Forgetting the subspace data: a map of pairs `(X, A) → (Y, B)` induces a map between
the trivial pairs `(X, ∅) → (Y, ∅)`. Used in the Eilenberg–Steenrod packaging. -/
def MapOfPairs.toSpaceMap {P Q : TopPair} (f : MapOfPairs P Q) :
    MapOfPairs (TopPair.ofSpace P.space) (TopPair.ofSpace Q.space) where
  toFun := f.toFun
  continuous_toFun := f.continuous_toFun
  mapsTo := fun _ h => h.elim

end EilenbergSteenrod
