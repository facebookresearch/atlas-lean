/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Thm2375
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory Category MonoidalCategory

universe u

set_option maxHeartbeats 800000

noncomputable def TorGroup
    (R : Type u) [CommRing R] (n : ℕ) (M A : ModuleCat.{u} R) :
    ModuleCat.{u} R :=
  ((Tor' (ModuleCat.{u} R) n).obj M).obj A

noncomputable def TorGroup.functor
    (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  Tor' (ModuleCat.{u} R) n

section TorDeltaFunctorAuxiliary

noncomputable def torRes (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ProjectiveResolution M := ProjectiveResolution.of M

noncomputable abbrev tR (R : Type u) [CommRing R] :=
  tensoringRight (ModuleCat.{u} R)

noncomputable def torChainSC
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((tR R).map S.f) (ComplexShape.down ℕ)).app
      (torRes R M).complex)
    ((NatTrans.mapHomologicalComplex ((tR R).map S.g) (ComplexShape.down ℕ)).app
      (torRes R M).complex)
    (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
          ← Functor.map_comp, S.zero, Functor.map_zero]
      ext i; simp [NatTrans.mapHomologicalComplex]; rfl)

noncomputable def torChainSE
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (torChainSC R M S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i => by
    let Pi := (torRes R M).complex.X i
    haveI : Module.Projective R Pi := Pi.projective_of_module_projective
    haveI : Module.Flat R Pi := Module.Flat.of_projective
    show (S.map (tensorLeft Pi)).ShortExact
    exact hS.map_of_exact (tensorLeft Pi))

noncomputable def torIso
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (A : ModuleCat.{u} R) (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).obj M).obj A ≅
    (HomologicalComplex.homologyFunctor _ _ n).obj
      (((tR R).obj A).mapHomologicalComplex _ |>.obj (torRes R M).complex) :=
  (torRes R M).isoLeftDerivedObj ((tR R).obj A) n

end TorDeltaFunctorAuxiliary

noncomputable def TorGroup.connectingHom
    (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact)
    (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₃ ⟶
    ((Tor' (ModuleCat.{u} R) n).obj M).obj S.X₁ :=
  (torIso R M S.X₃ (n + 1)).hom ≫
  (torChainSE R M S hS).δ (n + 1) n rfl ≫
  (torIso R M S.X₁ n).inv
