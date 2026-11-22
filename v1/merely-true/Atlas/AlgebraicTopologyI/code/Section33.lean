/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The singular chain complex $S_\bullet(X; R)$ of a topological space `X` with
coefficients in the ring `R`, as a chain complex of `R`-modules. -/
abbrev singularChainCx (X : TopCat.{0}) :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X)

/-- The $p$-th singular cohomology module $H^p(X; R)$ of `X` with coefficients
in `R`, computed as the $p$-th cohomology of the dual cochain complex
$\mathrm{Hom}_R(S_\bullet(X; R), R)$. -/
abbrev singularCohomologyR (X : TopCat.{0}) (p : ℕ) : ModuleCat R :=
  ((singularChainCx R X).linearYonedaObj R (ModuleCat.of R R)).homology p

/-- The pushforward $f_* : H_p(X; R) \to H_p(Y; R)$ on singular homology
induced by a continuous map `f : X → Y`. -/
def homologyPushforward (X Y : TopCat.{0}) (f : X ⟶ Y) (p : ℕ) :
    singularHomologyModule R X p ⟶ singularHomologyModule R Y p :=
  ((singularHomologyFunctor (ModuleCat.{0} R) p).obj (ModuleCat.of R R)).map f

/-- The cochain-level pullback $f^\# : S^\bullet(Y; R) \to S^\bullet(X; R)$
dual to the chain pushforward induced by `f : X → Y`. -/
def cochainPullbackMap (X Y : TopCat.{0}) (f : X ⟶ Y) :
    (singularChainCx R Y).linearYonedaObj R (ModuleCat.of R R) ⟶
    (singularChainCx R X).linearYonedaObj R (ModuleCat.of R R) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f)).op

/-- The pullback $f^* : H^p(Y; R) \to H^p(X; R)$ on singular cohomology induced
by a continuous map `f : X → Y`. -/
def cohomologyPullback (X Y : TopCat.{0}) (f : X ⟶ Y) (p : ℕ) :
    singularCohomologyR R Y p ⟶ singularCohomologyR R X p :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) p).map
    (cochainPullbackMap R X Y f)

end SingularCohomology

/-- Index-shape compatibility lemma: for the descending complex shape on `ℕ`,
the predecessor of `p` equals the successor of `p` for the ascending shape.
Both equal `p + 1`. Used to reconcile homological and cohomological indexing. -/
lemma down_prev_eq_up_next (p : ℕ) :
    (ComplexShape.down ℕ).prev p = (ComplexShape.up ℕ).next p := by
  rw [ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl),
      ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)]

/-- Index-shape compatibility lemma: for the descending complex shape on `ℕ`,
the successor of `p` equals the predecessor of `p` for the ascending shape.
Used to reconcile homological and cohomological indexing. -/
lemma down_next_eq_up_prev (p : ℕ) :
    (ComplexShape.down ℕ).next p = (ComplexShape.up ℕ).prev p := by
  rcases p with _ | p
  · simp [ComplexShape.next, ComplexShape.prev, ComplexShape.down, ComplexShape.up]
  · rw [ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down]),
        ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel p (p + 1) by simp [ComplexShape.up])]

end

noncomputable section

open SingularCohomology

/-- The **Kronecker pairing** $\langle -, - \rangle : H^p(X; R) \otimes_R H_p(X; R) \to R$:
a cohomology class `β ∈ H^p(X; R)` is represented by a cocycle, a homology class
`x ∈ H_p(X; R)` is represented by a cycle, and the pairing evaluates the cocycle
on the cycle. The construction passes to homology by verifying that cocycles
vanish on boundaries and that coboundaries vanish on cycles. -/
def SingularCohomology.kroneckerPairing
    (R : Type) [CommRing R] (X : TopCat.{0}) (p : ℕ) :
    (SingularCohomology.singularCohomologyR R X p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X p : Type) →ₗ[R] R := by

  set chainCx := singularChainCx R X
  set cochainCx := chainCx.linearYonedaObj R (ModuleCat.of R R)
  set Sc := chainCx.sc p
  set Scc := cochainCx.sc p

  set isoH := Sc.moduleCatHomologyIso
  set isoCH := Scc.moduleCatHomologyIso

  have h1 := down_prev_eq_up_next p
  have h2 := down_next_eq_up_prev p

  set rawEval : ∀ β : LinearMap.ker Scc.g.hom, LinearMap.ker Sc.g.hom →ₗ[R] R :=
    fun β => ((show chainCx.X p ⟶ ModuleCat.of R R from β.val).hom).comp
      (LinearMap.ker Sc.g.hom).subtype

  have h_cocycle : ∀ β : LinearMap.ker Scc.g.hom,
      LinearMap.range Sc.moduleCatToCycles ≤ LinearMap.ker (rawEval β) := by
    intro β x ⟨η, hη⟩; rw [LinearMap.mem_ker]; subst hη
    exact congr_arg (fun f => f.hom η)
      (show Sc.f ≫ (show chainCx.X p ⟶ ModuleCat.of R R from β.val) = 0 from by
        have hβ := β.prop; rw [LinearMap.mem_ker] at hβ
        let β' : chainCx.X p ⟶ ModuleCat.of R R := β.val
        rw [show Sc.f = chainCx.d ((ComplexShape.down ℕ).prev p) p from rfl,
            ← HomologicalComplex.XIsoOfEq_hom_comp_d chainCx h1 p]
        have key : chainCx.d ((ComplexShape.up ℕ).next p) p ≫ β' = 0 := hβ
        change ((HomologicalComplex.XIsoOfEq chainCx h1).hom ≫
          chainCx.d ((ComplexShape.up ℕ).next p) p) ≫ β' = 0
        rw [Category.assoc, key, comp_zero])

  set evalOnH := fun β : LinearMap.ker Scc.g.hom =>
    (LinearMap.range Sc.moduleCatToCycles).liftQ (rawEval β) (h_cocycle β)

  let outerMap : LinearMap.ker Scc.g.hom →ₗ[R]
      ((LinearMap.ker Sc.g.hom ⧸ LinearMap.range Sc.moduleCatToCycles) →ₗ[R] R) :=
    { toFun := evalOnH
      map_add' := fun β₁ β₂ => by
        ext ⟨ξ, hξ⟩
        show evalOnH (β₁ + β₂) (Submodule.Quotient.mk ⟨ξ, hξ⟩) =
          evalOnH β₁ (Submodule.Quotient.mk ⟨ξ, hξ⟩) + evalOnH β₂ (Submodule.Quotient.mk ⟨ξ, hξ⟩)
        simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
          Function.comp_apply]
        change (((β₁.val + β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom)) ξ =
          ((β₁.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ +
          ((β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ
        change ((β₁.val : chainCx.X p ⟶ ModuleCat.of R R).hom +
          (β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ = _
        simp [LinearMap.add_apply]
      map_smul' := fun r β => by
        ext ⟨ξ, hξ⟩
        show evalOnH (r • β) (Submodule.Quotient.mk ⟨ξ, hξ⟩) =
          r • evalOnH β (Submodule.Quotient.mk ⟨ξ, hξ⟩)
        simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
          Function.comp_apply, smul_eq_mul]
        change ((r • (β.val : chainCx.X p ⟶ ModuleCat.of R R)).hom) ξ =
          r * ((β.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ
        change (r • (β.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ = _
        simp [LinearMap.smul_apply, smul_eq_mul] }

  have h_cobdy : LinearMap.range Scc.moduleCatToCycles ≤ LinearMap.ker outerMap := by
    intro x ⟨α, hα⟩; rw [LinearMap.mem_ker]; subst hα
    ext ⟨ξ, hξ⟩
    show evalOnH (Scc.moduleCatToCycles α) (Submodule.Quotient.mk ⟨ξ, hξ⟩) = 0
    simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
      Function.comp_apply]
    show ((show chainCx.X p ⟶ ModuleCat.of R R from (Scc.f.hom α)).hom) ξ = 0
    have step1 : (show chainCx.X p ⟶ ModuleCat.of R R from (Scc.f.hom α)) =
        chainCx.d p ((ComplexShape.up ℕ).prev p) ≫
        (show chainCx.X ((ComplexShape.up ℕ).prev p) ⟶ ModuleCat.of R R from α) := rfl
    rw [step1, ModuleCat.comp_apply,
      show chainCx.d p ((ComplexShape.up ℕ).prev p) =
        chainCx.d p ((ComplexShape.down ℕ).next p) ≫
        (HomologicalComplex.XIsoOfEq chainCx h2).hom from
      (HomologicalComplex.d_comp_XIsoOfEq_hom chainCx h2 p).symm,
      ModuleCat.comp_apply,
      show (chainCx.d p ((ComplexShape.down ℕ).next p)).hom ξ = Sc.g.hom ξ from rfl]
    rw [LinearMap.mem_ker] at hξ
    erw [hξ, map_zero]

  set pairingConcrete :=
    (LinearMap.range Scc.moduleCatToCycles).liftQ outerMap h_cobdy
  exact
    { toFun := fun β_abs =>
        (pairingConcrete (isoCH.hom.hom β_abs)).comp isoH.hom.hom
      map_add' := fun β₁ β₂ => by
        ext x; simp only [LinearMap.comp_apply, LinearMap.add_apply]
        erw [map_add, map_add]; rfl
      map_smul' := fun r β => by
        ext x; simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        erw [map_smul, map_smul]; rfl }

end

set_option maxHeartbeats 1600000 in
/-- **Claim 33.1 (naturality of the Kronecker pairing).** For a continuous map
$f : X \to Y$, a class $b \in H^p(Y; R)$ and a class $x \in H_p(X; R)$,
$\langle f^* b, x \rangle = \langle b, f_* x \rangle$. -/
theorem SingularCohomology.kroneckerPairing_natural
    (R : Type) [CommRing R]
    (X Y : TopCat.{0}) (f : X ⟶ Y) (p : ℕ)
    (b : (SingularCohomology.singularCohomologyR R Y p : Type))
    (x : (SingularCohomology.singularHomologyModule R X p : Type)) :
    SingularCohomology.kroneckerPairing R X p
      (SingularCohomology.cohomologyPullback R X Y f p b) x =
    SingularCohomology.kroneckerPairing R Y p b
      (SingularCohomology.homologyPushforward R X Y f p x) := by


  set SccX := ((singularChainCx R X).linearYonedaObj R (ModuleCat.of R R)).sc p
  set SccY := ((singularChainCx R Y).linearYonedaObj R (ModuleCat.of R R)).sc p
  set ScX := (singularChainCx R X).sc p
  set ScY := (singularChainCx R Y).sc p

  set φcc := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) p).map
    (cochainPullbackMap R X Y f)
  set γcc : ShortComplex.LeftHomologyMapData φcc SccY.moduleCatLeftHomologyData
    SccX.moduleCatLeftHomologyData := default

  set chainMapF := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f
  set φc := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) p).map
    chainMapF
  set γc : ShortComplex.LeftHomologyMapData φc ScX.moduleCatLeftHomologyData
    ScY.moduleCatLeftHomologyData := default

  have hcc : SccX.moduleCatHomologyIso.hom.hom
      (ShortComplex.homologyMap φcc b) = γcc.φH.hom (SccY.moduleCatHomologyIso.hom.hom b) :=
    congr_arg (·.hom b) γcc.homologyMap_comm

  have hc : ScY.moduleCatHomologyIso.hom.hom
      (ShortComplex.homologyMap φc x) = γc.φH.hom (ScX.moduleCatHomologyIso.hom.hom x) :=
    congr_arg (·.hom x) γc.homologyMap_comm

  simp only [kroneckerPairing, cohomologyPullback, homologyPushforward,
    HomologicalComplex.homologyFunctor_map,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]


  erw [hcc, hc]


  refine Submodule.Quotient.induction_on _
    (SccY.moduleCatHomologyIso.hom.hom b) (fun β => ?_)
  refine Submodule.Quotient.induction_on _
    (ScX.moduleCatHomologyIso.hom.hom x) (fun ξ => ?_)


  have hccpi : γcc.φH.hom (Submodule.Quotient.mk β) =
      Submodule.Quotient.mk (γcc.φK.hom β) :=
    congr_arg (·.hom β) γcc.commπ
  have hcpi : γc.φH.hom (Submodule.Quotient.mk ξ) =
      Submodule.Quotient.mk (γc.φK.hom ξ) :=
    congr_arg (·.hom ξ) γc.commπ
  rw [hccpi, hcpi]

  simp only [Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk]

  rfl




set_option maxHeartbeats 800000 in
/-- Compatibility of the Kronecker pairing with `TopCat.prodIsoProd`: an
instance of `kroneckerPairing_natural` applied to the canonical comparison
isomorphism between the categorical product `X ⨯ Y` and the topological
product `X × Y`. -/
theorem SingularCohomology.kroneckerPairing_prodIsoProd_compat
    (R : Type) [CommRing R]
    (X Y : TopCat.{0}) (n : ℕ)
    (c : ↑(singularCohomology R (X ⨯ Y) (ModuleCat.of R R) n))
    (h : ↑(SingularCohomology.singularHomologyModule R (TopCat.of (↑X × ↑Y)) n)) :
    SingularCohomology.kroneckerPairing R (TopCat.of (↑X × ↑Y)) n
      ((singularCohomologyMap R (TopCat.prodIsoProd X Y).inv n).hom c) h =
    SingularCohomology.kroneckerPairing R (X ⨯ Y) n c
      ((SingularCohomology.homologyPushforward R (TopCat.of (↑X × ↑Y)) (X ⨯ Y)
        (TopCat.prodIsoProd X Y).inv n).hom h) :=
  SingularCohomology.kroneckerPairing_natural R (TopCat.of (↑X × ↑Y)) (X ⨯ Y)
    (TopCat.prodIsoProd X Y).inv n c h



