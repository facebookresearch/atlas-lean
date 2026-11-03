/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SerreDualityTate
import Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator


section TateVectorSpaceDef

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two subspaces `W₁`, `W₂` of `V` are commensurable iff their quotients by
their intersection are both finite-dimensional. -/
def IsCommensurable (W₁ W₂ : Submodule k V) : Prop :=
  Module.Finite k (W₁ ⧸ Submodule.comap W₁.subtype (W₁ ⊓ W₂)) ∧
  Module.Finite k (W₂ ⧸ Submodule.comap W₂.subtype (W₁ ⊓ W₂))

/-- Commensurability is reflexive: every subspace is commensurable with itself. -/
theorem IsCommensurable.refl (W : Submodule k V) : IsCommensurable W W := by
  have h : Submodule.comap W.subtype (W ⊓ W) = ⊤ := by ext x; simp
  constructor <;> { rw [h]; infer_instance }

/-- Commensurability is symmetric in its two arguments. -/
theorem IsCommensurable.symm {W₁ W₂ : Submodule k V}
    (h : IsCommensurable W₁ W₂) : IsCommensurable W₂ W₁ := by
  constructor
  · rw [inf_comm]; exact h.2
  · rw [inf_comm]; exact h.1

/-- A Tate vector space over `k` (Def 46, Lec 25): a topological `k`-vector
space whose neighborhood basis of zero consists of pairwise commensurable
linear subspaces. -/
class IsTateVectorSpace (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [TopologicalSpace V] : Prop where
  exists_nhds_basis : ∃ (ι : Type*) (W : ι → Submodule k V),
    (nhds (0 : V)).HasBasis (fun _ : ι => True) (fun i => ↑(W i)) ∧
    ∀ i j, IsCommensurable (W i) (W j)

end TateVectorSpaceDef

noncomputable section

universe v

namespace TateCechInfra

open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator

variable (k : Type*) [Field k]

/-- Packaging the data needed to apply Tate self-duality machinery to a Čech
cohomology setup on a smooth complete curve, recording the Riemann–Roch
identities for both `E` and the dualized line bundle `K - E`. -/
structure CechSheafData where
  setup : TateDualitySetup.{_, v} k
  [instFD : FiniteDimensional k setup.V]
  curve : SmoothCompleteCurve
  deg : ℤ
  h0_E : ℤ
  h1_EK : ℤ
  hRR_E : h0_E - ↑(Module.finrank k setup.cechH1) = curve.χ (1, deg)
  hRR_EK : ↑(Module.finrank k ↥setup.dual.cechH0) - h1_EK =
            curve.χ (1, curve.degK - deg)

attribute [instance] CechSheafData.instFD

variable {k}

/-- The dimension of `H¹(E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h1_E (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k D.setup.cechH1)

/-- The dimension of `H⁰(K - E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h0_EK (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k ↥D.setup.dual.cechH0)

/-- Unconditional Serre duality from Tate self-duality: `h⁰(K - E) = h¹(E)`. -/
theorem serre_duality_unconditional (D : CechSheafData k) :
    D.h0_EK = D.h1_E := by
  unfold CechSheafData.h0_EK CechSheafData.h1_E
  exact_mod_cast tate_duality_core D.setup





/-- If the residue pairing vanishes on `S.V₁ × V₁'`, then `V₁'` is contained
in the annihilator of `S.V₁`. -/
theorem residue_pairing_gives_annihilator_inclusion
    (S : TateDualitySetup k) (V₁' : Submodule k (Module.Dual k S.V))
    (h_residue : ∀ f ∈ S.V₁, ∀ φ ∈ V₁', φ f = 0) :
    V₁' ≤ S.V₁.dualAnnihilator :=
  residue_implies_annihilator_inclusion k S V₁' h_residue

/-- If both `Vᵢ'` equal the annihilators of `S.Vᵢ`, then their intersection
equals the annihilator of `S.V₁ ⊔ S.V₂`. -/
theorem annihilator_equalities_give_duality
    (S : TateDualitySetup k)
    (V₁' V₂' : Submodule k (Module.Dual k S.V))
    (h_eq₁ : V₁' = S.V₁.dualAnnihilator)
    (h_eq₂ : V₂' = S.V₂.dualAnnihilator) :
    V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator :=
  annihilator_equality_gives_duality k S V₁' h_eq₁ V₂' h_eq₂

/-- Core Tate dimension identity: the dual cohomology has the same dimension
as the original Čech `H¹`. -/
theorem tate_dimension_identity
    (S : TateDualitySetup.{_, v} k) [FiniteDimensional k S.V] :
    Module.finrank k ↥S.dual.cechH0 = Module.finrank k S.cechH1 :=
  tate_duality_core S

/-- In a finite-dimensional space, the annihilator of a sum has the same
dimension as the quotient by that sum. -/
theorem annihilator_quotient_dimension
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W₁ W₂ : Submodule k V) :
    Module.finrank k ↥(W₁ ⊔ W₂).dualAnnihilator =
    Module.finrank k (V ⧸ (W₁ ⊔ W₂)) := by
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (W₁ ⊔ W₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

/-- Tate duality via a self-pairing isomorphism `V ≃ V*`: the dimension of
the intersection of annihilators pulled back through `B` matches the quotient
dimension. -/
theorem self_pairing_tate_duality
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : V ≃ₗ[k] Module.Dual k V)
    (W₁ W₂ : Submodule k V) :
    Module.finrank k ↥(W₁.dualAnnihilator.comap B.toLinearMap ⊓
                         W₂.dualAnnihilator.comap B.toLinearMap) =
    Module.finrank k (V ⧸ (W₁ ⊔ W₂)) :=
  tate_duality_via_pairing B W₁ W₂




end TateCechInfra

end
