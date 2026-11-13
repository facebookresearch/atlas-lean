/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every integral scheme has a nonempty underlying topological space (since it is irreducible). -/
noncomputable instance instNonemptyIntegralScheme : Nonempty X := by
  have : IrreducibleSpace X := inferInstance; exact ⟨this.2.some⟩

/-- The top open set `⊤` of an integral scheme is nonempty. -/
noncomputable instance instNonemptyTop : Nonempty (⊤ : X.Opens) :=
  ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩

/-- The natural map from units of the structure sheaf on `U` to units of the function field of an
integral scheme, induced by the germ-to-function-field morphism. -/
noncomputable def structureUnitsToFunctionFieldUnits (U : X.Opens) [Nonempty U] :
    Γ(X, U)ˣ →* (X.functionField)ˣ :=
  Units.map (X.germToFunctionField U).hom.toMonoidHom

/-- The image inside `(X.functionField)ˣ` of the units of the structure sheaf on `U`. -/
noncomputable def structureUnitsSubgroup (U : X.Opens) [Nonempty U] :
    Subgroup (X.functionField)ˣ :=
  (structureUnitsToFunctionFieldUnits X U).range

/-- The Cartier divisor presheaf on `U` defined as the quotient `K(X)ˣ / O(U)ˣ`, modelling
sections of `K*/O*`. -/
noncomputable def CartierDivisorPresheafQuotient (U : X.Opens) [Nonempty U] : Type u :=
  (X.functionField)ˣ ⧸ structureUnitsSubgroup X U

/-- A Cartier divisor datum on `X` (Def 31, Lec 15): a cover of `X` by open sets `Uᵢ`, rational
functions `fᵢ ∈ K(X)ˣ`, and the compatibility `f_j · f_i⁻¹` is a unit of `O(U_i ∩ U_j)` on
overlaps. -/
structure CartierDivisorDatum where
  ι : Type u
  cover : ι → X.Opens
  cover_eq_top : ⨆ i, cover i = ⊤
  f : ι → (X.functionField)ˣ
  compat : ∀ (i j : ι) (h : Nonempty (cover i ⊓ cover j : X.Opens)),
    f j * (f i)⁻¹ ∈
      (@structureUnitsToFunctionFieldUnits X _ (cover i ⊓ cover j) h).range

/-- The Cartier divisor group on a scheme `X`, modelled as the type of `CartierDivisorDatum`. -/
def CartierDivisorGroupScheme : Type _ := CartierDivisorDatum X

/-- The Cartier divisor group of `X` is inhabited by the trivial datum. -/
noncomputable instance instInhabitedCartierDivisorGroupScheme :
    Inhabited (CartierDivisorGroupScheme X) :=
  ⟨⟨PUnit, fun _ => ⊤, by simp, fun _ => 1, fun _ _ h => by
    simp only [MonoidHom.mem_range]
    exact ⟨1, by simp [structureUnitsToFunctionFieldUnits]⟩⟩⟩

/-- The principal Cartier divisor associated to a rational function `g ∈ K(X)ˣ`, given by the
single-chart cover `{⊤}` with `f = g`. -/
noncomputable def CartierDivisorDatum.principal (g : (X.functionField)ˣ) :
    CartierDivisorDatum X where
  ι := PUnit
  cover := fun _ => ⊤
  cover_eq_top := by simp
  f := fun _ => g
  compat := fun _ _ h => by
    simp only [MonoidHom.mem_range]
    exact ⟨1, by simp [structureUnitsToFunctionFieldUnits]⟩

/-- The trivial Cartier divisor datum on `X`, corresponding to the principal divisor of `1`. -/
noncomputable def CartierDivisorDatum.trivialDatum : CartierDivisorDatum X :=
  CartierDivisorDatum.principal X 1

/-- Convert a rational function `g ∈ K(X)ˣ` into the associated principal Cartier divisor datum
on `X`. -/
noncomputable def toDatum (g : (X.functionField)ˣ) : CartierDivisorDatum X :=
  CartierDivisorDatum.principal X g

/-- The subgroup of `K(X)ˣ` coming from `O(U)ˣ` is contained in that coming from `O(V)ˣ`
whenever `V ⊆ U`, since restrictions are functorial. -/
theorem structureUnitsSubgroup_mono {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) : structureUnitsSubgroup X U ≤ structureUnitsSubgroup X V := by
  intro x hx
  simp only [structureUnitsSubgroup, MonoidHom.mem_range] at hx ⊢
  obtain ⟨φ, hφ⟩ := hx
  refine ⟨Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom φ, ?_⟩
  rw [← hφ]; ext
  simp only [structureUnitsToFunctionFieldUnits, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply]
  have key : X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V =
      X.germToFunctionField U := by
    unfold Scheme.germToFunctionField
    rw [TopCat.Presheaf.germ_res]
  exact congrFun (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom key)) φ.val

end CartierDivisorScheme
