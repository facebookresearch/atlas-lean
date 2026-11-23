/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves

namespace SheafCohCurvesFiniteness

open CohomologyP1 SheafCohomology


section TwoTermComplex

variable (k : Type*) [Field k]

/-- A two-term Čech complex `C⁰ → C¹` over a field `k`: the natural model
for the Čech cohomology of a sheaf on a two-element open cover. -/
structure CechComplex2 (k : Type*) [Field k] where
  C0 : Type*
  C1 : Type*
  [inst0 : AddCommGroup C0]
  [inst1 : AddCommGroup C1]
  [mod0 : Module k C0]
  [mod1 : Module k C1]
  d : C0 →ₗ[k] C1

attribute [instance] CechComplex2.inst0 CechComplex2.inst1
  CechComplex2.mod0 CechComplex2.mod1

/-- `H⁰` of a two-term Čech complex is the kernel of `d : C⁰ → C¹`. -/
def CechComplex2.H0 (C : CechComplex2 k) : Submodule k C.C0 :=
  LinearMap.ker C.d

/-- `H¹` of a two-term Čech complex is the cokernel `C¹ / im d`. -/
abbrev CechComplex2.H1 (C : CechComplex2 k) : Type* :=
  C.C1 ⧸ LinearMap.range C.d

/-- Vanishing of higher Čech cohomology: the quotient of `PUnit` by `⊤` has
finrank zero (trivially), illustrating `H^i = 0` for `i ≥ 2` in a two-term complex. -/
theorem cech2_higher_vanishing_finrank :
    Module.finrank k (PUnit ⧸ (⊤ : Submodule k PUnit)) = 0 := by
  haveI : Subsingleton (PUnit ⧸ (⊤ : Submodule k PUnit)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

end TwoTermComplex


section P1Finiteness

variable (k : Type) [Field k]

/-- The subspace of `Finsupp` supported in a finite set `S` is finite-dimensional. -/
@[reducible]
noncomputable def finiteDim_supported (S : Set ℤ) [Fintype S] :
    Module.Finite k ↥(Finsupp.supported k k S) :=
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp S).symm

/-- Finiteness of `H⁰(O_{ℙ¹}(n))`: it is `k`-supported on the finite set `[0, n]`. -/
noncomputable instance cechH0_finiteDim_P1 (n : ℤ) :
    Module.Finite k ↥(CechH0 k n) := by
  rw [cechH0_eq_supported]
  exact finiteDim_supported k (Set.Icc 0 n)

/-- Finiteness of `H¹(O_{ℙ¹}(n))`: it is realized by Laurent terms with indices
strictly between `n` and `0`, a finite range. -/
noncomputable instance cechH1_finiteDim_P1 (n : ℤ) :
    Module.Finite k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) := by
  haveI : Module.Finite k ↥(Finsupp.supported k k (Set.Ioo n (0 : ℤ))) :=
    finiteDim_supported k (Set.Ioo n 0)
  exact Module.Finite.equiv (H1_equiv_supported_complement k n).symm

end P1Finiteness


section DirectSumFiniteness

variable (k : Type*) [Field k]

end DirectSumFiniteness


section CurveCohomology

variable (k : Type) [Field k]

end CurveCohomology


section EulerCharacteristic

variable (k : Type) [Field k]

end EulerCharacteristic

end SheafCohCurvesFiniteness
