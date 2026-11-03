/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.GroupAction.Defs

noncomputable section

open Matrix.SpecialLinearGroup Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace CMFieldOfDefinition

/-- The principal congruence subgroup $\Gamma(N)$ is contained in $\Gamma_1(N)$: a matrix
congruent to the identity mod $N$ has diagonal entries $\equiv 1$ and upper-right entry
$\equiv 0$ mod $N$, which are precisely the defining conditions for $\Gamma_1(N)$. -/
theorem Gamma_le_Gamma1 (N : ℕ) : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

/-- The open modular curve $Y(\Gamma) = \Gamma \backslash \mathcal{H}$ as the quotient
of the upper half-plane by the action of a subgroup $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$
via Mobius transformations. This is the noncompactified moduli space of elliptic curves
with $\Gamma$-level structure. -/
def ModularCurveOpen (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ UpperHalfPlane)




/-- The open modular curve $Y(N) = \Gamma(N) \backslash \mathcal{H}$, parametrizing
elliptic curves with full level-$N$ structure. -/
abbrev Y (N : ℕ) : Type := ModularCurveOpen (Gamma N)

/-- The open modular curve $Y_1(N) = \Gamma_1(N) \backslash \mathcal{H}$, parametrizing
elliptic curves equipped with a point of exact order $N$. -/
abbrev Y₁ (N : ℕ) : Type := ModularCurveOpen (Gamma1 N)

/-- The open modular curve $Y_0(N) = \Gamma_0(N) \backslash \mathcal{H}$, parametrizing
elliptic curves equipped with a cyclic subgroup of order $N$. -/
abbrev Y₀ (N : ℕ) : Type := ModularCurveOpen (Gamma0 N)




end CMFieldOfDefinition
end
