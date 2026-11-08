/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.IwahoriDecomp

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section GLnDefs

variable (n : ℕ)

/-- The Iwahori subgroup $I \subseteq \mathrm{GL}_n(k)$: matrices whose diagonal entries are units of
$\mathcal O$, strictly-above-diagonal entries lie in $\mathcal O$, and strictly-below-diagonal
entries lie in the maximal ideal $\mathfrak m$. -/
def IwahoriGLn : Set (GL (Fin n) C.k) :=
  { g |
    (∀ i : Fin n, C.isUnitInO (g.val i i)) ∧
    (∀ i j : Fin n, i.val < j.val → C.isInO (g.val i j)) ∧
    (∀ i j : Fin n, i.val > j.val → C.isInMaxIdeal (g.val i j)) }

/-- The upper unipotent subgroup $N \subseteq \mathrm{GL}_n(k)$: upper unitriangular matrices,
i.e. matrices with $1$s on the diagonal and $0$s strictly below it. -/
def UpperUnipGLn : Set (GL (Fin n) C.k) :=
  { g |
    (∀ i : Fin n, g.val i i = 1) ∧
    (∀ i j : Fin n, i.val > j.val → g.val i j = 0) }

/-- The lower unipotent subgroup $N^{\mathrm{op}} \subseteq \mathrm{GL}_n(k)$: lower unitriangular
matrices, i.e. matrices with $1$s on the diagonal and $0$s strictly above it. -/
def LowerUnipGLn : Set (GL (Fin n) C.k) :=
  { g |
    (∀ i : Fin n, g.val i i = 1) ∧
    (∀ i j : Fin n, i.val < j.val → g.val i j = 0) }

/-- The diagonal subgroup $M \subseteq \mathrm{GL}_n(k)$: matrices that vanish off the diagonal. -/
def DiagGLn : Set (GL (Fin n) C.k) :=
  { g | ∀ i j : Fin n, i ≠ j → g.val i j = 0 }

end GLnDefs

end DVRContext
