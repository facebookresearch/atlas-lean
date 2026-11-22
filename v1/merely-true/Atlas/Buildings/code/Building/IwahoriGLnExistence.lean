/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnBaseCase
import Atlas.Buildings.code.Building.IwahoriGLnClearing

set_option maxHeartbeats 400000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

/-- Existence half of the base case: each $b$ in the Iwahori subgroup of $\mathrm{GL}_2(k)$ admits
some Iwahori factorisation $b = u' \cdot m \cdot u$. -/
theorem iwahoriDecompositionGLn_base_case_exists :
    ∀ b ∈ IwahoriGLn C 2,
      ∃ (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k),
        let (u', m, u) := triple
        u' ∈ LowerUnipGLn C 2 ∩ IwahoriGLn C 2 ∧
        m ∈ DiagGLn C 2 ∩ IwahoriGLn C 2 ∧
        u ∈ UpperUnipGLn C 2 ∩ IwahoriGLn C 2 ∧
        b = u' * m * u :=
  fun b hb => (C.iwahoriDecompositionGLn_base_case b hb).exists

/-- Existence of the Iwahori decomposition for $\mathrm{GL}_n(k)$ for all $n \ge 2$: proved by
induction on $n$ starting from the $n = 2$ base case and using the inductive clearing step. -/
theorem IwahoriDecompositionGLn_existence (n : ℕ) (hn : n ≥ 2) :
    ∀ b ∈ IwahoriGLn C n,
      ∃ (triple : GL (Fin n) C.k × GL (Fin n) C.k × GL (Fin n) C.k),
        let (u', m, u) := triple
        u' ∈ LowerUnipGLn C n ∩ IwahoriGLn C n ∧
        m ∈ DiagGLn C n ∩ IwahoriGLn C n ∧
        u ∈ UpperUnipGLn C n ∩ IwahoriGLn C n ∧
        b = u' * m * u := by

  induction n with
  | zero => omega
  | succ m ih =>


    by_cases hm_eq : m + 1 = 2
    ·
      have hm : m = 1 := by omega
      subst hm

      exact C.iwahoriDecompositionGLn_base_case_exists
    ·
      have hm_ge2 : m ≥ 2 := by omega
      have hm_ge1 : m ≥ 1 := by omega

      have ih_m : ∀ b ∈ IwahoriGLn C m,
          ∃ (triple : GL (Fin m) C.k × GL (Fin m) C.k × GL (Fin m) C.k),
            let (u', md, u) := triple
            u' ∈ LowerUnipGLn C m ∩ IwahoriGLn C m ∧
            md ∈ DiagGLn C m ∩ IwahoriGLn C m ∧
            u ∈ UpperUnipGLn C m ∩ IwahoriGLn C m ∧
            b = u' * md * u := ih hm_ge2

      intro b hb
      exact C.iwahori_inductive_step hm_ge1 b hb ih_m

end DVRContext
