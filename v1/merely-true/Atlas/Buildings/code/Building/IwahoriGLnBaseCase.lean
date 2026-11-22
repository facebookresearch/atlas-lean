/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnDefs
import Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Mathlib.Tactic.FinCases

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

/-- Strict inequality of `Fin 2` values: $i < j$ iff $(i, j) = (0, 1)$. -/
lemma fin2_lt_iff (i j : Fin 2) : i.val < j.val ↔ (i = 0 ∧ j = 1) := by
  constructor
  · intro h
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Strict inequality of `Fin 2` values, swapped: $i > j$ iff $(i, j) = (1, 0)$. -/
lemma fin2_gt_iff (i j : Fin 2) : i.val > j.val ↔ (i = 1 ∧ j = 0) := by
  constructor
  · intro h
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Identification of the general $\mathrm{GL}_n$ definition of the Iwahori subgroup at $n = 2$
with the concrete $\mathrm{GL}_2$ definition. -/
theorem iwahoriGLn_eq_iwahoriGL2 : IwahoriGLn C 2 = IwahoriGL2 C := by
  ext g
  simp only [IwahoriGLn, IwahoriGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, habove, hbelow⟩
    exact ⟨hdiag 0, hdiag 1,
           habove 0 1 (by norm_num),
           hbelow 1 0 (by norm_num)⟩
  · rintro ⟨h00, h11, h01, h10⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_lt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h01
    · intro i j hij
      rw [fin2_gt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h10

/-- Identification of the general upper unipotent subgroup at $n = 2$ with the concrete
$\mathrm{GL}_2$ version. -/
theorem upperUnipGLn_eq_upperUnipGL2 : UpperUnipGLn C 2 = UpperUnipGL2 C := by
  ext g
  simp only [UpperUnipGLn, UpperUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, hbelow⟩
    exact ⟨hdiag 0, hdiag 1, hbelow 1 0 (by norm_num)⟩
  · rintro ⟨h00, h11, h10⟩
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_gt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h10

/-- Identification of the general lower unipotent subgroup at $n = 2$ with the concrete
$\mathrm{GL}_2$ version. -/
theorem lowerUnipGLn_eq_lowerUnipGL2 : LowerUnipGLn C 2 = LowerUnipGL2 C := by
  ext g
  simp only [LowerUnipGLn, LowerUnipGL2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdiag, habove⟩
    exact ⟨hdiag 0, hdiag 1, habove 0 1 (by norm_num)⟩
  · rintro ⟨h00, h11, h01⟩
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      rw [fin2_lt_iff] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact h01

/-- Identification of the general diagonal subgroup at $n = 2$ with the concrete $\mathrm{GL}_2$
version. -/
theorem diagGLn_eq_diagGL2 : DiagGLn C 2 = DiagGL2 C := by
  ext g
  simp only [DiagGLn, DiagGL2, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h 0 1 (by decide), h 1 0 (by decide)⟩
  · rintro ⟨h01, h10⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Base case ($n = 2$) of the Iwahori decomposition for $\mathrm{GL}_n$: every Iwahori element
factors uniquely as $u' \cdot m \cdot u$, obtained from the concrete $\mathrm{GL}_2$ result. -/
theorem iwahoriDecompositionGLn_base_case :
    ∀ b ∈ IwahoriGLn C 2,
      ∃! (triple : GL (Fin 2) C.k × GL (Fin 2) C.k × GL (Fin 2) C.k),
        let (u', m, u) := triple
        u' ∈ LowerUnipGLn C 2 ∩ IwahoriGLn C 2 ∧
        m ∈ DiagGLn C 2 ∩ IwahoriGLn C 2 ∧
        u ∈ UpperUnipGLn C 2 ∩ IwahoriGLn C 2 ∧
        b = u' * m * u := by
  simp_rw [iwahoriGLn_eq_iwahoriGL2, lowerUnipGLn_eq_lowerUnipGL2,
      diagGLn_eq_diagGL2, upperUnipGLn_eq_upperUnipGL2]
  exact C.IwahoriDecomposition_concrete

end DVRContext
