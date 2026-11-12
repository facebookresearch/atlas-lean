/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnExistence
import Atlas.Buildings.code.Building.IwahoriGLnUniqueness

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section GLn

variable (n : ℕ)

/-- The identity matrix lies in the Iwahori subgroup of $\mathrm{GL}_n(k)$. -/
lemma one_mem_IwahoriGLn : (1 : GL (Fin n) C.k) ∈ IwahoriGLn C n := by
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
    exact C.isUnitInO_one
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]
    exact DVRClosure.isInO_zero
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]
    exact C.isInMaxIdeal_zero

/-- The identity matrix is lower unitriangular. -/
lemma one_mem_LowerUnipGLn : (1 : GL (Fin n) C.k) ∈ LowerUnipGLn C n := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]

/-- The identity matrix is upper unitriangular. -/
lemma one_mem_UpperUnipGLn : (1 : GL (Fin n) C.k) ∈ UpperUnipGLn C n := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Units.val_one, one_apply_eq]
  · have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp only [Units.val_one, one_apply_ne hne]

/-- Iwahori decomposition for $\mathrm{GL}_n(k)$: every element of the Iwahori subgroup $I$ admits
a unique factorisation $b = u' \cdot m \cdot u$ as a product of a lower unitriangular matrix
$u' \in N^{\mathrm{op}} \cap I$, a diagonal matrix $m \in M \cap I$, and an upper unitriangular
matrix $u \in N \cap I$. -/
theorem iwahoriDecompositionGLn :
    ∀ b ∈ IwahoriGLn C n,
      ∃! (triple : GL (Fin n) C.k × GL (Fin n) C.k × GL (Fin n) C.k),
        let (u', m, u) := triple
        u' ∈ LowerUnipGLn C n ∩ IwahoriGLn C n ∧
        m ∈ DiagGLn C n ∩ IwahoriGLn C n ∧
        u ∈ UpperUnipGLn C n ∩ IwahoriGLn C n ∧
        b = u' * m * u := by
  intro b hb
  by_cases hn : n ≥ 2
  ·
    obtain ⟨⟨u', m, u⟩, hu'_mem, hm_mem, hu_mem, hb_eq⟩ :=
      C.IwahoriDecompositionGLn_existence n hn b hb
    refine ⟨⟨u', m, u⟩, ⟨hu'_mem, hm_mem, hu_mem, hb_eq⟩, ?_⟩
    rintro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂_mem, hm₂_mem, hu₂_mem, hb_eq₂⟩
    have heq : u'₂ * m₂ * u₂ = u' * m * u := hb_eq₂.symm.trans hb_eq
    have ⟨h1, h2, h3⟩ := iwahori_decomp_unique u'₂ m₂ u₂ u' m u
      hu'₂_mem hm₂_mem hu₂_mem hu'_mem hm_mem hu_mem heq
    exact Prod.ext h1 (Prod.ext h2 h3)
  ·


    have hn_le : n ≤ 1 := by omega
    have h1_lower : (1 : GL (Fin n) C.k) ∈ LowerUnipGLn C n ∩ IwahoriGLn C n :=
      ⟨one_mem_LowerUnipGLn C n, one_mem_IwahoriGLn C n⟩
    have hb_diag : b ∈ DiagGLn C n ∩ IwahoriGLn C n := by
      refine ⟨fun i j hij => ?_, hb⟩

      interval_cases n
      · exact Fin.elim0 i
      · exact absurd (Subsingleton.elim i j) hij |> False.elim
    have h1_upper : (1 : GL (Fin n) C.k) ∈ UpperUnipGLn C n ∩ IwahoriGLn C n :=
      ⟨one_mem_UpperUnipGLn C n, one_mem_IwahoriGLn C n⟩
    have hb_eq : b = 1 * b * 1 := by simp
    refine ⟨⟨1, b, 1⟩, ⟨h1_lower, hb_diag, h1_upper, hb_eq⟩, ?_⟩
    rintro ⟨u'₂, m₂, u₂⟩ ⟨hu'₂_mem, hm₂_mem, hu₂_mem, hb_eq₂⟩
    have heq : u'₂ * m₂ * u₂ = 1 * b * 1 := hb_eq₂.symm.trans hb_eq
    have ⟨h1, h2, h3⟩ := iwahori_decomp_unique u'₂ m₂ u₂ 1 b 1
      hu'₂_mem hm₂_mem hu₂_mem h1_lower hb_diag h1_upper heq
    exact Prod.ext h1 (Prod.ext h2 h3)

end GLn

end DVRContext
