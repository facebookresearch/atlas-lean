/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnDefs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option maxHeartbeats 200000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section ElimMatrix

variable {n : ℕ}

/-- The transvection / elementary matrix $E_{ij}(c) = 1 + c \cdot e_{ij}$ packaged as an element of
$\mathrm{GL}_n(k)$, with explicit two-sided inverse $E_{ij}(-c)$. -/
noncomputable def elimMatrix (i j : Fin n) (hij : i ≠ j) (c : C.k) :
    GL (Fin n) C.k :=
  ⟨transvection i j c, transvection i j (-c),
    by simp [transvection, Matrix.add_mul, Matrix.mul_add, hij.symm, add_assoc, ← single_add],
    by simp [transvection, Matrix.add_mul, Matrix.mul_add, hij.symm, add_assoc, ← single_add]⟩

/-- The underlying matrix of `elimMatrix C i j hij c` is the transvection $E_{ij}(c)$. -/
@[simp]
theorem elimMatrix_val (i j : Fin n) (hij : i ≠ j) (c : C.k) :
    (elimMatrix C i j hij c).val = transvection i j c :=
  rfl

/-- Action of a transvection on a matrix from the left: in row $i$, the transvection adds $c$ times
row $j$ to row $i$. -/
theorem elim_matrix_mul (i j : Fin n) (c : C.k)
    (A : Matrix (Fin n) (Fin n) C.k) (b : Fin n) :
    (transvection i j c * A) i b = A i b + c * A j b := by
  simp [transvection, Matrix.add_mul]

/-- The inverse of the elementary matrix $E_{ij}(c)$ is $E_{ij}(-c)$. -/
theorem elim_matrix_inv (i j : Fin n) (hij : i ≠ j) (c : C.k) :
    (elimMatrix C i j hij c)⁻¹ = elimMatrix C i j hij (-c) := by
  ext1
  simp only [elimMatrix]
  rfl

/-- Rows of a matrix other than row $i$ are unchanged by left-multiplication by the transvection
$E_{ij}(c)$. -/
theorem elim_matrix_mul_ne (i j : Fin n) (c : C.k)
    (A : Matrix (Fin n) (Fin n) C.k) (a b : Fin n) (ha : a ≠ i) :
    (transvection i j c * A) a b = A a b := by
  simp [transvection, Matrix.add_mul, ha]

end ElimMatrix

section Unitriangular

variable {n : ℕ}

/-- An elementary matrix $E_{ij}(c)$ with $i < j$ is upper unitriangular. -/
theorem elim_matrix_upper_unitriangular (i j : Fin n) (hij : i ≠ j)
    (hlt : i.val < j.val) (c : C.k) :
    elimMatrix C i j hij c ∈ UpperUnipGLn C n := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
      show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
  · have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
      show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
      ite_false, add_zero]

/-- An elementary matrix $E_{ij}(c)$ with $i > j$ is lower unitriangular. -/
theorem elim_matrix_lower_unitriangular (i j : Fin n) (hij : i ≠ j)
    (hgt : i.val > j.val) (c : C.k) :
    elimMatrix C i j hij c ∈ LowerUnipGLn C n := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
      show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
  · have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
      show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
      ite_false, add_zero]

/-- An upper elementary matrix $E_{ij}(c)$ with $i < j$ lies in the Iwahori subgroup whenever
$c \in \mathcal O$. -/
theorem elim_matrix_iwahori_upper (i j : Fin n) (hij : i ≠ j)
    (hlt : i.val < j.val) (c : C.k) (hc : C.isInO c) :
    elimMatrix C i j hij c ∈ IwahoriGLn C n := by
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  ·
    have : (elimMatrix C i j hij c).val a a = 1 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
        show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
    rw [this]; exact C.isUnitInO_one
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply, zero_add]
    split_ifs with h
    · exact hc
    · exact DVRClosure.isInO_zero
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    have : (elimMatrix C i j hij c).val a b = 0 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
        show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
        ite_false, add_zero]

    rw [this]; exact C.isInMaxIdeal_zero

/-- A lower elementary matrix $E_{ij}(c)$ with $i > j$ lies in the Iwahori subgroup whenever
$c \in \mathfrak m$. -/
theorem elim_matrix_iwahori_lower (i j : Fin n) (hij : i ≠ j)
    (hgt : i.val > j.val) (c : C.k) (hc : C.isInMaxIdeal c) :
    elimMatrix C i j hij c ∈ IwahoriGLn C n := by
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  ·
    have : (elimMatrix C i j hij c).val a a = 1 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
        show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
    rw [this]; exact C.isUnitInO_one
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    have : (elimMatrix C i j hij c).val a b = 0 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
        show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
        ite_false, add_zero]
    rw [this]; exact DVRClosure.isInO_zero
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply, zero_add]
    split_ifs with h
    · exact hc
    · exact C.isInMaxIdeal_zero

end Unitriangular

section BlockEmbed

variable {n : ℕ}

/-- Equivalence $\mathrm{Fin}\,1 \oplus \mathrm{Fin}\,n \simeq \mathrm{Fin}(n + 1)$ obtained by
composing `finSumFinEquiv` with the natural cast $\mathrm{Fin}(1 + n) \simeq \mathrm{Fin}(n + 1)$. -/
noncomputable def finBlockEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

/-- `finBlockEquiv` sends the left summand `Sum.inl 0` to $0 \in \mathrm{Fin}(n + 1)$. -/
lemma finBlockEquiv_inl (n : ℕ) :
    (finBlockEquiv n) (Sum.inl (0 : Fin 1)) = (0 : Fin (n + 1)) := by
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.ext_iff]

/-- `finBlockEquiv` sends the right summand `Sum.inr k` to $k + 1 \in \mathrm{Fin}(n + 1)$. -/
lemma finBlockEquiv_inr (n : ℕ) (k : Fin n) :
    (finBlockEquiv n) (Sum.inr k) = ⟨k.val + 1, by omega⟩ := by
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.natAdd, Fin.ext_iff]; omega

/-- The inverse of `finBlockEquiv` sends $0 \in \mathrm{Fin}(n + 1)$ to the left summand
`Sum.inl 0`. -/
lemma finBlockEquiv_symm_zero (n : ℕ) :
    (finBlockEquiv n).symm 0 = Sum.inl 0 := by
  have := finBlockEquiv_inl n; rw [← this]; simp [Equiv.symm_apply_apply]

/-- The inverse of `finBlockEquiv` sends $k + 1 \in \mathrm{Fin}(n + 1)$ to the right summand
`Sum.inr k`. -/
lemma finBlockEquiv_symm_succ (n : ℕ) (k : Fin n) :
    (finBlockEquiv n).symm ⟨k.val + 1, by omega⟩ = Sum.inr k := by
  have := finBlockEquiv_inr n k; rw [← this]; simp [Equiv.symm_apply_apply]

/-- Case analysis on $\mathrm{Fin}(n + 1)$: every element is either $0$ or of the form $k + 1$ for
some $k \in \mathrm{Fin}\,n$. -/
lemma fin_succ_cases {n : ℕ} (p : Fin (n + 1)) :
    p = 0 ∨ ∃ k : Fin n, p = ⟨k.val + 1, by omega⟩ := by
  rcases Nat.eq_zero_or_pos p.val with h | h
  · left; exact Fin.ext h
  · right; exact ⟨⟨p.val - 1, by omega⟩, by simp [Fin.ext_iff]; omega⟩

/-- Block embedding $\mathrm{GL}_n \hookrightarrow \mathrm{GL}_{n+1}$ at the matrix level: place the
$n \times n$ matrix $A$ in the lower-right corner of the $(n+1) \times (n+1)$ matrix and put a
single $1$ in the upper-left corner. -/
noncomputable def blockEmbedMatrix (A : Matrix (Fin n) (Fin n) C.k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) C.k :=
  (reindexAlgEquiv C.k C.k (finBlockEquiv n))
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) C.k) 0 0 A)

/-- The $(0, 0)$-entry of `blockEmbedMatrix C A` is $1$. -/
lemma blockEmbedMatrix_zero_zero (A : Matrix (Fin n) (Fin n) C.k) :
    blockEmbedMatrix C A 0 0 = 1 := by
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, fromBlocks_apply₁₁, one_apply_eq]

/-- The first row of `blockEmbedMatrix C A` vanishes outside the $(0, 0)$ entry. -/
lemma blockEmbedMatrix_zero_succ (A : Matrix (Fin n) (Fin n) C.k) (k : Fin n) :
    blockEmbedMatrix C A 0 ⟨k.val + 1, by omega⟩ = 0 := by
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₁₂, Matrix.zero_apply]

/-- The first column of `blockEmbedMatrix C A` vanishes outside the $(0, 0)$ entry. -/
lemma blockEmbedMatrix_succ_zero (A : Matrix (Fin n) (Fin n) C.k) (k : Fin n) :
    blockEmbedMatrix C A ⟨k.val + 1, by omega⟩ 0 = 0 := by
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The lower-right $n \times n$ block of `blockEmbedMatrix C A` is $A$ itself. -/
lemma blockEmbedMatrix_succ_succ (A : Matrix (Fin n) (Fin n) C.k) (k l : Fin n) :
    blockEmbedMatrix C A ⟨k.val + 1, by omega⟩ ⟨l.val + 1, by omega⟩ = A k l := by
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_succ, fromBlocks_apply₂₂]

/-- Block embedding $\mathrm{GL}_n(k) \hookrightarrow \mathrm{GL}_{n+1}(k)$ at the group level:
upgrade `blockEmbedMatrix` to a unit by carrying the explicit inverse along. -/
noncomputable def blockEmbedGL (g : GL (Fin n) C.k) : GL (Fin (n + 1)) C.k := by
  refine ⟨blockEmbedMatrix C g.val, blockEmbedMatrix C g.inv, ?_, ?_⟩
  · simp only [blockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    simp [fromBlocks_one]
  · simp only [blockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    simp [fromBlocks_one]

/-- The underlying matrix of `blockEmbedGL C g` is `blockEmbedMatrix C g.val`. -/
@[simp]
theorem blockEmbedGL_val (g : GL (Fin n) C.k) :
    (blockEmbedGL C g).val = blockEmbedMatrix C g.val :=
  rfl

/-- The block embedding preserves the Iwahori subgroup. -/
theorem block_embed_preserves_iwahori (g : GL (Fin n) C.k)
    (hg : g ∈ IwahoriGLn C n) :
    blockEmbedGL C g ∈ IwahoriGLn C (n + 1) := by
  obtain ⟨hdiag, habove, hbelow⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]; exact C.isUnitInO_one
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_succ C]; exact DVRClosure.isInO_zero
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_zero C]; exact C.isInMaxIdeal_zero
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)

/-- The block embedding preserves upper unitriangular matrices. -/
theorem block_embed_preserves_upper_unip (g : GL (Fin n) C.k)
    (hg : g ∈ UpperUnipGLn C n) :
    blockEmbedGL C g ∈ UpperUnipGLn C (n + 1) := by
  obtain ⟨hdiag, hbelow⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_zero C]
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)

/-- The block embedding preserves lower unitriangular matrices. -/
theorem block_embed_preserves_lower_unip (g : GL (Fin n) C.k)
    (hg : g ∈ LowerUnipGLn C n) :
    blockEmbedGL C g ∈ LowerUnipGLn C (n + 1) := by
  obtain ⟨hdiag, habove⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_succ C]
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)

end BlockEmbed

section IwahoriMulClosure

variable {n : ℕ}

/-- The maximal ideal $\mathfrak m$ is closed under addition. -/
lemma isInMaxIdeal_add {x y : C.k}
    (hx : C.isInMaxIdeal x) (hy : C.isInMaxIdeal y) : C.isInMaxIdeal (x + y) := by
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx + ry, Ideal.add_mem _ hrx_mem hry_mem, by rw [map_add, hrx, hry]⟩

/-- If $x \in \mathcal O$ and $y \in \mathfrak m$, then $xy \in \mathfrak m$ (the maximal ideal is
an $\mathcal O$-module). -/
lemma isInO_mul_isInMaxIdeal {x y : C.k}
    (hx : C.isInO x) (hy : C.isInMaxIdeal y) : C.isInMaxIdeal (x * y) := by
  obtain ⟨rx, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_left _ rx hry_mem, by rw [map_mul, hrx, hry]⟩

/-- The set of units of $\mathcal O$ is closed under multiplication. -/
lemma isUnitInO_mul {x y : C.k}
    (hx : C.isUnitInO x) (hy : C.isUnitInO y) : C.isUnitInO (x * y) := by
  obtain ⟨rx, hrx_unit, hrx⟩ := hx; obtain ⟨ry, hry_unit, hry⟩ := hy
  exact ⟨rx * ry, hrx_unit.mul hry_unit, by rw [map_mul, hrx, hry]⟩

/-- Adding an element of the maximal ideal to a unit of $\mathcal O$ still gives a unit of
$\mathcal O$ (a unit plus a non-unit is a unit in a local ring). -/
lemma isUnitInO_add_isInMaxIdeal {x y : C.k}
    (hx : C.isUnitInO x) (hy : C.isInMaxIdeal y) : C.isUnitInO (x + y) := by
  rw [show x + y = x - (-y) from by ring]
  apply DVRClosureGL2.isUnitInO_sub_isInMaxIdeal hx
  obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨-ry, C.maxIdeal.neg_mem hry_mem, by rw [map_neg, hry]⟩

/-- A finite sum of elements of the maximal ideal lies in the maximal ideal. -/
lemma isInMaxIdeal_finset_sum {ι : Type*} {s : Finset ι} {f : ι → C.k}
    (hf : ∀ i ∈ s, C.isInMaxIdeal (f i)) : C.isInMaxIdeal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact C.isInMaxIdeal_zero
  | @insert a s' hna ih =>
    rw [Finset.sum_insert hna]
    exact C.isInMaxIdeal_add
      (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite sum of elements of $\mathcal O$ lies in $\mathcal O$. -/
lemma isInO_finset_sum {ι : Type*} {s : Finset ι} {f : ι → C.k}
    (hf : ∀ i ∈ s, C.isInO (f i)) : C.isInO (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact DVRClosure.isInO_zero
  | @insert a s' hna ih =>
    rw [Finset.sum_insert hna]
    exact DVRClosure.isInO_add
      (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Every entry of an Iwahori matrix lies in $\mathcal O$: diagonal entries are units, above-
diagonal entries are in $\mathcal O$ by definition, and below-diagonal entries are in
$\mathfrak m \subseteq \mathcal O$. -/
lemma iwahori_entry_isInO' (g : GL (Fin n) C.k)
    (hg : g ∈ IwahoriGLn C n) (i j : Fin n) : C.isInO (g.val i j) := by
  obtain ⟨hdiag, habove, hbelow⟩ := hg
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact habove i j h
  · have hij : i = j := Fin.ext h
    subst hij; exact C.isUnitInO_isInO (hdiag i)
  · exact C.isInMaxIdeal_isInO (hbelow i j h)

/-- Re-extraction lemma: strictly-below-diagonal entries of an Iwahori matrix lie in
$\mathfrak m$. -/
lemma iwahori_entry_below' (g : GL (Fin n) C.k)
    (hg : g ∈ IwahoriGLn C n) {i j : Fin n} (hij : i.val > j.val) :
    C.isInMaxIdeal (g.val i j) :=
  hg.2.2 i j hij

/-- The Iwahori subgroup of $\mathrm{GL}_n(k)$ is closed under multiplication. -/
theorem IwahoriGLn_mul_mem (g h : GL (Fin n) C.k)
    (hg : g ∈ IwahoriGLn C n) (hh : h ∈ IwahoriGLn C n) :
    g * h ∈ IwahoriGLn C n := by
  have hg_diag := hg.1
  have hg_above := hg.2.1
  have hg_below := hg.2.2
  have hh_diag := hh.1
  have hh_above := hh.2.1
  have hh_below := hh.2.2
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  ·

    show C.isUnitInO ((g * h).val i i)
    have hmul : (g * h).val i i = ∑ k : Fin n, g.val i k * h.val k i := by
      show (g.val * h.val) i i = _; simp [Matrix.mul_apply]
    rw [hmul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    apply C.isUnitInO_add_isInMaxIdeal
    · exact C.isUnitInO_mul (hg_diag i) (hh_diag i)
    · apply C.isInMaxIdeal_finset_sum
      intro k hk
      rw [Finset.mem_erase] at hk
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hk.1) with hki | hki
      ·
        exact DVRClosureGL2.isInMaxIdeal_mul_isInO (hg_below i k hki)
          (C.iwahori_entry_isInO' h hh k i)
      ·
        exact C.isInO_mul_isInMaxIdeal
          (C.iwahori_entry_isInO' g hg i k) (hh_below k i hki)
  ·

    show C.isInO ((g * h).val i j)
    have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
      show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
    rw [hmul]
    apply C.isInO_finset_sum
    intro k _
    exact DVRClosure.isInO_mul (C.iwahori_entry_isInO' g hg i k)
      (C.iwahori_entry_isInO' h hh k j)
  ·

    show C.isInMaxIdeal ((g * h).val i j)
    have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
      show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
    rw [hmul]
    apply C.isInMaxIdeal_finset_sum
    intro k _

    rcases le_or_gt k.val j.val with hkj | hkj
    ·
      exact DVRClosureGL2.isInMaxIdeal_mul_isInO
        (hg_below i k (by omega)) (C.iwahori_entry_isInO' h hh k j)
    ·
      exact C.isInO_mul_isInMaxIdeal
        (C.iwahori_entry_isInO' g hg i k) (hh_below k j hkj)

end IwahoriMulClosure

end DVRContext
