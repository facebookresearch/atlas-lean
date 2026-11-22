/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

open Finset Matrix BigOperators

namespace BregmanMinc

/-- The row sum $d_i$ of row $i$ of a $0/1$-matrix $A$: the number of columns $j$ with $A_{ij}=1$. -/
noncomputable def rowSum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card



/-- Row sum of a $0/1$-matrix indexed by an arbitrary finite type $V$: the number of $j$ with
$A_{ij}=1$. -/
noncomputable def rowSumGen {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (i : V) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card


end BregmanMinc

namespace KahnLovasz

open SimpleGraph Finset BigOperators

/-- The number of perfect matchings of a simple graph $G$. -/
noncomputable def numPerfectMatchings {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {M : G.Subgraph // M.IsPerfectMatching}


/-- The row sum of the adjacency matrix of $G$ at vertex $v$ equals the graph-theoretic degree
$\deg_G(v)$. -/
lemma adjMatrix_rowSumGen_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    BregmanMinc.rowSumGen (G.adjMatrix ℝ) v = G.degree v := by
  unfold BregmanMinc.rowSumGen SimpleGraph.degree
  congr 1
  ext w
  simp only [SimpleGraph.adjMatrix_apply, Finset.mem_filter, Finset.mem_univ, true_and,
             SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    split_ifs at h with hadj
    · exact hadj
    · norm_num at h
  · intro hadj
    simp [hadj]


end KahnLovasz
