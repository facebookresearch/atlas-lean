/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Integration

/-- The set `C([a,b])` of continuous real-valued functions on the closed interval `[a,b]`. -/
def C_ab (a b : ℝ) : Set (ℝ → ℝ) :=
  {f : ℝ → ℝ | ContinuousOn f (Set.Icc a b)}

/-- A partition of the closed interval `[a,b]`: a strictly increasing finite sequence
`a = x_0 < x_1 < ⋯ < x_n = b` of points. The field `n` is the number of subintervals,
and `points` enumerates the `n + 1` endpoints. -/
structure Partition (a b : ℝ) where
  n : ℕ
  points : Fin (n + 1) → ℝ
  ordered : StrictMono points
  first : points 0 = a
  last : points (Fin.last n) = b

variable {a b : ℝ}

/-- A tagged partition of `[a,b]`: a partition together with a choice of a tag
`ξ_k ∈ [x_{k-1}, x_k]` in each subinterval. -/
structure TaggedPartition (a b : ℝ) extends Partition a b where
  tags : Fin n → ℝ
  tag_mem : ∀ i : Fin n, points i.castSucc ≤ tags i ∧ tags i ≤ points i.succ

/-- The mesh (or norm) `‖x‖` of a partition: the maximum length
`max_k (x_k - x_{k-1})` of its subintervals. Defined to be `0` for the trivial
partition with `n = 0`. -/
noncomputable def Partition.mesh (P : Partition a b) : ℝ :=
  if h : P.n = 0 then 0
  else
    Finset.sup' (Finset.univ (α := Fin P.n))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun i => P.points i.succ - P.points i.castSucc)

/-- The underlying set `{x_0, x_1, …, x_n}` of points of a partition. -/
def Partition.pointSet (P : Partition a b) : Set ℝ :=
  Set.range P.points

/-- `Q` is a refinement of `P` if every point of `P` appears in `Q`, i.e. the
underlying point set of `P` is contained in that of `Q`. -/
def Partition.IsRefinement (Q P : Partition a b) : Prop :=
  P.pointSet ⊆ Q.pointSet

/-- The Riemann sum `S_f(x, ξ) = ∑_k f(ξ_k) (x_k - x_{k-1})` of a function `f`
with respect to a tagged partition `T`. -/
noncomputable def riemannSum (f : ℝ → ℝ) (T : TaggedPartition a b) : ℝ :=
  ∑ i : Fin T.n, f (T.tags i) * (T.points i.succ - T.points i.castSucc)

open Set Filter Topology

/-- If `a < b`, then any partition of `[a,b]` has at least one subinterval, i.e.
`0 < P.n`. -/
lemma Partition.n_pos_of_lt (hab : a < b) (P : Partition a b) : 0 < P.n := by
  by_contra h
  have hn : P.n = 0 := by omega
  have hlast : Fin.last P.n = (0 : Fin (P.n + 1)) := by ext; simp [hn]
  have := P.last; rw [hlast] at this
  linarith [P.first]

/-- If `a < b`, then the mesh of any partition of `[a,b]` is strictly positive. -/
lemma Partition.mesh_pos_of_lt (hab : a < b) (P : Partition a b) :
    0 < P.mesh := by
  have hn : P.n ≠ 0 := (P.n_pos_of_lt hab).ne'
  have i₀ : Fin P.n := ⟨0, Nat.pos_of_ne_zero hn⟩
  unfold Partition.mesh
  rw [dif_neg hn]
  have hlt : P.points i₀.castSucc < P.points i₀.succ :=
    P.ordered Fin.castSucc_lt_succ
  calc (0 : ℝ) < P.points i₀.succ - P.points i₀.castSucc := sub_pos.mpr hlt
    _ ≤ Finset.sup' Finset.univ _
          (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc) :=
        Finset.le_sup' (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc)
          (Finset.mem_univ i₀)

/-- The Riemann sum over a trivial tagged partition (with `n = 0` subintervals)
is `0`, since it is an empty sum. -/
lemma riemannSum_eq_zero_of_n_eq_zero (f : ℝ → ℝ) (T : TaggedPartition a b)
    (h : T.n = 0) : riemannSum f T = 0 := by
  unfold riemannSum
  have : IsEmpty (Fin T.n) := by rw [h]; infer_instance
  exact Fintype.sum_empty _

end Integration
