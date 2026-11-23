/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.RealAnalysis.code.Integration.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort

import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter Topology Finset

namespace Integration

/-- The modulus of continuity of a function `f` on `[a, b]` at scale `η`:
`w_f(η) = sup {|f(x) - f(y)| : x, y ∈ [a,b], |x - y| ≤ η}`. -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b η : ℝ) : ℝ :=
  sSup {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)}

/-- **Theorem I (Modulus of continuity vanishes).** For `f ∈ C([a,b])`,
`lim_{η → 0⁺} w_f(η) = 0`. That is, `∀ ε > 0, ∃ δ > 0, ∀ η < δ : w_f(η) < ε`. -/
theorem modulusOfContinuity_tendsto_zero (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto (modulusOfContinuity f a b) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hfδ⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun η hη_mem hη_dist => ?_⟩
  simp only [Real.dist_eq, sub_zero] at hη_dist ⊢
  have hη_pos : (0 : ℝ) < η := hη_mem
  have hη_lt_δ : η < δ := by linarith [abs_of_pos hη_pos]

  have hle : ∀ d ∈ {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)},
      d ≤ ε / 2 := by
    rintro d ⟨x, hx, y, hy, hxy, rfl⟩
    have hdist : dist x y < δ := by
      rw [Real.dist_eq]
      linarith
    have := hfδ x hx y hy hdist
    rw [Real.dist_eq] at this
    linarith

  have hne : ({|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} : Set ℝ).Nonempty :=
    ⟨|f a - f a|, a, ⟨le_refl a, hab⟩, a, ⟨le_refl a, hab⟩, by simp; linarith⟩

  have hsup_le : sSup {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} ≤ ε / 2 :=
    csSup_le hne hle

  have hbdd : BddAbove {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} :=
    ⟨ε / 2, hle⟩

  have hsup_nonneg : 0 ≤ sSup {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} := by
    have hmem : (0 : ℝ) ∈ {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} := by
      refine ⟨a, ⟨le_refl a, hab⟩, a, ⟨le_refl a, hab⟩, ?_, ?_⟩
      · simp; linarith
      · simp
    exact le_csSup hbdd hmem

  show |modulusOfContinuity f a b η| < ε
  unfold modulusOfContinuity
  rw [abs_of_nonneg hsup_nonneg]
  linarith

variable {a b : ℝ}

/-- The set of values `|f x - f y|` for `x, y ∈ [a,b]` with `|x - y| ≤ η` is
bounded above when `f` is continuous on `[a,b]`. -/
lemma modulusOfContinuity_bddAbove (f : ℝ → ℝ) (a b η : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    BddAbove {|f x - f y| | (x ∈ Icc a b) (y ∈ Icc a b) (_ : |x - y| ≤ η)} := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨C + C, by
    rintro d ⟨x, hx, y, hy, _, rfl⟩
    have h1 := hC x hx; have h2 := hC y hy
    rw [Real.norm_eq_abs] at h1 h2
    exact (abs_sub (f x) (f y)).trans (by linarith)⟩

/-- For `x, y ∈ [a,b]` with `|x - y| ≤ η`, the absolute difference `|f x - f y|`
is bounded by the modulus of continuity `w_f(η)`. -/
lemma le_modulusOfContinuity (f : ℝ → ℝ) {a b : ℝ} (η : ℝ)
    (hf : ContinuousOn f (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) {y : ℝ} (hy : y ∈ Icc a b) (hxy : |x - y| ≤ η) :
    |f x - f y| ≤ modulusOfContinuity f a b η :=
  le_csSup (modulusOfContinuity_bddAbove f a b η hf) ⟨x, hx, y, hy, hxy, rfl⟩

/-- Each subinterval `[x_i, x_{i+1}]` of a partition has nonnegative length. -/
lemma Partition.succ_sub_castSucc_nonneg (P : Partition a b) (i : Fin P.n) :
    0 ≤ P.points i.succ - P.points i.castSucc :=
  sub_nonneg.mpr (P.ordered.monotone Fin.castSucc_lt_succ.le)

/-- Each subinterval length `x_{i+1} - x_i` of a partition is bounded above by
the partition's mesh (i.e., the maximum subinterval length). -/
lemma Partition.le_mesh (P : Partition a b) (i : Fin P.n) :
    P.points i.succ - P.points i.castSucc ≤ P.mesh := by
  have hne : P.n ≠ 0 := Fin.pos i |>.ne'
  show P.points i.succ - P.points i.castSucc ≤
    (if h : P.n = 0 then (0 : ℝ) else Finset.sup' (Finset.univ (α := Fin P.n))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun i : Fin P.n => P.points i.succ - P.points i.castSucc))
  rw [dif_neg hne]
  exact Finset.le_sup' (fun i : Fin P.n => P.points i.succ - P.points i.castSucc)
    (Finset.mem_univ i)

/-- The subinterval lengths of a partition of `[a,b]` telescope to `b - a`:
`∑ᵢ (x_{i+1} - x_i) = b - a`. -/
lemma Partition.sum_sub_eq (P : Partition a b) :
    ∑ i : Fin P.n, (P.points i.succ - P.points i.castSucc) = b - a := by
  set g : ℕ → ℝ := fun j => if h : j < P.n + 1 then P.points ⟨j, h⟩ else 0
  suffices h : ∑ i ∈ Finset.range P.n, (g (i + 1) - g i) = b - a by
    rw [← h, ← Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i)]
    congr 1; ext i
    simp only [g, show (↑i : ℕ) + 1 < P.n + 1 from by omega,
      show (↑i : ℕ) < P.n + 1 from by omega, dif_pos]
    congr 1
  rw [Finset.sum_range_sub]
  simp only [g, show P.n < P.n + 1 from by omega, show (0 : ℕ) < P.n + 1 from by omega, dif_pos]
  rw [show (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n from Fin.ext rfl,
    show (⟨0, by omega⟩ : Fin (P.n + 1)) = (0 : Fin (P.n + 1)) from Fin.ext rfl,
    P.last, P.first]

/-- Every tag `ξ_i` of a tagged partition of `[a,b]` lies in `[a,b]`. -/
lemma TaggedPartition.tag_mem_Icc (T : TaggedPartition a b) (hab : a ≤ b) (i : Fin T.n) :
    T.tags i ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = T.points 0 := T.first.symm
      _ ≤ T.points i.castSucc := T.ordered.monotone (Fin.zero_le _)
      _ ≤ T.tags i := (T.tag_mem i).1
  · calc T.tags i ≤ T.points i.succ := (T.tag_mem i).2
      _ ≤ T.points (Fin.last T.n) := T.ordered.monotone (Fin.le_last _)
      _ = b := T.last

/-- `T'` is a tagged refinement of `T` when every subinterval of `T'` is contained
in some subinterval of `T` (witnessed by `assign`), and the subintervals of `T'`
assigned to each `T`-subinterval telescope to its length. This captures the
condition `x ⊂ x'` in Theorem II. -/
structure TaggedPartition.IsTaggedRefinement (T T' : TaggedPartition a b) where
  assign : Fin T'.n → Fin T.n
  contained_left : ∀ j : Fin T'.n, T.points (assign j).castSucc ≤ T'.points j.castSucc
  contained_right : ∀ j : Fin T'.n, T'.points j.succ ≤ T.points (assign j).succ
  telescope : ∀ k : Fin T.n,
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (T'.points j.succ - T'.points j.castSucc) = T.points k.succ - T.points k.castSucc

/-- The Riemann sum `S_f(T)` can be rewritten by summing over the refinement `T'`:
each summand uses the tag of `T` at the parent subinterval and the length of the
finer `T'`-subinterval. -/
lemma riemannSum_eq_fiber (f : ℝ → ℝ) (T T' : TaggedPartition a b)
    (href : T.IsTaggedRefinement T') :
    riemannSum f T = ∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc) := by
  unfold riemannSum
  conv_lhs => arg 2; ext k; rw [← href.telescope k, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := href.assign) (fun i _ => Finset.mem_univ _)]
  congr 1; ext k
  apply Finset.sum_congr rfl
  intro j hj; simp only [Finset.mem_filter] at hj; rw [← hj.2]

/-- **Theorem II.** If `T'` is a tagged refinement of `T` (i.e. `x ⊂ x'`), then
for `f ∈ C([a,b])`,
`|S_f(T) - S_f(T')| ≤ w_f(‖T‖) · (b - a)`. -/
theorem riemannSum_sub_le_modulusOfContinuity_mul
    (f : ℝ → ℝ) (T T' : TaggedPartition a b) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (href : T.IsTaggedRefinement T') :
    |riemannSum f T - riemannSum f T'| ≤
      modulusOfContinuity f a b T.toPartition.mesh * (b - a) := by

  rw [riemannSum_eq_fiber f T T' href]

  have hdiff : (∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc)) -
    riemannSum f T' =
    ∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
      (T'.points j.succ - T'.points j.castSucc) := by
    unfold riemannSum
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  rw [hdiff]

  calc |∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)|
      ≤ ∑ j : Fin T'.n, |(f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin T'.n, |f (T.tags (href.assign j)) - f (T'.tags j)| *
          (T'.points j.succ - T'.points j.castSucc) := by
            congr 1; ext j
            rw [abs_mul, abs_of_nonneg (T'.toPartition.succ_sub_castSucc_nonneg j)]
    _ ≤ ∑ j : Fin T'.n, modulusOfContinuity f a b T.toPartition.mesh *
          (T'.points j.succ - T'.points j.castSucc) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _ (T'.toPartition.succ_sub_castSucc_nonneg j)

            apply le_modulusOfContinuity f T.toPartition.mesh hf
            · exact T.tag_mem_Icc hab (href.assign j)
            · exact T'.tag_mem_Icc hab j
            ·
              set k := href.assign j
              have htk := T.tag_mem k
              have htj := T'.tag_mem j
              have hleft := href.contained_left j
              have hright := href.contained_right j
              have habs : |T.tags k - T'.tags j| ≤ T.points k.succ - T.points k.castSucc := by
                rw [abs_le]
                exact ⟨by linarith [htk.1, htj.2, hright],
                       by linarith [htj.1, hleft, htk.2]⟩
              exact habs.trans (T.toPartition.le_mesh k)
    _ = modulusOfContinuity f a b T.toPartition.mesh * (b - a) := by
            rw [← Finset.mul_sum, T'.toPartition.sum_sub_eq]

/-- **Theorem III (given a common refinement).** For tagged partitions `T₁, T₂`
that share a common tagged refinement `T''`, and `f ∈ C([a,b])`,
`|S_f(T₁) - S_f(T₂)| ≤ (w_f(‖T₁‖) + w_f(‖T₂‖)) · (b - a)`. -/
theorem riemannSum_sub_le_modulusOfContinuity_add_mul_of_commonRefinement
    (f : ℝ → ℝ) (T₁ T₂ : TaggedPartition a b) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (T'' : TaggedPartition a b)
    (href₁ : T₁.IsTaggedRefinement T'')
    (href₂ : T₂.IsTaggedRefinement T'') :
    |riemannSum f T₁ - riemannSum f T₂| ≤
      (modulusOfContinuity f a b T₁.toPartition.mesh +
       modulusOfContinuity f a b T₂.toPartition.mesh) * (b - a) := by
  have h1 := riemannSum_sub_le_modulusOfContinuity_mul f T₁ T'' hab hf href₁
  have h2 := riemannSum_sub_le_modulusOfContinuity_mul f T₂ T'' hab hf href₂
  calc |riemannSum f T₁ - riemannSum f T₂|
      = |(riemannSum f T₁ - riemannSum f T'') + (riemannSum f T'' - riemannSum f T₂)| := by
          ring_nf
    _ ≤ |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T'' - riemannSum f T₂| :=
          abs_add_le _ _
    _ = |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T₂ - riemannSum f T''| := by
          rw [abs_sub_comm (riemannSum f T'') (riemannSum f T₂)]
    _ ≤ modulusOfContinuity f a b T₁.toPartition.mesh * (b - a) +
        modulusOfContinuity f a b T₂.toPartition.mesh * (b - a) := by
          linarith
    _ = (modulusOfContinuity f a b T₁.toPartition.mesh +
         modulusOfContinuity f a b T₂.toPartition.mesh) * (b - a) := by
          ring

/-- Telescoping identity: given a strictly monotone embedding `φ` of a coarse
index set into a fine index set, the lengths of the fine subintervals whose
indices are assigned to a coarse index `k` sum to the length of the `k`-th
coarse subinterval. -/
lemma telescope_sum_of_embedding {n'' m : ℕ} (pts : Fin (n'' + 1) → ℝ)
    (φ : Fin (m + 1) → Fin (n'' + 1)) (hφ_strict : StrictMono φ)
    (assign : Fin n'' → Fin m)
    (hassign_spec : ∀ j : Fin n'', (φ (assign j).castSucc).val ≤ j.val ∧
      j.val < (φ (assign j).succ).val)
    (k : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (pts j.succ - pts j.castSucc) = pts (φ k.succ) - pts (φ k.castSucc) := by
  have hfilter_eq : Finset.univ.filter (fun j : Fin n'' => assign j = k) =
      Finset.univ.filter (fun j : Fin n'' => (φ k.castSucc).val ≤ j.val ∧
        j.val < (φ k.succ).val) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; have := hassign_spec j; rw [h] at this; exact this
    · intro ⟨hleft, hright⟩
      by_contra hne
      have hspec := hassign_spec j
      rcases Fin.lt_or_lt_of_ne hne with h | h
      · have h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.2; omega
      · have h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.1; omega
  rw [hfilter_eq]
  set a' := (φ k.castSucc).val; set b' := (φ k.succ).val
  have hab' : a' ≤ b' := (hφ_strict Fin.castSucc_lt_succ).le
  have hb'_lt : b' < n'' + 1 := (φ k.succ).isLt
  let g : ℕ → ℝ := fun i => if h : i < n'' + 1 then pts ⟨i, h⟩ else 0
  suffices hsuff : ∀ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
      pts j.succ - pts j.castSucc = g (j.val + 1) - g j.val by
    rw [Finset.sum_congr rfl hsuff]
    have hbij : ∑ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
        (g (↑j + 1) - g ↑j) = ∑ i ∈ Finset.Ico a' b', (g (i + 1) - g i) :=
      Finset.sum_nbij (fun j => j.val)
        (fun j hj => Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun i hi => ⟨⟨i, by have := (Finset.mem_Ico.mp hi).2; omega⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_Ico.mp hi⟩, rfl⟩)
        (fun _ _ => rfl)
    rw [hbij, Finset.sum_Ico_sub g hab']
    simp only [g, hb'_lt, Nat.lt_of_le_of_lt hab' hb'_lt, dif_pos]
    congr 1 <;> congr 1 <;> simp only [Fin.val]
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  simp only [g, show j.val < n'' + 1 from by omega,
    show j.val + 1 < n'' + 1 from by omega, dif_pos]
  congr 1 <;> congr 1 <;> simp only [Fin.val_succ, Fin.val]

/-- Any two tagged partitions of `[a,b]` admit a common tagged refinement:
the partition whose points are the union of both partitions' points. -/
theorem TaggedPartition.exists_commonRefinement (T₁ T₂ : TaggedPartition a b) (hab : a ≤ b) :
    ∃ T'' : TaggedPartition a b,
      Nonempty (T₁.IsTaggedRefinement T'') ∧ Nonempty (T₂.IsTaggedRefinement T'') := by
  classical

  let S := (Finset.image T₁.points Finset.univ) ∪ (Finset.image T₂.points Finset.univ)
  have ha_mem : a ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, T₁.first⟩)
  have hb_mem : b ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last T₁.n, Finset.mem_univ _, T₁.last⟩)
  have hS_ne : S.Nonempty := ⟨a, ha_mem⟩
  set n'' := S.card - 1
  have hS_card_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
  have hcard : S.card = n'' + 1 := by omega


  let pts := S.orderEmbOfFin hcard
  have hpts_strict : StrictMono pts := (S.orderEmbOfFin hcard).strictMono

  have hmin : S.min' hS_ne = a := by
    apply le_antisymm (Finset.min'_le _ _ ha_mem)
    apply Finset.le_min'; intro x hx
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · linarith [T₁.first, T₁.ordered.monotone (Fin.zero_le i)]
    · linarith [T₂.first, T₂.ordered.monotone (Fin.zero_le i)]
  have hmax : S.max' hS_ne = b := by
    apply le_antisymm
    · apply Finset.max'_le; intro x hx
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · linarith [T₁.last, T₁.ordered.monotone (Fin.le_last i)]
      · linarith [T₂.last, T₂.ordered.monotone (Fin.le_last i)]
    · exact Finset.le_max' _ _ hb_mem

  have hpts_first : pts ⟨0, by omega⟩ = a :=
    (Finset.orderEmbOfFin_zero hcard (by omega)).trans hmin
  have hpts_last : pts (Fin.last n'') = b := by
    have h := Finset.orderEmbOfFin_last hcard (by omega : 0 < n'' + 1)
    have heq : (⟨n'' + 1 - 1, (by omega)⟩ : Fin (n'' + 1)) = Fin.last n'' :=
      Fin.ext (by simp [Fin.last])
    rw [heq] at h; exact h.trans hmax

  let T'' : TaggedPartition a b := {
    n := n''
    points := pts
    ordered := hpts_strict
    first := hpts_first
    last := hpts_last
    tags := fun i => pts i.castSucc
    tag_mem := fun i => ⟨le_refl _, (hpts_strict Fin.castSucc_lt_succ).le⟩
  }

  have hT₁_sub : ∀ i, T₁.points i ∈ S :=
    fun i => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hT₂_sub : ∀ i, T₂.points i ∈ S :=
    fun i => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

  let φ₁ : Fin (T₁.n + 1) → Fin (n'' + 1) :=
    fun i => (S.orderIsoOfFin hcard).symm ⟨T₁.points i, hT₁_sub i⟩
  let φ₂ : Fin (T₂.n + 1) → Fin (n'' + 1) :=
    fun i => (S.orderIsoOfFin hcard).symm ⟨T₂.points i, hT₂_sub i⟩
  have hφ₁_strict : StrictMono φ₁ := fun i j hij =>
    (S.orderIsoOfFin hcard).symm.strictMono (Subtype.mk_lt_mk.mpr (T₁.ordered hij))
  have hφ₂_strict : StrictMono φ₂ := fun i j hij =>
    (S.orderIsoOfFin hcard).symm.strictMono (Subtype.mk_lt_mk.mpr (T₂.ordered hij))

  have hφ₁_spec : ∀ i, pts (φ₁ i) = T₁.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₁.points i, hT₁_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm
  have hφ₂_spec : ∀ i, pts (φ₂ i) = T₂.points i := fun i => by
    have h := Finset.coe_orderIsoOfFin_apply S hcard
      ((S.orderIsoOfFin hcard).symm ⟨T₂.points i, hT₂_sub i⟩)
    rw [OrderIso.apply_symm_apply] at h; exact h.symm

  have hφ₁_zero : (φ₁ 0).val = 0 := by
    have h1 : pts (φ₁ 0) = a := (hφ₁_spec 0).trans T₁.first
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_first.symm)
    exact congr_arg Fin.val h3
  have hφ₂_zero : (φ₂ 0).val = 0 := by
    have h1 : pts (φ₂ 0) = a := (hφ₂_spec 0).trans T₂.first
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_first.symm)
    exact congr_arg Fin.val h3

  have hφ₁_last : (φ₁ (Fin.last T₁.n)).val = n'' := by
    have h1 : pts (φ₁ (Fin.last T₁.n)) = b := (hφ₁_spec _).trans T₁.last
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_last.symm)
    have : (Fin.last n'').val = n'' := rfl
    linarith [congr_arg Fin.val h3, this]
  have hφ₂_last : (φ₂ (Fin.last T₂.n)).val = n'' := by
    have h1 : pts (φ₂ (Fin.last T₂.n)) = b := (hφ₂_spec _).trans T₂.last
    have h3 := (S.orderEmbOfFin hcard).injective (h1.trans hpts_last.symm)
    have : (Fin.last n'').val = n'' := rfl
    linarith [congr_arg Fin.val h3, this]

  have mk_assign₁ : ∀ j : Fin n'', ∃ k : Fin T₁.n,
      (φ₁ k.castSucc).val ≤ j.val ∧ j.val < (φ₁ k.succ).val := by
    intro j

    let good := Finset.univ.filter (fun i : Fin (T₁.n + 1) => (φ₁ i).val ≤ j.val)
    have hgood_ne : good.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hlast_not : Fin.last T₁.n ∉ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      have := hφ₁_last; have := j.isLt; omega
    set k₀ := good.max' hgood_ne
    have hk₀_mem := Finset.max'_mem good hgood_ne
    have hk₀_le : (φ₁ k₀).val ≤ j.val := (Finset.mem_filter.mp hk₀_mem).2
    have hk₀_lt_last : k₀ < Fin.last T₁.n := by
      rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
      · exact h
      · exact absurd (h ▸ hk₀_mem) hlast_not
    have hk₀_val_lt : k₀.val < T₁.n := by simp [Fin.lt_def, Fin.last] at hk₀_lt_last; exact hk₀_lt_last
    refine ⟨⟨k₀.val, hk₀_val_lt⟩, ?_, ?_⟩
    · have : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₁.n).castSucc = k₀ := Fin.ext rfl
      rw [this]; exact hk₀_le
    · have hsucc_eq : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₁.n).succ = ⟨k₀.val + 1, by omega⟩ :=
        Fin.ext (by simp [Fin.succ])
      rw [hsucc_eq]
      have hsucc_not : (⟨k₀.val + 1, (by omega : k₀.val + 1 < T₁.n + 1)⟩ : Fin (T₁.n + 1)) ∉ good := by
        intro hmem
        have hle := Finset.le_max' good _ hmem
        simp [Fin.le_def] at hle; omega
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsucc_not
      exact hsucc_not
  have mk_assign₂ : ∀ j : Fin n'', ∃ k : Fin T₂.n,
      (φ₂ k.castSucc).val ≤ j.val ∧ j.val < (φ₂ k.succ).val := by
    intro j
    let good := Finset.univ.filter (fun i : Fin (T₂.n + 1) => (φ₂ i).val ≤ j.val)
    have hgood_ne : good.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hlast_not : Fin.last T₂.n ∉ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      have := hφ₂_last; have := j.isLt; omega
    set k₀ := good.max' hgood_ne
    have hk₀_mem := Finset.max'_mem good hgood_ne
    have hk₀_le : (φ₂ k₀).val ≤ j.val := (Finset.mem_filter.mp hk₀_mem).2
    have hk₀_lt_last : k₀ < Fin.last T₂.n := by
      rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
      · exact h
      · exact absurd (h ▸ hk₀_mem) hlast_not
    have hk₀_val_lt : k₀.val < T₂.n := by simp [Fin.lt_def, Fin.last] at hk₀_lt_last; exact hk₀_lt_last
    refine ⟨⟨k₀.val, hk₀_val_lt⟩, ?_, ?_⟩
    · have : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₂.n).castSucc = k₀ := Fin.ext rfl
      rw [this]; exact hk₀_le
    · have hsucc_eq : (⟨k₀.val, hk₀_val_lt⟩ : Fin T₂.n).succ = ⟨k₀.val + 1, by omega⟩ :=
        Fin.ext (by simp [Fin.succ])
      rw [hsucc_eq]
      have hsucc_not : (⟨k₀.val + 1, (by omega : k₀.val + 1 < T₂.n + 1)⟩ : Fin (T₂.n + 1)) ∉ good := by
        intro hmem
        have hle := Finset.le_max' good _ hmem
        simp [Fin.le_def] at hle; omega
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsucc_not
      exact hsucc_not


  let assign₁ : Fin n'' → Fin T₁.n := fun j => (mk_assign₁ j).choose
  let assign₂ : Fin n'' → Fin T₂.n := fun j => (mk_assign₂ j).choose
  have hassign₁_spec : ∀ j, (φ₁ (assign₁ j).castSucc).val ≤ j.val ∧
      j.val < (φ₁ (assign₁ j).succ).val := fun j => (mk_assign₁ j).choose_spec
  have hassign₂_spec : ∀ j, (φ₂ (assign₂ j).castSucc).val ≤ j.val ∧
      j.val < (φ₂ (assign₂ j).succ).val := fun j => (mk_assign₂ j).choose_spec
  refine ⟨T'', ⟨?_⟩, ⟨?_⟩⟩
  · exact {
      assign := assign₁
      contained_left := fun j => by
        rw [← hφ₁_spec (assign₁ j).castSucc]
        exact hpts_strict.monotone (hassign₁_spec j).1
      contained_right := fun j => by
        rw [← hφ₁_spec (assign₁ j).succ]
        exact hpts_strict.monotone (Nat.lt_iff_add_one_le.mp (hassign₁_spec j).2)
      telescope := fun k => by
        show ∑ j ∈ Finset.univ.filter (fun j => assign₁ j = k),
          (pts j.succ - pts j.castSucc) = T₁.points k.succ - T₁.points k.castSucc
        rw [← hφ₁_spec k.succ, ← hφ₁_spec k.castSucc]
        exact telescope_sum_of_embedding pts φ₁ hφ₁_strict assign₁ hassign₁_spec k
    }
  · exact {
      assign := assign₂
      contained_left := fun j => by
        rw [← hφ₂_spec (assign₂ j).castSucc]
        exact hpts_strict.monotone (hassign₂_spec j).1
      contained_right := fun j => by
        rw [← hφ₂_spec (assign₂ j).succ]
        exact hpts_strict.monotone (Nat.lt_iff_add_one_le.mp (hassign₂_spec j).2)
      telescope := fun k => by
        show ∑ j ∈ Finset.univ.filter (fun j => assign₂ j = k),
          (pts j.succ - pts j.castSucc) = T₂.points k.succ - T₂.points k.castSucc
        rw [← hφ₂_spec k.succ, ← hφ₂_spec k.castSucc]
        exact telescope_sum_of_embedding pts φ₂ hφ₂_strict assign₂ hassign₂_spec k
    }

/-- **Theorem III.** For any two tagged partitions `T₁, T₂` of `[a,b]` and
`f ∈ C([a,b])`,
`|S_f(T₁) - S_f(T₂)| ≤ (w_f(‖T₁‖) + w_f(‖T₂‖)) · (b - a)`. -/
theorem riemannSum_sub_le_modulusOfContinuity_add_mul
    (f : ℝ → ℝ) (T₁ T₂ : TaggedPartition a b) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    |riemannSum f T₁ - riemannSum f T₂| ≤
      (modulusOfContinuity f a b T₁.toPartition.mesh +
       modulusOfContinuity f a b T₂.toPartition.mesh) * (b - a) := by
  obtain ⟨T'', ⟨href₁⟩, ⟨href₂⟩⟩ := TaggedPartition.exists_commonRefinement T₁ T₂ hab
  exact riemannSum_sub_le_modulusOfContinuity_add_mul_of_commonRefinement
    f T₁ T₂ hab hf T'' href₁ href₂

/-- For `f ∈ C([a,b])` with `a < b`, if a sequence of tagged partitions has mesh
tending to `0`, then the corresponding sequence of Riemann sums is Cauchy. -/
lemma riemannSum_cauchySeq_of_mesh_tendsto (f : ℝ → ℝ) (a b : ℝ) (hab_lt : a < b)
    (hf : ContinuousOn f (Icc a b))
    (T : ℕ → TaggedPartition a b)
    (hmesh : Filter.Tendsto (fun r => (T r).toPartition.mesh) Filter.atTop (𝓝 0)) :
    CauchySeq (fun r => riemannSum f (T r)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hmod := modulusOfContinuity_tendsto_zero f a b (le_of_lt hab_lt) hf
  rw [Metric.tendsto_nhdsWithin_nhds] at hmod
  have hba_pos : (0 : ℝ) < b - a := sub_pos.mpr hab_lt
  have hε' : (0 : ℝ) < ε / (2 * (b - a)) := div_pos hε (mul_pos two_pos hba_pos)
  obtain ⟨δ, hδ, hmod_bound⟩ := hmod (ε / (2 * (b - a))) hε'
  rw [Metric.tendsto_atTop] at hmesh
  obtain ⟨N, hN⟩ := hmesh δ hδ
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [Real.dist_eq]
  have hbound := riemannSum_sub_le_modulusOfContinuity_add_mul f (T m) (T n)
    (le_of_lt hab_lt) hf
  have hmesh_m_pos : (0 : ℝ) < (T m).toPartition.mesh :=
    Partition.mesh_pos_of_lt hab_lt (T m).toPartition
  have hmesh_m_lt : (T m).toPartition.mesh < δ := by
    have := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hmesh_m_pos.le] at this
    exact this
  have hmod_m := hmod_bound (mem_Ioi.mpr hmesh_m_pos) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmesh_m_pos]; exact hmesh_m_lt)
  have hmesh_n_pos : (0 : ℝ) < (T n).toPartition.mesh :=
    Partition.mesh_pos_of_lt hab_lt (T n).toPartition
  have hmesh_n_lt : (T n).toPartition.mesh < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hmesh_n_pos.le] at this
    exact this
  have hmod_n := hmod_bound (mem_Ioi.mpr hmesh_n_pos) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmesh_n_pos]; exact hmesh_n_lt)
  rw [Real.dist_eq, sub_zero] at hmod_m hmod_n
  calc |riemannSum f (T m) - riemannSum f (T n)|
      ≤ (modulusOfContinuity f a b (T m).toPartition.mesh +
         modulusOfContinuity f a b (T n).toPartition.mesh) * (b - a) := hbound
    _ ≤ (|modulusOfContinuity f a b (T m).toPartition.mesh| +
         |modulusOfContinuity f a b (T n).toPartition.mesh|) * (b - a) := by
          apply mul_le_mul_of_nonneg_right _ hba_pos.le
          exact add_le_add (le_abs_self _) (le_abs_self _)
    _ < (ε / (2 * (b - a)) + ε / (2 * (b - a))) * (b - a) := by
          apply mul_lt_mul_of_pos_right _ hba_pos
          exact add_lt_add hmod_m hmod_n
    _ = ε := by field_simp; ring

/-- For `f ∈ C([a,b])` with `a < b`, if two sequences of tagged partitions both
have meshes tending to `0`, then the difference of their Riemann sums tends to
`0`. -/
lemma riemannSum_sub_tendsto_zero (f : ℝ → ℝ) (a b : ℝ) (hab_lt : a < b)
    (hf : ContinuousOn f (Icc a b))
    (T₁ T₂ : ℕ → TaggedPartition a b)
    (hmesh₁ : Filter.Tendsto (fun r => (T₁ r).toPartition.mesh) Filter.atTop (𝓝 0))
    (hmesh₂ : Filter.Tendsto (fun r => (T₂ r).toPartition.mesh) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun r => riemannSum f (T₁ r) - riemannSum f (T₂ r))
      Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmod := modulusOfContinuity_tendsto_zero f a b (le_of_lt hab_lt) hf
  rw [Metric.tendsto_nhdsWithin_nhds] at hmod
  have hba_pos : (0 : ℝ) < b - a := sub_pos.mpr hab_lt
  have hε' : (0 : ℝ) < ε / (2 * (b - a)) := div_pos hε (mul_pos two_pos hba_pos)
  obtain ⟨δ, hδ, hmod_bound⟩ := hmod (ε / (2 * (b - a))) hε'
  rw [Metric.tendsto_atTop] at hmesh₁ hmesh₂
  obtain ⟨N₁, hN₁⟩ := hmesh₁ δ hδ
  obtain ⟨N₂, hN₂⟩ := hmesh₂ δ hδ
  refine ⟨max N₁ N₂, fun r hr => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hr₁ : N₁ ≤ r := le_of_max_le_left hr
  have hr₂ : N₂ ≤ r := le_of_max_le_right hr
  have hbound := riemannSum_sub_le_modulusOfContinuity_add_mul f (T₁ r) (T₂ r)
    (le_of_lt hab_lt) hf
  have hmesh₁_pos : (0 : ℝ) < (T₁ r).toPartition.mesh :=
    Partition.mesh_pos_of_lt hab_lt (T₁ r).toPartition
  have hmesh₁_lt : (T₁ r).toPartition.mesh < δ := by
    have := hN₁ r hr₁
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hmesh₁_pos.le] at this
    exact this
  have hmod₁ := hmod_bound (mem_Ioi.mpr hmesh₁_pos) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmesh₁_pos]; exact hmesh₁_lt)
  have hmesh₂_pos : (0 : ℝ) < (T₂ r).toPartition.mesh :=
    Partition.mesh_pos_of_lt hab_lt (T₂ r).toPartition
  have hmesh₂_lt : (T₂ r).toPartition.mesh < δ := by
    have := hN₂ r hr₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hmesh₂_pos.le] at this
    exact this
  have hmod₂ := hmod_bound (mem_Ioi.mpr hmesh₂_pos) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmesh₂_pos]; exact hmesh₂_lt)
  rw [Real.dist_eq, sub_zero] at hmod₁ hmod₂
  calc |riemannSum f (T₁ r) - riemannSum f (T₂ r)|
      ≤ (modulusOfContinuity f a b (T₁ r).toPartition.mesh +
         modulusOfContinuity f a b (T₂ r).toPartition.mesh) * (b - a) := hbound
    _ ≤ (|modulusOfContinuity f a b (T₁ r).toPartition.mesh| +
         |modulusOfContinuity f a b (T₂ r).toPartition.mesh|) * (b - a) := by
          apply mul_le_mul_of_nonneg_right _ hba_pos.le
          exact add_le_add (le_abs_self _) (le_abs_self _)
    _ < (ε / (2 * (b - a)) + ε / (2 * (b - a))) * (b - a) := by
          apply mul_lt_mul_of_pos_right _ hba_pos
          exact add_lt_add hmod₁ hmod₂
    _ = ε := by field_simp; ring

/-- **Convergence of the Riemann integral.** For `f ∈ C([a,b])`, there exists a
real number `I` such that for every sequence of tagged partitions whose mesh
tends to `0`, the Riemann sums converge to `I`. -/
theorem riemann_integral_convergence (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ I : ℝ, ∀ (T : ℕ → TaggedPartition a b),
      Filter.Tendsto (fun r => (T r).toPartition.mesh) Filter.atTop (𝓝 0) →
      Filter.Tendsto (fun r => riemannSum f (T r)) Filter.atTop (𝓝 I) := by
  rcases hab.eq_or_lt with rfl | hab_lt
  ·
    refine ⟨0, fun T _ => ?_⟩
    have hzero : ∀ r, riemannSum f (T r) = 0 := by
      intro r
      have hn : (T r).n = 0 := by
        by_contra h
        have hpos : 0 < (T r).n := Nat.pos_of_ne_zero h
        have h0lt : (0 : Fin ((T r).n + 1)) < Fin.last (T r).n := by
          simp [Fin.lt_def]; omega
        have := (T r).ordered h0lt
        linarith [(T r).first, (T r).last]
      exact riemannSum_eq_zero_of_n_eq_zero f (T r) hn
    simp_rw [hzero]
    exact tendsto_const_nhds
  ·


    have hCauchy : ∀ (T : ℕ → TaggedPartition a b),
        Filter.Tendsto (fun r => (T r).toPartition.mesh) Filter.atTop (𝓝 0) →
        ∃ I : ℝ, Filter.Tendsto (fun r => riemannSum f (T r)) Filter.atTop (𝓝 I) :=
      fun T hmesh => ⟨_, (riemannSum_cauchySeq_of_mesh_tendsto f a b hab_lt hf T hmesh).tendsto_limUnder⟩

    have hUniq : ∀ (T₁ T₂ : ℕ → TaggedPartition a b)
        (hmesh₁ : Filter.Tendsto (fun r => (T₁ r).toPartition.mesh) Filter.atTop (𝓝 0))
        (hmesh₂ : Filter.Tendsto (fun r => (T₂ r).toPartition.mesh) Filter.atTop (𝓝 0))
        (I₁ I₂ : ℝ)
        (hI₁ : Filter.Tendsto (fun r => riemannSum f (T₁ r)) Filter.atTop (𝓝 I₁))
        (hI₂ : Filter.Tendsto (fun r => riemannSum f (T₂ r)) Filter.atTop (𝓝 I₂)),
        I₁ = I₂ := by
      intro T₁ T₂ hmesh₁ hmesh₂ I₁ I₂ hI₁ hI₂
      have hdiff := riemannSum_sub_tendsto_zero f a b hab_lt hf T₁ T₂ hmesh₁ hmesh₂
      have hlim : Filter.Tendsto (fun r => riemannSum f (T₁ r) - riemannSum f (T₂ r))
          Filter.atTop (𝓝 (I₁ - I₂)) :=
        hI₁.sub hI₂
      exact sub_eq_zero.mp (tendsto_nhds_unique hlim hdiff)


    by_cases h : ∃ (T₀ : ℕ → TaggedPartition a b),
        Filter.Tendsto (fun r => (T₀ r).toPartition.mesh) Filter.atTop (𝓝 0)
    · obtain ⟨T₀, hmesh₀⟩ := h
      obtain ⟨I, hI⟩ := hCauchy T₀ hmesh₀
      exact ⟨I, fun T hmesh => by
        obtain ⟨I', hI'⟩ := hCauchy T hmesh
        have heq := hUniq T₀ T hmesh₀ hmesh I I' hI hI'
        rw [heq]; exact hI'⟩
    ·
      exact ⟨0, fun T hmesh => absurd ⟨T, hmesh⟩ h⟩

end Integration
