/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section30
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.FiveLemma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Function

namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- **Conclusion of Theorem 32.1 for a compact subset `K`.** Packages the
two assertions of the orientation theorem for an `n`-manifold `M` and a
compact set `K ⊆ M`: the relative homology groups `Hrel q K` vanish for
`q > n`, and the comparison map `jMap K : Hrel n K → Γsec K` to sections
of the orientation sheaf is a bijection. Stated abstractly so that the
proof structure of Section 32 can be reused for any homology theory
`Hrel`/section functor `Γsec` satisfying the appropriate axioms. -/
structure OrientationTheoremResult
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [inst : ∀ q A, AddCommGroup (Hrel q A)]
    (Γsec : Set M → Type*)
    [inst' : ∀ A, AddCommGroup (Γsec A)]
    (jMap : (A : Set M) → Hrel n A →+ Γsec A)
    (K : Set M) : Prop where
  vanishing : ∀ q, q > n → ∀ x : Hrel q K, x = 0
  isomorphism : Bijective (jMap K)

/-- **Mayer–Vietoris ladder data for Proposition 32.2.** Records the
relevant portion of the commutative diagram with exact rows used to prove
that if the orientation theorem holds for `A`, `B`, and `A ∩ B`, then it
holds for `A ∪ B`: the top row is the relative-homology Mayer–Vietoris
sequence at degrees `n` and `q > n`, the bottom row is the
Mayer–Vietoris sequence for sections of the orientation sheaf, and
`jMap` provides the comparison map between them. -/
structure MayerVietorisLadder
    (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα : Hrel n (A ∪ B) →+ Hrel n A × Hrel n B
  mvβ : Hrel n A × Hrel n B →+ Hrel n (A ∩ B)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  mv_inj : ∀ x, mvα x = 0 → x = 0
  mv_exact : Exact mvα mvβ
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp mvα
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp mvβ
  mv_inj_q : ∀ q, q > n →
    ∃ (αq : Hrel q (A ∪ B) →+ Hrel q A × Hrel q B),
      ∀ x, αq x = 0 → x = 0

/-- Build a `MayerVietorisLadder` from the full Mayer–Vietoris long exact
sequences in `Hrel` and `Γsec` together with the commutation hypotheses.
Uses the vanishing part of the orientation theorem on `A ∩ B` to derive
injectivity of `mvα` and of the higher-degree maps `mvα_q` for `q > n`,
since their kernels lie in `Hrel (q+1) (A ∩ B) = 0`. -/
def MayerVietorisLadder.ofExactSequences
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) (_hA : IsClosed A) (_hB : IsClosed B)
    (_hOT_AB : OrientationTheoremResult n Hrel Γsec jMap (A ∩ B))

    (mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B)
    (mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B))
    (mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B))

    (mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q))
    (mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q))

    (secα : Γsec (A ∪ B) →+ Γsec A × Γsec B)
    (secβ : Γsec A × Γsec B →+ Γsec (A ∩ B))
    (sec_inj : ∀ x, secα x = 0 → x = 0)
    (sec_exact : Exact secα secβ)

    (comm_α : secα.comp (jMap (A ∪ B)) =
      (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n))
    (comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
      (jMap (A ∩ B)).comp (mvβ_q n)) :
    MayerVietorisLadder n Hrel Γsec jMap A B where
  mvα := mvα_q n
  mvβ := mvβ_q n
  secα := secα
  secβ := secβ
  mv_inj := by


    intro x hx

    obtain ⟨y, rfl⟩ := (mv_exact_δα n x).mp hx

    have hy : y = 0 := _hOT_AB.vanishing (n + 1) (by omega) y
    rw [hy, map_zero]
  mv_exact := mv_exact_αβ n
  sec_inj := sec_inj
  sec_exact := sec_exact
  comm_α := comm_α
  comm_β := comm_β
  mv_inj_q := by
    intro q hq
    exact ⟨mvα_q q, by
      intro x hx
      obtain ⟨y, rfl⟩ := (mv_exact_δα q x).mp hx

      have hy : y = 0 := _hOT_AB.vanishing (q + 1) (by omega) y
      rw [hy, map_zero]⟩

/-- **Proposition 32.2, ladder form.** Given the orientation theorem on
`A`, `B`, and `A ∩ B`, together with a Mayer–Vietoris ladder relating
their relative homologies and section groups, deduce the orientation
theorem on `A ∪ B`. The vanishing part follows from injectivity of `mvα`
in degrees `q > n`, and the bijectivity of `jMap (A ∪ B)` is obtained by
the five-lemma applied to the ladder. -/
theorem orientation_theorem_union_of_ladder
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A B : Set M) (_hA : IsClosed A) (_hB : IsClosed B)

    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)

    (hOT_A : OrientationTheoremResult n Hrel Γsec jMap A)
    (hOT_B : OrientationTheoremResult n Hrel Γsec jMap B)
    (hOT_AB : OrientationTheoremResult n Hrel Γsec jMap (A ∩ B))

    (ladder : MayerVietorisLadder n Hrel Γsec jMap A B) :
    OrientationTheoremResult n Hrel Γsec jMap (A ∪ B) := by
  constructor
  ·


    intro q hq x
    obtain ⟨αq, h_inj_q⟩ := ladder.mv_inj_q q hq
    have h_prod_zero : ∀ y : Hrel q A × Hrel q B, y = 0 :=
      fun ⟨a, b⟩ => Prod.ext (hOT_A.vanishing q hq a) (hOT_B.vanishing q hq b)
    have hα : αq x = 0 := h_prod_zero (αq x)
    exact h_inj_q x hα
  ·


    have j_prod_bij : Bijective (AddMonoidHom.prodMap (jMap A) (jMap B)) :=
      hOT_A.isomorphism.prodMap hOT_B.isomorphism
    have h_top_ex₁ : Exact (0 : PUnit.{1} →+ PUnit.{1})
        (0 : PUnit.{1} →+ Hrel n (A ∪ B)) := by
      intro ⟨⟩; simp [Set.mem_range]
    have h_top_ex₂ : Exact (0 : PUnit.{1} →+ Hrel n (A ∪ B)) ladder.mvα := by
      intro y; constructor
      · exact fun h => ⟨⟨⟩, (ladder.mv_inj y h).symm⟩
      · rintro ⟨⟨⟩, rfl⟩; simp
    have h_bot_ex₁ : Exact (0 : PUnit.{1} →+ PUnit.{1})
        (0 : PUnit.{1} →+ Γsec (A ∪ B)) := by
      intro ⟨⟩; simp [Set.mem_range]
    have h_bot_ex₂ : Exact (0 : PUnit.{1} →+ Γsec (A ∪ B)) ladder.secα := by
      intro y; constructor
      · exact fun h => ⟨⟨⟩, (ladder.sec_inj y h).symm⟩
      · rintro ⟨⟨⟩, rfl⟩; simp
    have h_comm_zero : (0 : PUnit.{1} →+ Γsec (A ∪ B)).comp
        (0 : PUnit.{1} →+ PUnit.{1}) =
        (jMap (A ∪ B)).comp (0 : PUnit.{1} →+ Hrel n (A ∪ B)) := by
      ext ⟨⟩; simp
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective

      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ Hrel n (A ∪ B))
      ladder.mvα ladder.mvβ

      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ Γsec (A ∪ B))
      ladder.secα ladder.secβ

      (0 : PUnit.{1} →+ PUnit.{1}) (0 : PUnit.{1} →+ PUnit.{1})
      (jMap (A ∪ B)) (AddMonoidHom.prodMap (jMap A) (jMap B)) (jMap (A ∩ B))

      rfl h_comm_zero ladder.comm_α ladder.comm_β

      h_top_ex₁ h_top_ex₂ ladder.mv_exact

      h_bot_ex₁ h_bot_ex₂ ladder.sec_exact


      (fun ⟨⟩ => ⟨⟨⟩, rfl⟩)

      ⟨fun _ _ _ => Subsingleton.elim _ _, fun ⟨⟩ => ⟨⟨⟩, rfl⟩⟩

      j_prod_bij

      hOT_AB.isomorphism.injective

/-- Abstract data of the relative Mayer–Vietoris long exact sequences in
all degrees together with the section-sequence and compatibility
conditions, packaged so that `MayerVietorisLadder.ofExactSequences` can
be invoked from a single bundle. -/
structure RelativeMVSequenceData
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (A B : Set M) where
  mvα_q : ∀ q, Hrel q (A ∪ B) →+ Hrel q A × Hrel q B
  mvβ_q : ∀ q, Hrel q A × Hrel q B →+ Hrel q (A ∩ B)
  mvδ_q : ∀ q, Hrel (q + 1) (A ∩ B) →+ Hrel q (A ∪ B)
  mv_exact_δα : ∀ q, Exact (mvδ_q q) (mvα_q q)
  mv_exact_αβ : ∀ q, Exact (mvα_q q) (mvβ_q q)
  secα : Γsec (A ∪ B) →+ Γsec A × Γsec B
  secβ : Γsec A × Γsec B →+ Γsec (A ∩ B)
  sec_inj : ∀ x, secα x = 0 → x = 0
  sec_exact : Exact secα secβ
  comm_α : secα.comp (jMap (A ∪ B)) =
    (AddMonoidHom.prodMap (jMap A) (jMap B)).comp (mvα_q n)
  comm_β : secβ.comp (AddMonoidHom.prodMap (jMap A) (jMap B)) =
    (jMap (A ∩ B)).comp (mvβ_q n)




/-- **Lemma 32.5.** In a Hausdorff space, given a decreasing sequence
`A₀ ⊇ A₁ ⊇ ⋯` of compact subsets and an open set `U` containing the
intersection `⋂ i, A i`, some term `A i` is already contained in `U`.
Proved by contradiction using compactness of the nonempty closed sets
`A i \ U`. -/
theorem compact_decreasing_sequence_subset_open {X : Type*} [TopologicalSpace X] [T2Space X]
    (A : ℕ → Set X) (hA_compact : ∀ i, IsCompact (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (U : Set X) (hU_open : IsOpen U)
    (hAU : ⋂ i, A i ⊆ U) :
    ∃ i, A i ⊆ U := by
  by_contra h
  push Not at h

  have hne : ∀ i, (A i \ U).Nonempty :=
    fun i => Set.nonempty_of_not_subset (h i)

  have hdecr : ∀ i, A (i + 1) \ U ⊆ A i \ U :=
    fun i => diff_subset_diff_left (hA_decreasing i)

  have hclosed : ∀ i, IsClosed (A i \ U) :=
    fun i => (hA_compact i).isClosed.sdiff hU_open

  have hcompact0 : IsCompact (A 0 \ U) := (hA_compact 0).diff hU_open

  have hinter := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun i => A i \ U) hdecr hne hcompact0 hclosed

  have heq : ⋂ i, A i \ U = (⋂ i, A i) \ U := by
    simp only [diff_eq]
    exact (iInter_inter Uᶜ A).symm

  rw [heq, Set.diff_eq_empty.mpr hAU] at hinter
  exact Set.not_nonempty_empty hinter

variable {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {Hrel : ℕ → Set M → Type*}
  [∀ q K, AddCommGroup (Hrel q K)]
  {Γsec : Set M → Type*}
  [∀ K, AddCommGroup (Γsec K)]
  {jMap : (K : Set M) → Hrel n K →+ Γsec K}

/-- Iterated form of the union step (Proposition 32.2): if the
`union_step` hypothesis is available, then the orientation theorem
propagates from intersections `⋂ i ∈ S, D i` along nonempty finite
families to the union `⋃ i ∈ T, D i` over any nonempty finite index set
`T` with `T.card ≤ k`. Proved by induction on `k`, peeling off one
element at a time and applying `union_step`. -/
lemma result_finset_biUnion
    {ι : Type*} [DecidableEq ι]
    (union_step : ∀ (K₁ K₂ : Set M),
      IsClosed K₁ → IsClosed K₂ →
      OrientationTheoremResult n Hrel Γsec jMap K₁ →
      OrientationTheoremResult n Hrel Γsec jMap K₂ →
      OrientationTheoremResult n Hrel Γsec jMap (K₁ ∩ K₂) →
      OrientationTheoremResult n Hrel Γsec jMap (K₁ ∪ K₂))
    : ∀ (k : ℕ) (D : ι → Set M) (_ : ∀ i, IsClosed (D i))
    (_ : ∀ (S : Finset ι), S.Nonempty →
      OrientationTheoremResult n Hrel Γsec jMap (⋂ i ∈ S, D i))
    (T : Finset ι) (_ : T.Nonempty) (_ : T.card ≤ k),
    OrientationTheoremResult n Hrel Γsec jMap (⋃ i ∈ T, D i) := by
  intro k
  induction k with
  | zero =>
    intro D _ _ T hT hk
    have := hT.card_pos; omega
  | succ k ih =>
    intro D hD_closed hbase T hT hk
    obtain ⟨j, hj⟩ := hT
    by_cases hT' : (T.erase j).Nonempty
    · have hcard_erase : (T.erase j).card ≤ k := by
        have := Finset.card_erase_of_mem hj; omega
      have hT_eq : (⋃ i ∈ T, D i) = D j ∪ (⋃ i ∈ T.erase j, D i) := by
        rw [show T = insert j (T.erase j) from (Finset.insert_erase hj).symm]; simp
      rw [hT_eq]
      apply union_step
      · exact hD_closed j
      · exact isClosed_biUnion_finset (fun i _ => hD_closed i)
      · have : D j = ⋂ i ∈ ({j} : Finset ι), D i := by simp
        rw [this]; exact hbase {j} (Finset.singleton_nonempty j)
      · exact ih D hD_closed hbase (T.erase j) hT' hcard_erase
      · rw [inter_iUnion₂]
        apply ih (fun i => D j ∩ D i)
          (fun i => (hD_closed j).inter (hD_closed i))
          (fun S hS => by
            have : (⋂ i ∈ S, (D j ∩ D i)) = ⋂ i ∈ insert j S, D i := by
              ext x; simp only [mem_iInter, Finset.mem_insert, mem_inter_iff]
              constructor
              · intro h i hi
                rcases hi with rfl | hi
                · obtain ⟨s, hs⟩ := hS; exact (h s hs).1
                · exact (h i hi).2
              · intro h i hi; exact ⟨h j (Or.inl rfl), h i (Or.inr hi)⟩
            rw [this]
            exact hbase (insert j S) (Finset.insert_nonempty j S))
          (T.erase j) hT' hcard_erase
    · rw [Finset.not_nonempty_iff_eq_empty] at hT'
      have hT_single : T = {j} := by
        rw [← Finset.insert_erase hj, hT']; simp
      rw [hT_single]; simp
      have : D j = ⋂ i ∈ ({j} : Finset ι), D i := by simp
      rw [this]; exact hbase {j} (Finset.singleton_nonempty j)

/-- Reduces the orientation theorem for a compact `A ⊆ M` to the case of
intersections `A ∩ ⋂ i ∈ S, D i` where `D : Fin m → Set M` is a finite
closed cover of `A`. Combines `result_finset_biUnion` with the
decomposition `A = ⋃ i, A ∩ D i`. -/
theorem orientation_theorem_from_cover
    (n : ℕ) (A : Set M)
    [AlgebraicTopologyI.TopologicalManifold n M]

    (_hA_compact : IsCompact A)
    (hA_closed : IsClosed A)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (m : ℕ) (D : Fin m → Set M)
    (hD_closed : ∀ i, IsClosed (D i))
    (hD_cover : A ⊆ ⋃ i, D i)
    (hD_result : ∀ (S : Finset (Fin m)), S.Nonempty →
      OrientationTheoremResult n Hrel Γsec jMap (A ∩ ⋂ i ∈ S, D i))
    (union_step : ∀ (K₁ K₂ : Set M),
      IsClosed K₁ → IsClosed K₂ →
      OrientationTheoremResult n Hrel Γsec jMap K₁ →
      OrientationTheoremResult n Hrel Γsec jMap K₂ →
      OrientationTheoremResult n Hrel Γsec jMap (K₁ ∩ K₂) →
      OrientationTheoremResult n Hrel Γsec jMap (K₁ ∪ K₂))
    (hm_pos : 0 < m) :
    OrientationTheoremResult n Hrel Γsec jMap A := by
  have hA_eq : A = ⋃ i ∈ (Finset.univ : Finset (Fin m)), (A ∩ D i) := by
    ext x; simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hD_cover hx)
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩; exact hx
  rw [hA_eq]
  exact result_finset_biUnion union_step m (fun i => A ∩ D i)
    (fun i => hA_closed.inter (hD_closed i))
    (fun S hS => by
      have : (⋂ i ∈ S, (A ∩ D i)) = A ∩ ⋂ i ∈ S, D i := by
        ext x; simp only [mem_iInter, mem_inter_iff]
        constructor
        · intro h; exact ⟨(h _ hS.choose_spec).1, fun i hi => (h i hi).2⟩
        · rintro ⟨ha, hD⟩ i hi; exact ⟨ha, hD i hi⟩
      rw [this]; exact hD_result S hS)
    Finset.univ ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩ (Finset.card_fin m).le

end OrientationTheorem

namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- Abstract data witnessing that `G (⋂ j, A j)` is the colimit of the
sequence `G (A i)` along the inclusions `A (i+1) ⊆ A i`: restriction
maps `ρ i` to the intersection, transition maps `φ i j` compatible with
them, and the two filtered-colimit conditions (every element of the
limit comes from some `G (A i)`, and an element vanishing in the limit
already vanishes at some larger stage). -/
structure RelativeHomologyColimitData {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (G : Set X → Type*)
    [∀ K, AddCommGroup (G K)] where
  ρ : ∀ i, G (A i) →+ G (⋂ j, A j)
  φ : ∀ (i j : ℕ), i ≤ j → G (A i) →+ G (A j)
  compat : ∀ i j (hij : i ≤ j), (ρ j).comp (φ i j hij) = ρ i
  surj : ∀ (x : G (⋂ j, A j)), ∃ i, ∃ g : G (A i), ρ i g = x
  inj : ∀ i (g : G (A i)), ρ i g = 0 → ∃ j, ∃ hij : i ≤ j, φ i j hij g = 0

/-- If every group `G (A i)` vanishes, the colimit `G (⋂ j, A j)` also
vanishes. Used to propagate the vanishing part of the orientation
theorem from a decreasing sequence of compact sets to their
intersection. -/
theorem RelativeHomologyColimitData.vanishing_propagation
    {X : Type*} [TopologicalSpace X]
    {A : ℕ → Set X} {G : Set X → Type*} [∀ K, AddCommGroup (G K)]
    (col : RelativeHomologyColimitData A G)
    (hvan : ∀ i, ∀ x : G (A i), x = 0) :
    ∀ x : G (⋂ j, A j), x = 0 := by
  intro x
  obtain ⟨i, g, hg⟩ := col.surj x
  rw [hvan i g, map_zero] at hg
  exact hg.symm

/-- If a natural transformation `f : G ⟶ H` of colimit data induces a
bijection at each stage `A i`, then the induced map on colimits
`f (⋂ j, A j)` is also bijective. This is the standard fact that
filtered colimits of bijections are bijections, packaged in the form
needed to upgrade the orientation-theorem isomorphism from each `A i` to
their intersection. -/
theorem RelativeHomologyColimitData.bijective_propagation
    {X : Type*} [TopologicalSpace X]
    {A : ℕ → Set X}
    {G H : Set X → Type*} [∀ K, AddCommGroup (G K)] [∀ K, AddCommGroup (H K)]
    (colG : RelativeHomologyColimitData A G)
    (colH : RelativeHomologyColimitData A H)
    (f : ∀ K, G K →+ H K)
    (hf_ρ : ∀ i, (colH.ρ i).comp (f (A i)) = (f (⋂ j, A j)).comp (colG.ρ i))
    (hf_φ : ∀ i j (hij : i ≤ j),
      (colH.φ i j hij).comp (f (A i)) = (f (A j)).comp (colG.φ i j hij))
    (hf_bij : ∀ i, Bijective (f (A i))) :
    Bijective (f (⋂ j, A j)) := by
  constructor
  ·
    intro a b hab
    suffices key : ∀ x : G (⋂ j, A j), f (⋂ j, A j) x = 0 → x = 0 by
      have hd := key (a - b) (by rw [map_sub, hab, sub_self])
      rwa [sub_eq_zero] at hd
    intro x hx
    obtain ⟨i, gi, hgi⟩ := colG.surj x
    have hc := DFunLike.congr_fun (hf_ρ i) gi
    simp only [AddMonoidHom.comp_apply] at hc
    rw [hgi, hx] at hc
    obtain ⟨j, hij, hφ⟩ := colH.inj i _ hc
    have hj := DFunLike.congr_fun (hf_φ i j hij) gi
    simp only [AddMonoidHom.comp_apply] at hj
    rw [hφ] at hj
    have hφG0 : colG.φ i j hij gi = 0 :=
      (hf_bij j).injective (hj.symm.trans (map_zero _).symm)
    have hρ := DFunLike.congr_fun (colG.compat i j hij) gi
    simp only [AddMonoidHom.comp_apply] at hρ
    rw [hφG0, map_zero] at hρ
    rw [← hgi, hρ]
  ·
    intro s
    obtain ⟨i, si, hsi⟩ := colH.surj s
    obtain ⟨gi, hgi⟩ := (hf_bij i).surjective si
    refine ⟨colG.ρ i gi, ?_⟩
    have := DFunLike.congr_fun (hf_ρ i) gi
    simp only [AddMonoidHom.comp_apply] at this
    rw [← this, hgi, hsi]

/-- **Proposition 32.3, abstract form.** For a decreasing sequence
`A₀ ⊇ A₁ ⊇ ⋯` of compact subsets of a Hausdorff `n`-manifold-like
space, given colimit data witnessing that `Hrel q (⋂ i, A i)` and
`Γsec (⋂ i, A i)` are colimits of `Hrel q (A i)` and `Γsec (A i)`, the
orientation theorem on each `A i` implies the orientation theorem on
the intersection `⋂ i, A i`. -/
theorem orientation_theorem_iInter
    [T2Space M] (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {A : ℕ → Set M}
    (_hA_compact : ∀ i, IsCompact (A i))
    (_hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)

    (colH : ∀ q, RelativeHomologyColimitData A (Hrel q))
    (colΓ : RelativeHomologyColimitData A Γsec)

    (hjMap_ρ : ∀ i, (colΓ.ρ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp ((colH n).ρ i))
    (hjMap_φ : ∀ i j (hij : i ≤ j),
      (colΓ.φ i j hij).comp (jMap (A i)) = (jMap (A j)).comp ((colH n).φ i j hij))
    (hsat : ∀ i, OrientationTheoremResult n Hrel Γsec jMap (A i)) :
    OrientationTheoremResult n Hrel Γsec jMap (⋂ i, A i) where
  vanishing q hq x :=
    (colH q).vanishing_propagation (fun i g => (hsat i).vanishing q hq g) x
  isomorphism :=
    RelativeHomologyColimitData.bijective_propagation (colH n) colΓ
      (fun K => jMap K) hjMap_ρ hjMap_φ (fun i => (hsat i).isomorphism)

/-- Bundle of all colimit data needed for the `orientation_theorem_iInter`
proof at a single decreasing compact sequence: per-degree
`RelativeHomologyColimitData` for `Hrel q`, one for `Γsec`, and the
compatibility of `jMap` with the restriction and transition maps. -/
structure ColimitDataForDecreasingCompact {M : Type*} [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K) where
  colH : ∀ q, RelativeHomologyColimitData A (Hrel q)
  colΓ : RelativeHomologyColimitData A Γsec
  hjMap_ρ : ∀ i, (colΓ.ρ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp ((colH n).ρ i)
  hjMap_φ : ∀ i j (hij : i ≤ j),
    (colΓ.φ i j hij).comp (jMap (A i)) = (jMap (A j)).comp ((colH n).φ i j hij)

/-- Companion to `compact_decreasing_sequence_subset_open` rephrased in
complement form: if `K` is a compact subset of the complement of
`⋂ i, A i` where `A i` is a decreasing sequence of closed sets, then
`K ⊆ (A i)ᶜ` already for some `i`. Proved using the directed-cover
formulation of compactness. -/
lemma compact_subset_complement_eventually_aux
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (K : Set X) (hK : IsCompact K)
    (hKA : K ⊆ (⋂ i, A i)ᶜ) :
    ∃ i, K ⊆ (A i)ᶜ := by
  rw [compl_iInter] at hKA
  exact hK.elim_directed_cover _ (fun i => (hA_closed i).isOpen_compl) hKA
    (Monotone.directed_le (fun i j hij =>
      compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hij)))

/-- Manifold-flavoured constructor for
`ColimitDataForDecreasingCompact`: assembles the colimit data from the
manifold versions of the surjectivity and injectivity assertions, where
witnesses are presented as compact subsets of the complement of
`⋂ i, A i` and are converted to indices using
`compact_subset_complement_eventually_aux`. -/
def ColimitDataForDecreasingCompact.ofManifold
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [AlgebraicTopologyI.TopologicalManifold n M]
    (A : ℕ → Set M)
    (hA_compact : ∀ i, IsCompact (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)

    (ρH : ∀ q, ∀ i, Hrel q (A i) →+ Hrel q (⋂ j, A j))
    (φH : ∀ q, ∀ (i j : ℕ), i ≤ j → Hrel q (A i) →+ Hrel q (A j))
    (hcompatH : ∀ q i j (hij : i ≤ j), (ρH q j).comp (φH q i j hij) = ρH q i)

    (hsurjH : ∀ q (x : Hrel q (⋂ j, A j)),
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
        ∀ i, K ⊆ (A i)ᶜ → ∃ g : Hrel q (A i), ρH q i g = x)

    (hinjH : ∀ q (i : ℕ) (g : Hrel q (A i)), ρH q i g = 0 →
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ k, A k)ᶜ ∧
        ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φH q i j hij g = 0)

    (ρΓ : ∀ i, Γsec (A i) →+ Γsec (⋂ j, A j))
    (φΓ : ∀ (i j : ℕ), i ≤ j → Γsec (A i) →+ Γsec (A j))
    (hcompatΓ : ∀ i j (hij : i ≤ j), (ρΓ j).comp (φΓ i j hij) = ρΓ i)

    (hsurjΓ : ∀ (x : Γsec (⋂ j, A j)),
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
        ∀ i, K ⊆ (A i)ᶜ → ∃ g : Γsec (A i), ρΓ i g = x)

    (hinjΓ : ∀ (i : ℕ) (g : Γsec (A i)), ρΓ i g = 0 →
      ∃ (K : Set M), IsCompact K ∧ K ⊆ (⋂ k, A k)ᶜ ∧
        ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φΓ i j hij g = 0)

    (hjMap_ρ : ∀ i, (ρΓ i).comp (jMap (A i)) = (jMap (⋂ j, A j)).comp (ρH n i))

    (hjMap_φ : ∀ i j (hij : i ≤ j),
      (φΓ i j hij).comp (jMap (A i)) = (jMap (A j)).comp (φH n i j hij)) :
    ColimitDataForDecreasingCompact n A Hrel Γsec jMap where
  colH q := {
    ρ := ρH q
    φ := φH q
    compat := hcompatH q
    surj := by
      intro x
      obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := hsurjH q x
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨i, hKi⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      obtain ⟨g, hg⟩ := hK_lift i hKi
      exact ⟨i, g, hg⟩
    inj := by
      intro i g hg
      obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := hinjH q i g hg
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨j, hKj⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      have hij : i ≤ max i j := le_max_left i j
      have hjmax : j ≤ max i j := le_max_right i j
      have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
        (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))
      exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩
  }
  colΓ := {
    ρ := ρΓ
    φ := φΓ
    compat := hcompatΓ
    surj := by
      intro x
      obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := hsurjΓ x
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨i, hKi⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      obtain ⟨g, hg⟩ := hK_lift i hKi
      exact ⟨i, g, hg⟩
    inj := by
      intro i g hg
      obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := hinjΓ i g hg
      have hA_closed : ∀ i, IsClosed (A i) := fun i =>
        (hA_compact i).isClosed
      obtain ⟨j, hKj⟩ := compact_subset_complement_eventually_aux A hA_closed
        hA_decreasing K hK_compact hK_sub
      have hij : i ≤ max i j := le_max_left i j
      have hjmax : j ≤ max i j := le_max_right i j
      have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
        (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))
      exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩
  }
  hjMap_ρ := hjMap_ρ
  hjMap_φ := hjMap_φ


/-- **Proposition 32.3.** For a decreasing sequence of compact subsets
of a topological `n`-manifold, given the colimit data from
`ColimitDataForDecreasingCompact`, the orientation theorem propagates
from each `A i` to their intersection `⋂ i, A i`. -/
theorem orientation_theorem_iInter_manifold
    {M : Type*} [TopologicalSpace M]
    (n : ℕ) [AlgebraicTopologyI.TopologicalManifold n M]
    {A : ℕ → Set M}
    (hA_compact : ∀ i, IsCompact (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (Hrel : ℕ → Set M → Type*)
    [∀ q K, AddCommGroup (Hrel q K)]
    (Γsec : Set M → Type*)
    [∀ K, AddCommGroup (Γsec K)]
    (jMap : (K : Set M) → Hrel n K →+ Γsec K)
    (cd : ColimitDataForDecreasingCompact n A Hrel Γsec jMap)
    (hsat : ∀ i, OrientationTheoremResult n Hrel Γsec jMap (A i)) :
    OrientationTheoremResult n Hrel Γsec jMap (⋂ i, A i) :=
  orientation_theorem_iInter n hA_compact hA_decreasing Hrel Γsec jMap
    cd.colH cd.colΓ cd.hjMap_ρ cd.hjMap_φ hsat




end OrientationTheorem
