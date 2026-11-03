/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 800000

/-- A `ℤ_+`-ring (general version, not requiring `ι` to be finite): a set `ι` of
distinguished basis elements with nonnegative integer structure constants `N i j k`
satisfying unitality and associativity, and with finite multiplicative support. -/
structure ZPlusRingGen (ι : Type*) [DecidableEq ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  finite_support : ∀ i j, Set.Finite {k | N i j k ≠ 0}
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l,
    Set.Finite {m | N i j m * N m k l ≠ 0} ∧
    Set.Finite {m | N j k m * N i m l ≠ 0} ∧
    ∑ᶠ m, N i j m * N m k l = ∑ᶠ m, N j k m * N i m l

/-- Alias for Definition 1.42.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-ring is the
general (possibly infinite-index) version `ZPlusRingGen`. -/
abbrev Definition_1_42_1 := ZPlusRingGen

/-- A `ℤ_+`-ring with finite index set `ι`: nonnegative integer structure constants
`N i j k`, a unit subset `I₀`, and the unitality and associativity axioms expressed
with ordinary finite sums. -/
structure ZPlusRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

/-- When the index set `ι` is finite, a general `ZPlusRingGen` collapses to a
`ZPlusRing`: the `finsum` associativity becomes an ordinary `Finset.sum`. -/
def ZPlusRingGen.toZPlusRing {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : ZPlusRingGen ι) : ZPlusRing ι where
  N := R.N
  I₀ := R.I₀
  unit_mul := R.unit_mul
  mul_unit := R.mul_unit
  assoc := fun i j k l => by
    have ⟨_, _, h⟩ := R.assoc i j k l
    rwa [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h

/-- A `ZPlusRing` over a finite index set `ι` can always be regarded as a `ZPlusRingGen`,
since finiteness automatically supplies the finite-support and `finsum` data. -/
def ZPlusRing.toZPlusRingGen {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : ZPlusRing ι) : ZPlusRingGen ι where
  N := R.N
  I₀ := R.I₀
  finite_support := fun _ _ => Set.Finite.subset (Set.toFinite _) (Set.subset_univ _)
  unit_mul := R.unit_mul
  mul_unit := R.mul_unit
  assoc := fun i j k l =>
    ⟨Set.Finite.subset (Set.toFinite _) (Set.subset_univ _),
     Set.Finite.subset (Set.toFinite _) (Set.subset_univ _),
     by rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]; exact R.assoc i j k l⟩

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The squared coefficient at `k`: the total `∑_{i,j} N(i, j, k)` of structure
constants whose product lands at `k`. This bounds dimensions of irreducible modules. -/
def ZPlusRing.squaredCoeff (R : ZPlusRing ι) (k : ι) : ℕ :=
  ∑ i : ι, ∑ j : ι, R.N i j k

/-- The maximum of `R.squaredCoeff k` over all basis elements `k`, which bounds
the size of any irreducible `ℤ_+`-module over `R`. -/
noncomputable def ZPlusRing.maxSquaredCoeff (R : ZPlusRing ι) [Nonempty ι] : ℕ :=
  Finset.sup' Finset.univ Finset.univ_nonempty R.squaredCoeff

/-- Each squared coefficient is bounded by the maximum squared coefficient over `ι`. -/
theorem ZPlusRing.squaredCoeff_le_maxSquaredCoeff (R : ZPlusRing ι) [Nonempty ι] (k : ι) :
    R.squaredCoeff k ≤ R.maxSquaredCoeff :=
  Finset.le_sup' R.squaredCoeff (Finset.mem_univ k)

/-- A `ℤ_+`-module over a `ℤ_+`-ring `R`: a finite basis set `κ` together with
nonnegative integer action constants `act i l k`, satisfying unitality from `R.I₀`
and a compatibility expressing associativity of the action. -/
structure ZPlusModule (R : ZPlusRing ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

/-- Alias for Definition 2.8.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-module
over a `ℤ_+`-ring is what `ZPlusModule` formalizes. -/
abbrev Definition_2_8_1 := @ZPlusModule

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]

namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- The diagonal unitality identity for a `ℤ_+`-module: summing the action of the
unit elements `s ∈ R.I₀` on `l` against itself gives `1`. -/
theorem act_unit_self (l : κ) :
    ∑ s ∈ R.I₀, M.act s l l = 1 := by
  have h := M.act_unit l l; rw [if_pos rfl] at h; exact h

/-- A nonempty proper subset `S ⊆ κ` is a `ℤ_+`-submodule of `M` if it is closed
under the action: `M.act i l k ≠ 0` and `l ∈ S` implies `k ∈ S`. -/
structure IsZPlusSubmodule (S : Finset κ) : Prop where
  nonempty : S.Nonempty
  proper : S ≠ Finset.univ
  closed : ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- A `ℤ_+`-module is irreducible if it has no proper nonempty `ℤ_+`-submodule. -/
def IsIrreducible : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule S

/-- Alias for Definition 2.8.3: irreducibility of a `ℤ_+`-module. -/
abbrev def_2_8_3 : Prop := M.IsIrreducible

/-- The sum `∑_{k} act(i, l, k)` of action coefficients of `i ∈ ι` acting on `l ∈ κ`. -/
def actCoeffSum (i : ι) (l : κ) : ℕ := ∑ k : κ, M.act i l k

/-- The total action coefficient at `l ∈ κ`: the sum over all `i ∈ ι` of `actCoeffSum i l`. -/
def totalActCoeff (l : κ) : ℕ := ∑ i : ι, M.actCoeffSum i l

/-- Summing `actCoeffSum s l` over `s ∈ R.I₀` gives `1`, a consequence of unitality
of the `ℤ_+`-module action. -/
theorem actCoeffSum_unit (l : κ) :
    ∑ s ∈ R.I₀, M.actCoeffSum s l = 1 := by
  simp only [actCoeffSum]
  rw [Finset.sum_comm]
  simp_rw [M.act_unit]
  simp

/-- If `l₀ ∈ κ` minimizes `totalActCoeff`, then `M.totalActCoeff l₀` is bounded by
`R.maxSquaredCoeff`. This is the key inequality underlying Proposition 2.8.7. -/
theorem totalActCoeff_le_of_min [Nonempty ι] (l₀ : κ)
    (hmin : ∀ n : κ, M.totalActCoeff l₀ ≤ M.totalActCoeff n) :
    M.totalActCoeff l₀ ≤ R.maxSquaredCoeff := by
  by_cases hd : M.totalActCoeff l₀ = 0
  · omega
  have hpos : 0 < M.totalActCoeff l₀ := Nat.pos_of_ne_zero hd
  suffices h : M.totalActCoeff l₀ * M.totalActCoeff l₀ ≤
      R.maxSquaredCoeff * M.totalActCoeff l₀ from
    Nat.le_of_mul_le_mul_right h hpos


  have step1 : M.totalActCoeff l₀ * M.totalActCoeff l₀ ≤
      ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n := by
    rw [show M.totalActCoeff l₀ = ∑ j : ι, ∑ n : κ, M.act j l₀ n from by
      simp only [totalActCoeff, actCoeffSum]]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro n _
    exact Nat.mul_le_mul_left _ (hmin n)


  have step2 : ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n ≤
      R.maxSquaredCoeff * M.totalActCoeff l₀ := by
    calc ∑ j : ι, ∑ n : κ, M.act j l₀ n * M.totalActCoeff n
        = ∑ j : ι, ∑ n : κ, M.act j l₀ n * (∑ i : ι, M.actCoeffSum i n) := by rfl
      _ = ∑ j : ι, ∑ n : κ, ∑ i : ι, M.act j l₀ n * M.actCoeffSum i n := by
          congr 1; ext j; congr 1; ext n; rw [Finset.mul_sum]
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, M.act j l₀ n * M.actCoeffSum i n := by
          congr 1; ext j; rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, M.act j l₀ n * ∑ k : κ, M.act i n k := by rfl
      _ = ∑ j : ι, ∑ i : ι, ∑ n : κ, ∑ k : κ, M.act j l₀ n * M.act i n k := by
          congr 1; ext j; congr 1; ext i; congr 1; ext n; rw [Finset.mul_sum]
      _ = ∑ j : ι, ∑ i : ι, ∑ k : κ, ∑ n : κ, M.act j l₀ n * M.act i n k := by
          congr 1; ext j; congr 1; ext i; rw [Finset.sum_comm]
      _ = ∑ j : ι, ∑ i : ι, ∑ k : κ, ∑ m : ι, R.N i j m * M.act m l₀ k := by
          congr 1; ext j; congr 1; ext i; congr 1; ext k
          exact (M.act_compat i j l₀ k).symm
      _ = ∑ i : ι, ∑ j : ι, ∑ k : κ, ∑ m : ι, R.N i j m * M.act m l₀ k := by
          rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ j : ι, ∑ m : ι, ∑ k : κ, R.N i j m * M.act m l₀ k := by
          congr 1; ext i; congr 1; ext j; rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ j : ι, ∑ m : ι, R.N i j m * M.actCoeffSum m l₀ := by
          congr 1; ext i; congr 1; ext j; congr 1; ext m
          simp only [actCoeffSum, Finset.mul_sum]

      _ = ∑ m : ι, R.squaredCoeff m * M.actCoeffSum m l₀ := by
          conv_lhs =>
            arg 2; ext i
            rw [Finset.sum_comm (f := fun j m => R.N i j m * M.actCoeffSum m l₀)]
          rw [Finset.sum_comm
            (f := fun i m => ∑ j, R.N i j m * M.actCoeffSum m l₀)]
          congr 1; ext m
          simp_rw [← Finset.sum_mul]
          rfl

      _ ≤ ∑ m : ι, R.maxSquaredCoeff * M.actCoeffSum m l₀ := by
          apply Finset.sum_le_sum; intro m _
          exact Nat.mul_le_mul_right _ (R.squaredCoeff_le_maxSquaredCoeff m)
      _ = R.maxSquaredCoeff * M.totalActCoeff l₀ := by
          rw [← Finset.mul_sum]; rfl
  exact le_trans step1 step2

/-- In an irreducible `ℤ_+`-module, for every pair `l, k ∈ κ` there exists some
`i ∈ ι` whose action takes `l` to a positive coefficient at `k`. -/
theorem act_pos_of_irreducible (hirr : M.IsIrreducible) (l k : κ) :
    ∃ i : ι, 0 < M.act i l k := by
  classical
  let S := Finset.univ.filter (fun k' => ∃ i : ι, 0 < M.act i l k')

  have hl_in_S : l ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ l, ?_⟩
    have h1 := M.act_unit_self l
    by_contra hc
    simp only [not_exists, Nat.not_lt, Nat.le_zero] at hc
    have : ∑ s ∈ R.I₀, M.act s l l = 0 :=
      Finset.sum_eq_zero (fun s _ => hc s)
    omega

  have hS_closed : ∀ (j : ι) (k' : κ), k' ∈ S → ∀ (k'' : κ),
      M.act j k' k'' ≠ 0 → k'' ∈ S := by
    intro j k' hk' k'' hact
    have hk'_mem := (Finset.mem_filter.mp hk').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k'', ?_⟩
    obtain ⟨i₀, hi₀⟩ := hk'_mem


    have hcompat := M.act_compat j i₀ l k''
    have hact_pos : 0 < M.act j k' k'' := Nat.pos_of_ne_zero hact
    have hrhs_pos : 0 < ∑ n : κ, M.act i₀ l n * M.act j n k'' :=
      calc 0 < M.act i₀ l k' * M.act j k' k'' := Nat.mul_pos hi₀ hact_pos
        _ ≤ ∑ n : κ, M.act i₀ l n * M.act j n k'' :=
          Finset.single_le_sum (f := fun n => M.act i₀ l n * M.act j n k'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k')
    rw [← hcompat] at hrhs_pos

    by_contra hc2
    simp only [not_exists, Nat.not_lt, Nat.le_zero] at hc2
    have : ∑ m : ι, R.N j i₀ m * M.act m l k'' = 0 :=
      Finset.sum_eq_zero (fun m _ => by simp [hc2 m])
    omega

  by_cases hS_all : S = Finset.univ
  · have hk_in : k ∈ S := hS_all ▸ Finset.mem_univ k
    exact (Finset.mem_filter.mp hk_in).2

  · exfalso
    exact hirr S ⟨⟨l, hl_in_S⟩, hS_all, hS_closed⟩

/-- For an irreducible `ℤ_+`-module the cardinality of the basis `κ` is bounded
above by `totalActCoeff l` for every `l ∈ κ`. -/
theorem card_le_totalActCoeff_of_irreducible (hirr : M.IsIrreducible) (l : κ) :
    Fintype.card κ ≤ M.totalActCoeff l := by
  unfold totalActCoeff actCoeffSum
  rw [Finset.sum_comm]
  calc Fintype.card κ = Finset.univ.card := Finset.card_univ.symm
    _ = ∑ _k ∈ (Finset.univ : Finset κ), 1 := by simp
    _ ≤ ∑ k ∈ (Finset.univ : Finset κ), ∑ i : ι, M.act i l k := by
        apply Finset.sum_le_sum
        intro k _
        obtain ⟨i₀, hi₀⟩ := M.act_pos_of_irreducible hirr l k
        calc 1 ≤ M.act i₀ l k := hi₀
          _ ≤ ∑ i : ι, M.act i l k :=
            Finset.single_le_sum (f := fun i => M.act i l k)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
    _ = ∑ k : κ, ∑ i : ι, M.act i l k := by rfl

/-- Proposition 2.8.7 (Etingof–Gelaki–Nikshych–Ostrik): if `M` is an irreducible
`ℤ_+`-module over a `ℤ_+`-ring `R`, then `|κ| ≤ R.maxSquaredCoeff`. -/
theorem prop_2_8_7 (hirr : M.IsIrreducible) [Nonempty ι] [hκ : Nonempty κ] :
    Fintype.card κ ≤ R.maxSquaredCoeff := by
  obtain ⟨l₀, _, hl₀⟩ := Finset.exists_min_image Finset.univ M.totalActCoeff
    ⟨Classical.arbitrary κ, Finset.mem_univ _⟩
  calc Fintype.card κ
      ≤ M.totalActCoeff l₀ := M.card_le_totalActCoeff_of_irreducible hirr l₀
    _ ≤ R.maxSquaredCoeff :=
        M.totalActCoeff_le_of_min l₀ (fun n => hl₀ n (Finset.mem_univ n))

/-- The regular `ℤ_+`-module of a `ℤ_+`-ring `R`: `R` acting on its own basis `ι`
via the structure constants `N`. -/
def regularModule (R : ZPlusRing ι) : ZPlusModule R ι where
  act := R.N
  act_unit := R.unit_mul
  act_compat := R.assoc

/-- A morphism of `ℤ_+`-modules over the same `ℤ_+`-ring `R`: a nonnegative integer
matrix `toMatrix : κ₁ → κ₂ → ℕ` that intertwines the two actions of `R`. -/
structure ZPlusModuleHom {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  toMatrix : κ₁ → κ₂ → ℕ
  equivariant : ∀ (i : ι) (l : κ₁) (k₂ : κ₂),
    ∑ k₁ : κ₁, M₁.act i l k₁ * toMatrix k₁ k₂ =
    ∑ n : κ₂, toMatrix l n * M₂.act i n k₂

/-- An isomorphism between two `ℤ_+`-modules: a bijection of basis sets `κ₁ ≃ κ₂`
that intertwines the two actions of `R`. -/
structure IsIsomorphism {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  equiv : κ₁ ≃ κ₂
  compat : ∀ (i : ι) (l k : κ₁), M₁.act i l k = M₂.act i (equiv l) (equiv k)

/-- A `ℤ_+`-module is indecomposable if its basis `κ` cannot be split into two
nonempty disjoint action-closed subsets covering `κ`. -/
def IsIndecomposable : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- Every irreducible `ℤ_+`-module is indecomposable: a proper action-closed
nonempty subset would contradict irreducibility. -/
theorem IsIrreducible.isIndecomposable (hirr : M.IsIrreducible) : M.IsIndecomposable := by
  intro S₁ S₂ hne₁ hne₂ hdisj _ hcl₁ _
  have hS₁_proper : S₁ ≠ Finset.univ := by
    intro heq
    have : S₂ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact Finset.disjoint_right.mp hdisj hx (heq ▸ Finset.mem_univ x)
    exact hne₂.ne_empty this
  exact hirr S₁ ⟨hne₁, hS₁_proper, hcl₁⟩

/-- Exactness of a `ℤ_+`-module: whenever `act i l k ≠ 0` there exists some `j ∈ ι`
with `act j k l ≠ 0`, i.e. the action is symmetric up to relabeling. -/
def IsExact : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

/-- Lemma 2.8.5 of Etingof–Gelaki–Nikshych–Ostrik: an indecomposable, exact
`ℤ_+`-module is irreducible. -/
theorem lemma_2_8_5 (hindec : M.IsIndecomposable) (hexact : M.IsExact) :
    M.IsIrreducible := by
  intro S hS
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hS.proper
    have : S = Finset.univ \ (Finset.univ \ S) := by simp
    rw [this, h]; simp
  have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
  have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ S)
  have hSc_closed : ∀ (i : ι) (l : κ), l ∈ Finset.univ \ S → ∀ (k : κ),
      M.act i l k ≠ 0 → k ∈ Finset.univ \ S := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨Finset.mem_univ k, fun hk_in_S => by
      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hS.closed j k hk_in_S l hj)⟩
  exact hindec S (Finset.univ \ S) hS.nonempty hSc_ne hdisj hunion hS.closed hSc_closed

/-- A subset `S ⊆ κ` is action-closed under `M` if whenever `l ∈ S` and
`M.act i l k ≠ 0` we have `k ∈ S`. -/
def IsActionClosed (S : Finset κ) : Prop :=
  ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- An action-closed subset `S ⊆ κ` is an indecomposable piece if it cannot be
partitioned into two nonempty disjoint action-closed subsets. -/
def IsIndecomposablePiece (S : Finset κ) : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = S →
    M.IsActionClosed S₁ → M.IsActionClosed S₂ → False

/-- An action-closed subset `S ⊆ κ` is an irreducible piece if it contains no
proper nonempty action-closed subset. -/
def IsIrreduciblePiece (S : Finset κ) : Prop :=
  ∀ T : Finset κ, T.Nonempty → T ≠ S → T ⊆ S → ¬M.IsActionClosed T

/-- A `ℤ_+`-decomposition of `M`: a finite family of nonempty pairwise disjoint
action-closed subsets of `κ` whose union covers `κ`. -/
structure IsZPlusDecomposition (parts : Finset (Finset κ)) : Prop where
  covers : ∀ k : κ, ∃ P ∈ parts, k ∈ P
  pairwise_disjoint : ∀ P₁ ∈ parts, ∀ P₂ ∈ parts, P₁ ≠ P₂ → Disjoint P₁ P₂
  nonempty : ∀ P ∈ parts, P.Nonempty
  closed : ∀ P ∈ parts, M.IsActionClosed P

/-- Auxiliary recursion lemma: every nonempty action-closed subset `S ⊆ κ` admits
a partition into nonempty pairwise disjoint action-closed indecomposable pieces. -/
theorem decompose_finset_aux :
    ∀ S : Finset κ, S.Nonempty → M.IsActionClosed S →
    ∃ parts : Finset (Finset κ),
      (∀ k : κ, k ∈ S ↔ ∃ P ∈ parts, k ∈ P) ∧
      (∀ P₁ ∈ parts, ∀ P₂ ∈ parts, P₁ ≠ P₂ → Disjoint P₁ P₂) ∧
      (∀ P ∈ parts, P.Nonempty) ∧
      (∀ P ∈ parts, M.IsActionClosed P) ∧
      (∀ P ∈ parts, M.IsIndecomposablePiece P) := by
  classical
  apply Finset.strongInduction
  intro S ih hne hclosed
  by_cases hindec : M.IsIndecomposablePiece S
  · exact ⟨{S},
      fun k => ⟨fun hk => ⟨S, Finset.mem_singleton_self S, hk⟩,
               fun ⟨P, hP, hk⟩ => Finset.mem_singleton.mp hP ▸ hk⟩,
      fun P₁ hP₁ P₂ hP₂ hne => by
        simp only [Finset.mem_singleton] at hP₁ hP₂
        exact absurd (hP₁.trans hP₂.symm) hne,
      fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hne,
      fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hclosed,
      fun P hP => by rw [Finset.mem_singleton.mp hP]; exact hindec⟩
  · unfold IsIndecomposablePiece at hindec
    push_neg at hindec
    obtain ⟨S₁, S₂, hne₁, hne₂, hdisj_S, hunion, hcl₁, hcl₂, _⟩ := hindec
    have hss₁ : S₁ ⊂ S := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨fun x hx => hunion ▸ Finset.mem_union_left S₂ hx,
        fun heq => by
          obtain ⟨y, hy⟩ := hne₂
          exact Finset.disjoint_left.mp hdisj_S
            (heq ▸ hunion ▸ Finset.mem_union_right S₁ hy) hy⟩
    have hss₂ : S₂ ⊂ S := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨fun x hx => hunion ▸ Finset.mem_union_right S₁ hx,
        fun heq => by
          obtain ⟨y, hy⟩ := hne₁
          exact Finset.disjoint_right.mp hdisj_S
            (heq ▸ hunion ▸ Finset.mem_union_left S₂ hy) hy⟩
    obtain ⟨parts₁, hcov₁, hdisj₁, hne₁', hcl₁', hindec₁⟩ := ih S₁ hss₁ hne₁ hcl₁
    obtain ⟨parts₂, hcov₂, hdisj₂, hne₂', hcl₂', hindec₂⟩ := ih S₂ hss₂ hne₂ hcl₂
    have hp₁_sub : ∀ P ∈ parts₁, P ⊆ S₁ :=
      fun P hP k hk => (hcov₁ k).mpr ⟨P, hP, hk⟩
    have hp₂_sub : ∀ P ∈ parts₂, P ⊆ S₂ :=
      fun P hP k hk => (hcov₂ k).mpr ⟨P, hP, hk⟩
    refine ⟨parts₁ ∪ parts₂, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro k; constructor
      · intro hk
        rw [← hunion, Finset.mem_union] at hk
        cases hk with
        | inl hk₁ =>
          have ⟨P, hP, hkP⟩ := (hcov₁ k).mp hk₁
          exact ⟨P, Finset.mem_union_left _ hP, hkP⟩
        | inr hk₂ =>
          have ⟨P, hP, hkP⟩ := (hcov₂ k).mp hk₂
          exact ⟨P, Finset.mem_union_right _ hP, hkP⟩
      · intro ⟨P, hP, hkP⟩
        rw [Finset.mem_union] at hP; rw [← hunion]
        cases hP with
        | inl hP₁ => exact Finset.mem_union_left _ ((hcov₁ k).mpr ⟨P, hP₁, hkP⟩)
        | inr hP₂ => exact Finset.mem_union_right _ ((hcov₂ k).mpr ⟨P, hP₂, hkP⟩)
    ·
      intro P₁ hP₁ P₂ hP₂ hne_P
      rw [Finset.mem_union] at hP₁ hP₂
      match hP₁, hP₂ with
      | .inl h₁, .inl h₂ => exact hdisj₁ P₁ h₁ P₂ h₂ hne_P
      | .inr h₁, .inr h₂ => exact hdisj₂ P₁ h₁ P₂ h₂ hne_P
      | .inl h₁, .inr h₂ =>
        exact Finset.disjoint_of_subset_left (hp₁_sub P₁ h₁)
          (Finset.disjoint_of_subset_right (hp₂_sub P₂ h₂) hdisj_S)
      | .inr h₁, .inl h₂ =>
        exact Finset.disjoint_of_subset_left (hp₂_sub P₁ h₁)
          (Finset.disjoint_of_subset_right (hp₁_sub P₂ h₂) hdisj_S.symm)
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hne₁' P h | inr h => exact hne₂' P h
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hcl₁' P h | inr h => exact hcl₂' P h
    ·
      intro P hP; rw [Finset.mem_union] at hP
      cases hP with | inl h => exact hindec₁ P h | inr h => exact hindec₂ P h

/-- Every `ℤ_+`-module (with nonempty basis) admits a `ℤ_+`-decomposition into
indecomposable pieces. -/
theorem exists_indecomposable_decomposition [Nonempty κ] :
    ∃ parts : Finset (Finset κ),
      M.IsZPlusDecomposition parts ∧
      ∀ P ∈ parts, M.IsIndecomposablePiece P := by
  have hne : (Finset.univ : Finset κ).Nonempty := Finset.univ_nonempty
  have hclosed : M.IsActionClosed Finset.univ :=
    fun _ _ _ _ _ => Finset.mem_univ _
  obtain ⟨parts, hcov, hdisj, hne', hcl', hindec⟩ :=
    M.decompose_finset_aux Finset.univ hne hclosed
  exact ⟨parts,
    ⟨fun k => (hcov k).mp (Finset.mem_univ k), hdisj, hne', hcl'⟩,
    hindec⟩

/-- For exact `ℤ_+`-modules, every indecomposable piece is automatically irreducible:
a proper action-closed subset would split off its complement using exactness. -/
theorem indecomposable_piece_irreducible_of_exact
    (hexact : M.IsExact) (S : Finset κ)
    (hclosed : M.IsActionClosed S) (hindec : M.IsIndecomposablePiece S) :
    M.IsIrreduciblePiece S := by
  intro T hTne hTne_S hTsub hTclosed
  have hunion : T ∪ (S \ T) = S := Finset.union_sdiff_of_subset hTsub
  have hSdiff_ne : (S \ T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hTne_S
    exact Finset.Subset.antisymm hTsub (by
      intro x hx; by_contra hxT
      exact Finset.notMem_empty x (h ▸ Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
  have hSdiff_closed : M.IsActionClosed (S \ T) := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨hclosed i l hl.1 k hact, fun hkT => by
      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hTclosed j k hkT l hj)⟩
  exact hindec T (S \ T) hTne hSdiff_ne Finset.disjoint_sdiff hunion hTclosed hSdiff_closed

end ZPlusModule

/-- Proposition 2.8.7 (Etingof–Gelaki–Nikshych–Ostrik): the cardinality of the basis
of any irreducible `ℤ_+`-module is bounded by the maximum squared coefficient of `R`. -/
theorem Proposition_2_8_7
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    {R : ZPlusRing ι}
    {κ : Type*} [DecidableEq κ] [Fintype κ] [Nonempty κ]
    (M : ZPlusModule R κ)
    (hirr : M.IsIrreducible) :
    Fintype.card κ ≤ R.maxSquaredCoeff :=
  M.prop_2_8_7 hirr
