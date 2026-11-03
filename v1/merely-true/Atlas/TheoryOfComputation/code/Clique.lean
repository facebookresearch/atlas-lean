/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Atlas.TheoryOfComputation.code.Complexity
import Atlas.TheoryOfComputation.code.NPCompleteness

namespace Clique

open SimpleGraph

/-- A graph `G` has a `k`-clique iff there exists a `k`-vertex subset all of
whose pairs are adjacent in `G`. -/
def HasKClique {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (s : Finset V), G.IsNClique k s

/-- The language `CLIQUE = {⟨G, k⟩ | G has a k-clique}` as a set of
graph/integer pairs. -/
def CLIQUE (V : Type*) : Set (SimpleGraph V × ℕ) :=
  {p | HasKClique p.1 p.2}

end Clique

namespace ThreeSATToClique

/-- The polarity of a propositional literal: positive (`x`) or negative (`¬x`). -/
inductive Polarity where
  | pos : Polarity
  | neg : Polarity
  deriving DecidableEq, Repr

/-- A propositional literal: a variable index together with a polarity, so
that `⟨i, .pos⟩` represents `x_i` and `⟨i, .neg⟩` represents `¬x_i`. -/
structure Literal where
  varIdx : ℕ
  pol : Polarity
  deriving DecidableEq, Repr

/-- Two literals are contradictory when they refer to the same variable but
have opposite polarities (e.g. `x_i` and `¬x_i`). -/
def Literal.IsContradictory (l₁ l₂ : Literal) : Prop :=
  l₁.varIdx = l₂.varIdx ∧ l₁.pol ≠ l₂.pol

/-- Contradictoriness of literals is decidable, inherited from decidability of
equality on variable indices and polarities. -/
instance (l₁ l₂ : Literal) : Decidable (l₁.IsContradictory l₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The "contradictory" relation between literals is symmetric. -/
theorem Literal.IsContradictory.symm' {l₁ l₂ : Literal}
    (h : l₁.IsContradictory l₂) : l₂.IsContradictory l₁ :=
  ⟨h.1.symm, fun h' => h.2 h'.symm⟩

/-- Evaluate a literal under a truth assignment `σ : ℕ → Bool`: a positive
literal returns `σ l.varIdx`, a negative literal returns its negation. -/
def Literal.eval (σ : ℕ → Bool) (l : Literal) : Bool :=
  match l.pol with
  | .pos => σ l.varIdx
  | .neg => !σ l.varIdx

/-- A 3-clause is a triple of literals, representing the disjunction
`l₁ ∨ l₂ ∨ l₃` in a 3CNF formula. -/
abbrev ThreeClause := Literal × Literal × Literal

/-- Project the `j`-th literal (for `j : Fin 3`) out of a 3-clause. -/
def ThreeClause.literalAt (c : ThreeClause) (j : Fin 3) : Literal :=
  match j with
  | ⟨0, _⟩ => c.1
  | ⟨1, _⟩ => c.2.1
  | ⟨2, _⟩ => c.2.2

/-- A 3-clause is satisfied by an assignment `σ` iff at least one of its three
literals evaluates to `true` under `σ`. -/
def ThreeClause.isSatBy (σ : ℕ → Bool) (c : ThreeClause) : Prop :=
  ∃ j : Fin 3, (c.literalAt j).eval σ = true

/-- A 3CNF formula, represented as a list of 3-clauses (interpreted as their
conjunction). -/
abbrev ThreeCNF := List ThreeClause

/-- A 3CNF formula `φ` is satisfiable iff there is an assignment `σ` under
which every clause of `φ` is satisfied. -/
def ThreeCNF.IsSatisfiable (φ : ThreeCNF) : Prop :=
  ∃ σ : ℕ → Bool, ∀ (i : Fin φ.length), (φ.get i).isSatBy σ

/-- The graph produced by the standard `3SAT ≤_P CLIQUE` reduction. Vertices
are pairs `(i, j)` with `i` a clause index and `j ∈ Fin 3` a literal position;
two distinct vertices are adjacent iff they come from different clauses and
their literals are not contradictory. A clique of size `|φ|` then encodes a
satisfying assignment by picking, in each clause, a literal that is true. -/
def reductionGraph (φ : ThreeCNF) :
    SimpleGraph (Fin φ.length × Fin 3) where
  Adj v₁ v₂ :=
    v₁ ≠ v₂ ∧
    v₁.1 ≠ v₂.1 ∧
    ¬((φ.get v₁.1).literalAt v₁.2).IsContradictory
      ((φ.get v₂.1).literalAt v₂.2)
  symm v₁ v₂ := by
    rintro ⟨hne, hcl, hnc⟩
    exact ⟨hne.symm, hcl.symm, fun h => hnc h.symm'⟩
  loopless := ⟨fun v ⟨hne, _, _⟩ => hne rfl⟩

/-- Two contradictory literals cannot both evaluate to `true` under any
single assignment. -/
theorem contradictory_not_both_true {l₁ l₂ : Literal} {σ : ℕ → Bool}
    (hc : l₁.IsContradictory l₂)
    (h₁ : l₁.eval σ = true) (h₂ : l₂.eval σ = true) : False := by
  obtain ⟨hvar, hpol⟩ := hc
  cases hl₁ : l₁.pol <;> cases hl₂ : l₂.pol <;> simp_all [Literal.eval]

/-- Given a satisfying assignment `σ` for a clause `c`, choose (using
classical choice) one position `j : Fin 3` whose literal evaluates to `true`. -/
noncomputable def ThreeClause.trueLitPos (σ : ℕ → Bool) (c : ThreeClause)
    (hsat : c.isSatBy σ) : Fin 3 :=
  hsat.choose

/-- Specification of `trueLitPos`: the literal at the chosen position indeed
evaluates to `true` under `σ`. -/
theorem ThreeClause.trueLitPos_spec (σ : ℕ → Bool) (c : ThreeClause)
    (hsat : c.isSatBy σ) :
    (c.literalAt (c.trueLitPos σ hsat)).eval σ = true :=
  hsat.choose_spec

/-- Given a satisfying assignment `σ` for every clause of `φ`, build the
candidate clique in `reductionGraph φ` by selecting, for each clause `i`, the
vertex `(i, j)` where `j` is a position witnessing the clause's satisfaction. -/
noncomputable def satisfyingClique (φ : ThreeCNF) (σ : ℕ → Bool)
    (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
    Finset (Fin φ.length × Fin 3) :=
  Finset.univ.image (fun i => (i, (φ.get i).trueLitPos σ (hsat i)))

/-- The candidate clique `satisfyingClique φ σ hsat` has exactly `|φ|`
vertices (one per clause), since the map `i ↦ (i, _)` is injective in `i`. -/
theorem satisfyingClique_card (φ : ThreeCNF) (σ : ℕ → Bool)
    (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
    (satisfyingClique φ σ hsat).card = φ.length := by
  simp only [satisfyingClique]
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, Fintype.card_fin]
  · intro i₁ i₂ h
    exact (Prod.ext_iff.mp h).1

/-- The candidate set `satisfyingClique φ σ hsat` is indeed a clique in
`reductionGraph φ`: any two of its vertices come from different clauses, and
their selected literals are both true under `σ`, hence not contradictory. -/
theorem satisfyingClique_isClique (φ : ThreeCNF) (σ : ℕ → Bool)
    (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
    (reductionGraph φ).IsClique (satisfyingClique φ σ hsat : Set _) := by
  rw [SimpleGraph.isClique_iff]
  intro v₁ hv₁ v₂ hv₂ hne
  simp only [satisfyingClique, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hv₁ hv₂
  obtain ⟨i₁, rfl⟩ := hv₁
  obtain ⟨i₂, rfl⟩ := hv₂
  refine ⟨hne, ?_, ?_⟩
  · intro heq
    exact hne (by rw [show i₁ = i₂ from heq])
  · intro hc
    exact contradictory_not_both_true hc
      (ThreeClause.trueLitPos_spec σ (φ.get i₁) (hsat i₁))
      (ThreeClause.trueLitPos_spec σ (φ.get i₂) (hsat i₂))

/-- Forward direction of the `3SAT ≤_P CLIQUE` reduction: if `φ` is
satisfiable, then `reductionGraph φ` contains a `|φ|`-clique. -/
theorem satisfiable_imp_clique (φ : ThreeCNF) (hsat : φ.IsSatisfiable) :
    ∃ s : Finset (Fin φ.length × Fin 3),
      (reductionGraph φ).IsNClique φ.length s := by
  obtain ⟨σ, hσ⟩ := hsat
  exact ⟨satisfyingClique φ σ hσ,
    ⟨satisfyingClique_isClique φ σ hσ,
     satisfyingClique_card φ σ hσ⟩⟩

/-- Backward direction of the `3SAT ≤_P CLIQUE` reduction: a `|φ|`-clique in
`reductionGraph φ` must hit every clause exactly once (since edges only join
different clauses) and pick a pairwise non-contradictory set of literals;
setting variables to make all chosen positive literals true yields a
satisfying assignment for `φ`. -/
theorem clique_imp_satisfiable (φ : ThreeCNF)
    (s : Finset (Fin φ.length × Fin 3))
    (hclique : (reductionGraph φ).IsNClique φ.length s) :
    φ.IsSatisfiable := by
  classical
  obtain ⟨hcl, hcard⟩ := hclique

  have hcovers : s.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    have : (s.image Prod.fst).card = φ.length := by
      conv_rhs => rw [← hcard]
      apply Finset.card_image_of_injOn
      intro ⟨i₁, j₁⟩ hi₁ ⟨i₂, j₂⟩ hi₂ heq
      simp only at heq
      by_contra hne
      exact (hcl (Finset.mem_coe.mpr hi₁) (Finset.mem_coe.mpr hi₂) hne).2.1 heq
    rw [this, Fintype.card_fin]

  have hnode : ∀ i : Fin φ.length, ∃ j : Fin 3, (i, j) ∈ s := by
    intro i
    have : i ∈ s.image Prod.fst := hcovers ▸ Finset.mem_univ _
    obtain ⟨⟨i', j⟩, hmem, rfl⟩ := Finset.mem_image.mp this
    exact ⟨j, hmem⟩

  let σ : ℕ → Bool := fun v =>
    if ∃ node ∈ s, ((φ.get node.1).literalAt node.2).varIdx = v ∧
                    ((φ.get node.1).literalAt node.2).pol = Polarity.pos
    then true else false
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hnode i
  refine ⟨j, ?_⟩

  simp only [Literal.eval]
  cases hpol : ((φ.get i).literalAt j).pol
  ·
    simp only [σ]
    rw [if_pos]
    exact ⟨(i, j), hj, rfl, hpol⟩
  ·

    simp only [σ, Bool.not_eq_true']
    rw [if_neg]
    push Not
    intro ⟨i', j'⟩ hmem' hvar hpol'
    by_cases heq : (i, j) = (i', j')
    ·
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [hpol] at hpol'
      exact absurd hpol' (by decide)
    ·

      exfalso
      apply (hcl (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hmem') heq).2.2
      exact ⟨hvar.symm, by rw [hpol, hpol']; decide⟩

/-- **Correctness of the `3SAT ≤_P CLIQUE` reduction.** A 3CNF formula `φ` is
satisfiable iff its reduction graph `reductionGraph φ` contains a clique of
size `|φ|`. -/
theorem reduction_correct (φ : ThreeCNF) :
    φ.IsSatisfiable ↔
    ∃ s : Finset (Fin φ.length × Fin 3),
      (reductionGraph φ).IsNClique φ.length s := by
  constructor
  · exact satisfiable_imp_clique φ
  · rintro ⟨s, hs⟩
    exact clique_imp_satisfiable φ s hs

end ThreeSATToClique

namespace CliqueReduction

open TuringMachine NPCompleteness ThreeSATToClique ThreeSATComplete

/-- Tape alphabet used to encode either a 3SAT instance or a CLIQUE instance
on a single Turing-machine tape. The symbol `sat φ` represents an encoded
3CNF formula `φ`, and `clique φ` represents the encoded CLIQUE instance
`⟨reductionGraph φ, |φ|⟩`. -/
inductive SATCliqueSymbol where
  | sat (φ : ThreeCNF) : SATCliqueSymbol
  | clique (φ : ThreeCNF) : SATCliqueSymbol

/-- Encoded 3SAT language: those single-symbol tape strings `[.sat φ]` whose
underlying formula `φ` is satisfiable. -/
def ThreeSATEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ φ : ThreeCNF, w = [.sat φ] ∧ φ.IsSatisfiable}

/-- Encoded CLIQUE language (specialized to instances arising from the
reduction): the single-symbol strings `[.clique φ]` whose reduction graph
`reductionGraph φ` contains a `|φ|`-clique. -/
def CLIQUEEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ (φ : ThreeCNF),
    w = [.clique φ] ∧ Clique.HasKClique (reductionGraph φ) φ.length}

/-- The reduction function `f : Σ* → Σ*` on encodings: maps `[.sat φ]` to
`[.clique φ]` and every other input to the empty string. -/
def threeSATToCliqueEnc : List SATCliqueSymbol → List SATCliqueSymbol
  | [.sat φ] => [.clique φ]
  | _ => []

/-- On any input that is not of the form `[.sat φ]`, the reduction function
`threeSATToCliqueEnc` returns the empty list. -/
theorem threeSATToCliqueEnc_default {w : List SATCliqueSymbol}
    (hw : ¬∃ φ : ThreeCNF, w = [.sat φ]) :
    threeSATToCliqueEnc w = [] := by
  cases w with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil =>
      cases a with
      | sat φ => exact absurd ⟨φ, rfl⟩ hw
      | clique _ => rfl
    | cons b t' =>
      simp only [threeSATToCliqueEnc]

/-- The empty string is not in the encoded CLIQUE language, since every
member of `CLIQUEEnc` has the form `[.clique φ]`. -/
theorem nil_not_mem_CLIQUEEnc : ([] : List SATCliqueSymbol) ∉ CLIQUEEnc := by
  intro ⟨φ, heq, _⟩
  exact absurd heq (List.cons_ne_nil _ _).symm

/-- Per-formula correctness of the encoded reduction:
`[.sat φ] ∈ ThreeSATEnc ↔ threeSATToCliqueEnc [.sat φ] ∈ CLIQUEEnc`,
obtained directly from `reduction_correct`. -/
theorem reduction_enc_correct (φ : ThreeCNF) :
    [SATCliqueSymbol.sat φ] ∈ ThreeSATEnc ↔
    threeSATToCliqueEnc [.sat φ] ∈ CLIQUEEnc := by
  constructor
  ·
    rintro ⟨φ', hφ'eq, hsat⟩
    have hφeq : φ' = φ := (SATCliqueSymbol.sat.inj (List.cons.inj hφ'eq).1).symm
    subst hφeq
    exact ⟨_, rfl, (reduction_correct _).mp hsat⟩
  ·
    rintro ⟨φ', heq, hclique⟩
    have hφeq : φ' = φ := (SATCliqueSymbol.clique.inj (List.cons.inj heq).1).symm
    subst hφeq
    exact ⟨_, rfl, (reduction_correct _).mpr ⟨_, hclique.choose_spec⟩⟩

/-- Full correctness of the reduction function as a many-one reduction:
for every input string `w`, `w ∈ ThreeSATEnc ↔ threeSATToCliqueEnc w ∈ CLIQUEEnc`. -/
theorem threeSATToCliqueEnc_correct (w : List SATCliqueSymbol) :
    w ∈ ThreeSATEnc ↔ threeSATToCliqueEnc w ∈ CLIQUEEnc := by
  constructor
  · rintro ⟨φ, rfl, hsat⟩
    exact (reduction_enc_correct φ).mp ⟨φ, rfl, hsat⟩
  · intro hmem
    by_cases hw : ∃ φ : ThreeCNF, w = [.sat φ]
    · obtain ⟨φ, rfl⟩ := hw
      exact (reduction_enc_correct φ).mpr hmem
    · exfalso
      rw [threeSATToCliqueEnc_default hw] at hmem
      exact nil_not_mem_CLIQUEEnc hmem





end CliqueReduction
