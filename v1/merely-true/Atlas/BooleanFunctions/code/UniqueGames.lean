/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Atlas.BooleanFunctions.code.PCP
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
namespace UniqueGames

structure UniqueGame (V : Type*) (W : Type*) [DecidableEq V] [DecidableEq W] (k : ℕ) where
  edges : Finset (V × W)
  constraint : V → W → Equiv.Perm (Fin k)
  left_degree : ℕ
  right_degree : ℕ
  left_regular : ∀ v : V, (edges.filter (fun e => e.1 = v)).card = left_degree
  right_regular : ∀ w : W, (edges.filter (fun e => e.2 = w)).card = right_degree

structure Labeling (V : Type*) (W : Type*) (k : ℕ) where
  labelV : V → Fin k
  labelW : W → Fin k

def edgeSatisfied {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) (v : V) (w : W) : Prop :=
  game.constraint v w (labeling.labelV v) = labeling.labelW w

instance {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) (v : V) (w : W) :
    Decidable (edgeSatisfied game labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

def numSatisfiedEdges {V : Type*} {W : Type*} {k : ℕ} [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℕ :=
  (game.edges.filter (fun p => edgeSatisfied game labeling p.1 p.2)).card

def numEdges {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) : ℕ :=
  game.edges.card

noncomputable def fractionSatisfied {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℝ :=
  (numSatisfiedEdges game labeling : ℝ) / (numEdges game : ℝ)

noncomputable def value {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) : ℝ :=
  iSup (fun labeling : Labeling V W k => fractionSatisfied game labeling)

structure NonBipartiteUniqueGame (X : Type*) [DecidableEq X] (k : ℕ) where
  edges : Finset (X × X)
  constraint : X → X → Equiv.Perm (Fin k)
  degree : ℕ
  regular : ∀ x : X, (edges.filter (fun e => e.1 = x)).card = degree

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def NonBipartiteUniqueGame.edgesWithin (game : NonBipartiteUniqueGame X k)
    (X' : Finset X) : Finset (X × X) :=
  game.edges.filter (fun e => e.1 ∈ X' ∧ e.2 ∈ X')

def NonBipartiteUniqueGame.edgeSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Fin k) (e : X × X) : Prop :=
  game.constraint e.1 e.2 (A e.1) = A e.2

instance (game : NonBipartiteUniqueGame X k) (A : X → Fin k) (e : X × X) :
    Decidable (game.edgeSatisfiedBy A e) :=
  inferInstanceAs (Decidable (_ = _))

noncomputable def NonBipartiteUniqueGame.fractionSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X) (A : X → Fin k) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def NonBipartiteUniqueGame.edgeTSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Finset (Fin k)) (e : X × X) : Prop :=
  ∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b

instance (game : NonBipartiteUniqueGame X k) (A : X → Finset (Fin k)) (e : X × X) :
    Decidable (game.edgeTSatisfiedBy A e) :=
  inferInstanceAs (Decidable (∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b))

def IsTAssignment (A : X → Finset (Fin k)) (X' : Finset X) (t : ℕ) : Prop :=
  ∀ x ∈ X', (A x).card = t

noncomputable def NonBipartiteUniqueGame.fractionTSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X)
    (A : X → Finset (Fin k)) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeTSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def StrongUGC_YES (game : NonBipartiteUniqueGame X k) (ε : ℝ) : Prop :=
  ∃ X' : Finset X,
    (X'.card : ℝ) ≥ (1 - ε) * ((Finset.univ : Finset X).card : ℝ) ∧
    ∃ A : X → Fin k, ∀ e ∈ game.edgesWithin X', game.edgeSatisfiedBy A e

def StrongUGC_NO (game : NonBipartiteUniqueGame X k) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ X' : Finset X,
    (X'.card : ℝ) ≥ ε * ((Finset.univ : Finset X).card : ℝ) →
    ∀ A : X → Finset (Fin k), IsTAssignment A X' t →
      ∃ e ∈ game.edgesWithin X', ¬ game.edgeTSatisfiedBy A e

structure LabelCover (V : Type*) (W : Type*) (k l : ℕ) where
  edges : Finset (V × W)
  constraint : V → W → (Fin l → Fin k)

structure LabelCover.Labeling (V : Type*) (W : Type*) (k l : ℕ) where
  labelV : V → Fin k
  labelW : W → Fin l

def LabelCover.edgeSatisfied {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l)
    (v : V) (w : W) : Prop :=
  game.constraint v w (labeling.labelW w) = labeling.labelV v

instance {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l)
    (v : V) (w : W) :
    Decidable (game.edgeSatisfied labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

def LabelCover.numSatisfiedEdges {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℕ :=
  (game.edges.filter (fun p => game.edgeSatisfied labeling p.1 p.2)).card

noncomputable def LabelCover.fractionSatisfied {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℝ :=
  (game.numSatisfiedEdges labeling : ℝ) / (game.edges.card : ℝ)

noncomputable def LabelCover.value {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) : ℝ :=
  iSup (fun labeling : LabelCover.Labeling V W k l => game.fractionSatisfied labeling)

def LabelCover.IsUnique {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) : Prop :=
  k = l ∧ ∀ v w, (⟨v, w⟩ : V × W) ∈ game.edges →
    Function.Bijective (game.constraint v w)

lemma fractionSatisfied_le_one {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ 1 := by
  unfold fractionSatisfied numSatisfiedEdges numEdges
  by_cases h : (game.edges.card : ℝ) = 0
  · simp [h]
  · rw [div_le_one (by positivity : (0 : ℝ) < (game.edges.card : ℝ))]
    exact_mod_cast Finset.card_filter_le _ _

lemma bddAbove_fractionSatisfied {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) :
    BddAbove (Set.range (fun labeling : Labeling V W k => fractionSatisfied game labeling)) :=
  ⟨1, fun _ ⟨lab, hlab⟩ => hlab ▸ fractionSatisfied_le_one game lab⟩

lemma fractionSatisfied_le_value {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ value game :=
  le_ciSup (bddAbove_fractionSatisfied game) labeling

lemma fractionSatisfied_le_of_value_le {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W]
    {k : ℕ} (game : UniqueGame V W k) (δ : ℝ) (hval : value game ≤ δ)
    (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ δ :=
  le_trans (fractionSatisfied_le_value game labeling) hval

end UniqueGames

namespace MaxCut

open Finset

structure MaxCutInstance (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (V × V)
  symm : ∀ e ∈ edges, (e.2, e.1) ∈ edges

def numCutEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℕ :=
  (G.edges.filter (fun e => f e.1 ≠ f e.2)).card

noncomputable def cutFraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℝ :=
  (numCutEdges G f : ℝ) / (G.edges.card : ℝ)

noncomputable def value {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) : ℝ :=
  iSup (fun f : V → Bool => cutFraction G f)

noncomputable def goemansWilliamsonConstant : ℝ :=
  ⨅ θ ∈ Set.Ioo (0 : ℝ) Real.pi, (2 / Real.pi) * θ / (1 - Real.cos θ)

def IsPolyTimeMaxCutInstanceReduction {numVerts : ℕ → ℕ}
    (_ : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))) : Prop :=
  ∃ (steps : ℕ → ℕ), PCP.IsPolynomial steps ∧ ∀ (m : ℕ), numVerts m ≤ steps m

def IsNPHardGapMaxCut (c s : ℝ) : Prop :=
  ∀ (L : PCP.Language), PCP.InNP L →
    ∃ (numVerts : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))),
      PCP.IsPolynomial numVerts ∧
      IsPolyTimeMaxCutInstanceReduction reduce ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m → value (reduce m x) ≥ c) ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m → value (reduce m x) ≤ s)

end MaxCut

noncomputable def maxBalancedNoiseStab (ρ : ℝ) (δ : ℝ) (k : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (f : (Fin k → Bool) → ℝ),
    (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ) ∧
    ((1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x = 0) ∧
    s = (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x *
      ((1 / (2 : ℝ) ^ k) * ∑ y : Fin k → Bool,
        (∏ i : Fin k, if x i = y i then 1 else ρ) * f y)}

noncomputable def longCodeReduce (_ρ : ℝ) (k numV numW : ℕ) :
    UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
    MaxCut.MaxCutInstance (Fin (Fintype.card (Fin numV × (Fin k → Bool)))) := by
  classical
  intro game
  let VType := Fin numV × (Fin k → Bool)
  let eqv : VType ≃ Fin (Fintype.card VType) := Fintype.equivFin VType

  let fwd : Finset (Fin (Fintype.card VType) × Fin (Fintype.card VType)) :=
    game.edges.biUnion fun vw₁ =>
      game.edges.biUnion fun vw₂ =>
        if h : vw₁.2 = vw₂.2 then

          let σ : Equiv.Perm (Fin k) :=
            (game.constraint vw₂.1 vw₂.2).symm.trans (game.constraint vw₁.1 vw₁.2)
          (Finset.univ : Finset (Fin k → Bool)).image fun x =>
            (eqv (vw₁.1, x), eqv (vw₂.1, fun i => !(x (σ.symm i))))
        else ∅
  let bwd := fwd.image (fun p => (p.2, p.1))
  exact ⟨fwd ∪ bwd, by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    rcases he with h | h
    · right; exact Finset.mem_image.mpr ⟨e, h, rfl⟩
    · left
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      have heq : e = (p.2, p.1) := hpe.symm
      subst heq; exact hp⟩

