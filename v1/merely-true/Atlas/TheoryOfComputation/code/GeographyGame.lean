/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic

namespace GeographyGame

variable {V : Type*} [DecidableEq V]

/-- A position in Generalized Geography: the current vertex (whose owner is
about to move) together with the set of already-visited vertices. -/
structure Position (V : Type*) where
  current : V
  visited : Finset V

/-- `next` is a valid move from `pos` in `G`: there is an edge from the current
vertex to `next`, and `next` has not been visited. -/
def ValidMove (G : Digraph V) (pos : Position V) (next : V) : Prop :=
  G.Adj pos.current next ∧ next ∉ pos.visited

/-- Update a position by moving the token to `next`, marking it visited. -/
def makeMove (pos : Position V) (next : V) : Position V where
  current := next
  visited := pos.visited ∪ {next}

/-- A position is stuck if no valid move exists — the player to move loses. -/
def IsStuck (G : Digraph V) (pos : Position V) : Prop :=
  ∀ v : V, ¬ ValidMove G pos v

/-- The "has winning strategy" relation for Generalized Geography. `HasWinningStrategy G pos b`
holds when the player whose turn it is (`b = true` for Player I, `b = false` for Player II)
has a strategy to win from position `pos`:
- Player I (`true`) wins by choosing some valid move leading to a position where Player II loses.
- Player II (`false`) wins immediately if the position is stuck (Player I cannot move), or if
  every valid move by Player I leads to a Player-I-winning position. -/
inductive HasWinningStrategy (G : Digraph V) : Position V → Bool → Prop where
  | playerI_moves {pos : Position V} {next : V}
    (hmove : ValidMove G pos next)
    (hwin : HasWinningStrategy G (makeMove pos next) false) :
    HasWinningStrategy G pos true
  | playerII_stuck {pos : Position V}
    (hstuck : IsStuck G pos) :
    HasWinningStrategy G pos false
  | playerII_moves {pos : Position V}
    (hnotStuck : ¬ IsStuck G pos)
    (hwin : ∀ next : V, ValidMove G pos next →
      HasWinningStrategy G (makeMove pos next) true) :
    HasWinningStrategy G pos false

/-- The initial position of the game starting at vertex `s`, with `s` already visited. -/
def initPosition (s : V) : Position V where
  current := s
  visited := {s}

/-- **Sipser, Lecture 19.** The language
`GG = {⟨G, a⟩ | Player I has a forced win in Generalized Geography on G from a}`.
`GG` is PSPACE-complete. -/
def GG (G : Digraph V) (s : V) : Prop :=
  HasWinningStrategy G (initPosition s) true

end GeographyGame
