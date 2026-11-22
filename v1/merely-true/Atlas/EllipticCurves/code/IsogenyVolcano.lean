/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Atlas.EllipticCurves.code.RingClassField
import Atlas.EllipticCurves.code.HilbertClassPolynomial

noncomputable section

open Polynomial Finset

/-- A multigraph on vertex set `V`: each unordered pair `(v, w)` carries a
multiplicity `edgeMult v w : ℕ`, required to be symmetric in `v, w`. -/
structure Multigraph (V : Type*) where
  edgeMult : V → V → ℕ
  symm : ∀ v w, edgeMult v w = edgeMult w v

namespace Multigraph

variable {V : Type*} (G : Multigraph V)

/-- Two vertices `v, w` are adjacent in `G` iff their edge multiplicity is positive. -/
def Adj (v w : V) : Prop := 0 < G.edgeMult v w

/-- The (multi)degree of a vertex `v`: the sum of edge multiplicities to all
vertices of `V`. -/
def degree [Fintype V] (v : V) : ℕ := ∑ w : V, G.edgeMult v w

/-- The partial degree of `v` restricted to neighbours satisfying the predicate `P`. -/
def degreeOn [Fintype V] (v : V) (P : V → Prop) [DecidablePred P] : ℕ :=
  ∑ w ∈ Finset.univ.filter P, G.edgeMult v w

/-- `v` and `w` are connected in `G` iff there is a finite path (a reflexive-
transitive closure of adjacency) from `v` to `w`. -/
def Connected (v w : V) : Prop := Relation.ReflTransGen G.Adj v w

/-- The multigraph `G` is connected iff every pair of vertices is connected. -/
def IsConnected : Prop := ∀ v w : V, G.Connected v w

/-- The total degree decomposes as the partial degree over `P` plus the partial
degree over `¬P`. -/
theorem degreeOn_compl [Fintype V] (v : V) (P : V → Prop) [DecidablePred P] :
    G.degree v = G.degreeOn v P + G.degreeOn v (fun w => ¬P w) := by
  simp only [degree, degreeOn]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]

/-- Two predicates `P`, `Q` that agree on all neighbours of `v` (vertices with
positive edge multiplicity) give the same partial degree at `v`. -/
theorem degreeOn_congr [Fintype V] (v : V) (P Q : V → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ w, G.edgeMult v w > 0 → (P w ↔ Q w)) :
    G.degreeOn v P = G.degreeOn v Q := by
  unfold degreeOn
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hm : G.edgeMult v w = 0
  · simp [hm]
  · have hpos : G.edgeMult v w > 0 := Nat.pos_of_ne_zero hm
    have hiff := h w hpos
    by_cases hp : P w
    · simp [hp, hiff.mp hp]
    · simp [hp, mt hiff.mpr hp]

end Multigraph


namespace IsogenyGraph



/-- The set of possible `j`-invariants over `𝔽_p`, identified with `ZMod p`. -/
abbrev 𝔽_p_jInvariants (p : ℕ) : Type := ZMod p






end IsogenyGraph

/-- An `ℓ`-volcano: a connected multigraph organized into levels (the *surface* is
level `0`, the *floor* is level `depth`). Vertices off the floor have degree `ℓ + 1`,
surface vertices have a prescribed surface degree (`≤ 2`), and non-surface vertices
have a unique parent at the level above. Edges can only join the surface to itself
or adjacent levels. -/
structure IsogenyVolcano (ℓ : ℕ) where
  V : Type*
  [instFintype : Fintype V]
  [instDecEq : DecidableEq V]
  graph : Multigraph V
  depth : ℕ
  level : V → Fin (depth + 1)
  level_surj : Function.Surjective level
  surfaceDegree : ℕ
  surfaceDegree_le : surfaceDegree ≤ 2
  surface_regular : ∀ v, level v = ⟨0, Nat.zero_lt_succ _⟩ →
    graph.degreeOn v (fun w => level w = ⟨0, Nat.zero_lt_succ _⟩) = surfaceDegree
  unique_parent : ∀ v, (level v : ℕ) > 0 →
    graph.degreeOn v (fun w => (level w : ℕ) + 1 = (level v : ℕ)) = 1
  edges_between_levels : ∀ v w, graph.edgeMult v w > 0 →
    ((level v : ℕ) = 0 ∧ (level w : ℕ) = 0) ∨
    (level w : ℕ) + 1 = (level v : ℕ) ∨
    (level v : ℕ) + 1 = (level w : ℕ)
  degree_eq : ∀ v, (level v : ℕ) < depth → graph.degree v = ℓ + 1
  connected : graph.IsConnected

attribute [instance] IsogenyVolcano.instFintype IsogenyVolcano.instDecEq

namespace IsogenyVolcano

variable {ℓ : ℕ} (vol : IsogenyVolcano ℓ)

/-- A vertex of the volcano is on the *surface* (or *crater*) iff its level is `0`. -/
def isSurface (v : vol.V) : Prop :=
  vol.level v = ⟨0, Nat.zero_lt_succ _⟩

/-- A vertex of the volcano is on the *floor* iff its level is the maximal one
(`depth`). -/
def isFloor (v : vol.V) : Prop :=
  vol.level v = Fin.last vol.depth

/-- The depth of the volcano (the maximal level index). -/
def volcanoDepth : ℕ := vol.depth

/-- An edge `(v, w)` is *horizontal* iff it has positive multiplicity and both
endpoints lie on the surface. -/
def IsHorizontalEdge (v w : vol.V) : Prop :=
  vol.graph.edgeMult v w > 0 ∧ (vol.level v : ℕ) = 0 ∧ (vol.level w : ℕ) = 0

/-- An edge `(v, w)` is *descending* iff `w` is one level below `v`
(`level v + 1 = level w`). -/
def IsDescendingEdge (v w : vol.V) : Prop :=
  vol.graph.edgeMult v w > 0 ∧ (vol.level v : ℕ) + 1 = (vol.level w : ℕ)

/-- An edge `(v, w)` is *ascending* iff `w` is one level above `v`
(`level w + 1 = level v`). -/
def IsAscendingEdge (v w : vol.V) : Prop :=
  vol.graph.edgeMult v w > 0 ∧ (vol.level w : ℕ) + 1 = (vol.level v : ℕ)

/-- An edge is *vertical* iff it is either descending or ascending. -/
def IsVerticalEdge (v w : vol.V) : Prop :=
  vol.IsDescendingEdge v w ∨ vol.IsAscendingEdge v w

/-- An edge `(v, w)` is descending iff the reverse edge `(w, v)` is ascending. -/
theorem descending_iff_ascending_symm (v w : vol.V) :
    vol.IsDescendingEdge v w ↔ vol.IsAscendingEdge w v := by
  constructor
  · intro ⟨he, hl⟩
    exact ⟨by rw [vol.graph.symm]; exact he, hl⟩
  · intro ⟨he, hl⟩
    exact ⟨by rw [vol.graph.symm]; exact he, hl⟩

/-- An edge `(v, w)` is ascending iff the reverse edge `(w, v)` is descending. -/
theorem ascending_iff_descending_symm (v w : vol.V) :
    vol.IsAscendingEdge v w ↔ vol.IsDescendingEdge w v :=
  (vol.descending_iff_ascending_symm w v).symm

end IsogenyVolcano

namespace CMConductorTrichotomy

/-- If two coprime natural numbers `a, b` both divide a prime `ℓ`, then either both
are `1`, or one is `1` and the other is `ℓ`. -/
theorem coprime_dvd_prime {ℓ a b : ℕ} (hℓ : Nat.Prime ℓ) (hab : Nat.Coprime a b)
    (ha : a ∣ ℓ) (hb : b ∣ ℓ) :
    (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = ℓ) ∨ (a = ℓ ∧ b = 1) := by
  rcases hℓ.eq_one_or_self_of_dvd a ha with ha1 | haℓ
  · rcases hℓ.eq_one_or_self_of_dvd b hb with hb1 | hbℓ
    · exact Or.inl ⟨ha1, hb1⟩
    · exact Or.inr (Or.inl ⟨ha1, hbℓ⟩)
  · rcases hℓ.eq_one_or_self_of_dvd b hb with hb1 | hbℓ
    · exact Or.inr (Or.inr ⟨haℓ, hb1⟩)
    · exfalso; subst haℓ; subst hbℓ
      exact hℓ.one_lt.ne' (by rwa [Nat.Coprime, Nat.gcd_self] at hab)

/-- Conductor trichotomy for `ℓ`-isogenies: if conductors `f, f'` satisfy
`f ∣ ℓ f'` and `f' ∣ ℓ f`, then `f = f'` (horizontal), `f = ℓ f'` (ascending), or
`f' = ℓ f` (descending). Encodes the index relation behind Theorem 22.3. -/
theorem isogeny_order_trichotomy {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    {f f' : ℕ} (hf : 0 < f)
    (h1 : f ∣ ℓ * f') (h2 : f' ∣ ℓ * f) :
    f = f' ∨ f = ℓ * f' ∨ f' = ℓ * f := by

  set g := Nat.gcd f f'
  have hg : 0 < g := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
  set a := f / g
  set b := f' / g
  have hfa : f = g * a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f f')).symm
  have hfb : f' = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f f')).symm
  have hab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg

  have ha_dvd : a ∣ ℓ * b := by
    have : g * a ∣ g * (ℓ * b) := by
      have := h1; rw [hfa, hfb] at this
      rwa [mul_left_comm] at this
    exact (Nat.mul_dvd_mul_iff_left hg).mp this

  have hb_dvd : b ∣ ℓ * a := by
    have : g * b ∣ g * (ℓ * a) := by
      have := h2; rw [hfa, hfb] at this
      rwa [mul_left_comm] at this
    exact (Nat.mul_dvd_mul_iff_left hg).mp this

  have ha_dvd_ℓ : a ∣ ℓ := hab.dvd_of_dvd_mul_right ha_dvd
  have hb_dvd_ℓ : b ∣ ℓ := hab.symm.dvd_of_dvd_mul_right hb_dvd

  rcases coprime_dvd_prime hℓ hab ha_dvd_ℓ hb_dvd_ℓ with ⟨ha1, hb1⟩ | ⟨ha1, hbℓ⟩ | ⟨haℓ, hb1⟩
  ·
    left; rw [hfa, hfb, ha1, hb1]
  ·
    right; right; rw [hfa, hfb, ha1, hbℓ, mul_one, mul_comm]
  ·
    right; left; rw [hfa, hfb, haℓ, hb1, mul_one, mul_comm]

/-- Classification (Definition 22.4) of an `ℓ`-isogeny between CM elliptic curves
by the relation between the source and target endomorphism orders: horizontal
(`𝒪 = 𝒪''`), descending (`[𝒪 : 𝒪''] = ℓ`), or ascending (`[𝒪'' : 𝒪] = ℓ`). -/
inductive IsogenyType
  |     horizontal
  |     descending
  |     ascending
  deriving DecidableEq

/-- Classify an `ℓ`-isogeny by comparing source conductor `f` and target conductor
`f'`: `f = f'` is horizontal, `f = ℓ f'` is descending, otherwise ascending. -/
def classifyIsogeny (ℓ f f' : ℕ) : IsogenyType :=
  if f = f' then IsogenyType.horizontal
  else if f = ℓ * f' then IsogenyType.descending
  else IsogenyType.ascending

/-- If `f = f'` then the isogeny is classified as horizontal. -/
theorem classifyIsogeny_horizontal {ℓ f f' : ℕ} (h : f = f') :
    classifyIsogeny ℓ f f' = IsogenyType.horizontal := by
  simp [classifyIsogeny, h]

/-- If `f = ℓ f'` (with `f' > 0` and `ℓ > 1`), the isogeny is classified as descending. -/
theorem classifyIsogeny_descending {ℓ : ℕ} (hℓ : 1 < ℓ) {f f' : ℕ}
    (hf' : 0 < f') (h : f = ℓ * f') :
    classifyIsogeny ℓ f f' = IsogenyType.descending := by
  simp only [classifyIsogeny]
  have hne : ¬(ℓ * f' = f') := by nlinarith
  simp only [↓reduceIte, h, hne]

/-- If `f' = ℓ f` (with `f > 0` and `ℓ > 1`), the isogeny is classified as ascending. -/
theorem classifyIsogeny_ascending {ℓ : ℕ} (hℓ : 1 < ℓ) {f f' : ℕ}
    (hf : 0 < f) (h : f' = ℓ * f) :
    classifyIsogeny ℓ f f' = IsogenyType.ascending := by
  simp only [classifyIsogeny]
  have hne : ¬(f = f') := by nlinarith
  have hne2 : ¬(f = ℓ * f') := by
    intro heq; rw [h] at heq
    nlinarith [Nat.mul_le_mul_right f (show 1 ≤ ℓ from by omega)]
  simp only [hne, ↓reduceIte, hne2, ↓reduceIte]

end CMConductorTrichotomy

namespace IsogenyVolcano

variable {ℓ : ℕ} (vol : IsogenyVolcano ℓ)

/-- The *crater* (surface) subgraph of an isogeny volcano: the multigraph induced on
the surface (level `0`) vertices, keeping only edges that lie entirely on the
surface. -/
def craterGraph : Multigraph vol.V where
  edgeMult v w :=
    if vol.level v = ⟨0, Nat.zero_lt_succ _⟩ ∧ vol.level w = ⟨0, Nat.zero_lt_succ _⟩
    then vol.graph.edgeMult v w
    else 0
  symm v w := by
    split_ifs with h1 h2 h3
    · exact vol.graph.symm v w
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h3.2, h3.1⟩ h1
    · rfl

/-- For a surface vertex `v`, its degree in the crater subgraph equals the volcano's
`surfaceDegree`. -/
theorem crater_degree_surface (v : vol.V) (hv : vol.level v = ⟨0, Nat.zero_lt_succ _⟩) :
    vol.craterGraph.degree v = vol.surfaceDegree := by
  unfold craterGraph Multigraph.degree
  simp only [hv, true_and]
  have : (∑ w : vol.V, if vol.level w = ⟨0, Nat.zero_lt_succ _⟩
      then vol.graph.edgeMult v w else 0) =
    ∑ w ∈ Finset.univ.filter (fun w => vol.level w = ⟨0, Nat.zero_lt_succ _⟩),
      vol.graph.edgeMult v w := by
    rw [Finset.sum_filter]
  rw [this]
  exact vol.surface_regular v hv

/-- The crater subgraph is regular when restricted to surface vertices: any two
surface vertices have the same crater-degree. -/
theorem crater_is_regular :
    ∀ v w : vol.V, vol.isSurface v → vol.isSurface w →
      vol.craterGraph.degree v = vol.craterGraph.degree w := by
  intro v w hv hw
  rw [vol.crater_degree_surface v hv, vol.crater_degree_surface w hw]

/-- Surface vertices have crater-degree at most `2`, reflecting the surface-degree
bound `≤ 2`. -/
theorem crater_degree_le_two (v : vol.V) (hv : vol.isSurface v) :
    vol.craterGraph.degree v ≤ 2 := by
  rw [vol.crater_degree_surface v hv]
  exact vol.surfaceDegree_le

/-- For a non-surface vertex `v`, every neighbour `w` is either one level above or one
level below `v` — there are no horizontal edges away from the surface. -/
theorem nonsurface_edges_adjacent (v : vol.V) (hv : (vol.level v : ℕ) > 0)
    (w : vol.V) (hw : vol.graph.edgeMult v w > 0) :
    (vol.level w : ℕ) + 1 = (vol.level v : ℕ) ∨
    (vol.level v : ℕ) + 1 = (vol.level w : ℕ) := by
  rcases vol.edges_between_levels v w hw with ⟨hv0, _⟩ | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h

/-- For a non-surface vertex `v` with neighbour `w`, not being an ascending edge is
equivalent to being a descending edge. -/
theorem nonsurface_not_ascending_iff_descending (v : vol.V)
    (hv : (vol.level v : ℕ) > 0) (w : vol.V)
    (hw : vol.graph.edgeMult v w > 0) :
    ¬((vol.level w : ℕ) + 1 = (vol.level v : ℕ)) ↔
      (vol.level v : ℕ) + 1 = (vol.level w : ℕ) := by
  constructor
  · intro hna
    rcases vol.nonsurface_edges_adjacent v hv w hw with h | h
    · exact absurd h hna
    · exact h
  · intro hd hna; omega

/-- For a non-surface vertex `v` strictly above the floor, the descending degree
equals `ℓ`: there are exactly `ℓ` descending edges. -/
theorem nonsurface_descending_degree (v : vol.V)
    (hv_pos : (vol.level v : ℕ) > 0) (hv_lt : (vol.level v : ℕ) < vol.depth) :
    vol.graph.degreeOn v
      (fun w => (vol.level v : ℕ) + 1 = (vol.level w : ℕ)) = ℓ := by
  have h_deg := vol.degree_eq v hv_lt
  have h_asc := vol.unique_parent v hv_pos
  have h_split := vol.graph.degreeOn_compl v
    (fun w => (vol.level w : ℕ) + 1 = (vol.level v : ℕ))
  have h_congr := vol.graph.degreeOn_congr v
    (fun w => ¬((vol.level w : ℕ) + 1 = (vol.level v : ℕ)))
    (fun w => (vol.level v : ℕ) + 1 = (vol.level w : ℕ))
    (fun w hw => vol.nonsurface_not_ascending_iff_descending v hv_pos w hw)
  omega

/-- For a surface vertex `v` (when the volcano has positive depth), the number of
edges leaving the surface equals `ℓ + 1 - surfaceDegree`. -/
theorem surface_descending_degree (v : vol.V)
    (hv : vol.isSurface v) (hd : 0 < vol.depth) :
    vol.graph.degreeOn v
      (fun w => ¬vol.level w = ⟨0, Nat.zero_lt_succ _⟩) =
        ℓ + 1 - vol.surfaceDegree := by
  have h_deg := vol.degree_eq v (by
    have : (vol.level v : ℕ) = 0 := by
      simp only [isSurface] at hv; simp [hv]
    omega)
  have h_surf := vol.surface_regular v hv
  have h_split := vol.graph.degreeOn_compl v
    (fun w => vol.level w = ⟨0, Nat.zero_lt_succ _⟩)
  omega

/-- If the volcano has depth `0`, every vertex has level value `0`. -/
theorem level_val_eq_zero_of_depth_zero (hd : vol.depth = 0) (v : vol.V) :
    (vol.level v : ℕ) = 0 := by
  have := (vol.level v).isLt
  omega

/-- For a floor vertex (level equal to `depth`, with positive depth), the number of
non-ascending edges is `0`: floor vertices have only their unique ascending edge. -/
theorem floor_nonascending_degree_eq_zero
    (v : vol.V) (hv : (vol.level v : ℕ) = vol.depth) (hd : 0 < vol.depth) :
    vol.graph.degreeOn v (fun w => ¬((vol.level w : ℕ) + 1 = (vol.level v : ℕ))) = 0 := by
  unfold Multigraph.degreeOn
  apply Finset.sum_eq_zero
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨_, hw_not_asc⟩ := hw
  by_contra h_pos
  push Not at h_pos

  have h_pos' : vol.graph.edgeMult v w > 0 := Nat.pos_of_ne_zero (by omega)
  rcases vol.edges_between_levels v w h_pos' with ⟨hv0, _⟩ | hasc | hdesc
  · omega
  · exact hw_not_asc hasc
  · have := (vol.level w).isLt
    omega

/-- A floor vertex of a positive-depth volcano has total degree exactly `1` — its
single edge being the ascending one. -/
theorem floor_degree_eq_one (v : vol.V)
    (hv : (vol.level v : ℕ) = vol.depth) (hd : 0 < vol.depth) :
    vol.graph.degree v = 1 := by
  have h_asc := vol.unique_parent v (by omega)
  have h_nonasc := vol.floor_nonascending_degree_eq_zero v hv hd
  have h_split := vol.graph.degreeOn_compl v
    (fun w => (vol.level w : ℕ) + 1 = (vol.level v : ℕ))
  omega

/-- For a depth-zero volcano (no non-surface levels) every vertex has total degree
equal to the surface degree. -/
theorem degree_eq_surfaceDegree_of_depth_zero (hd : vol.depth = 0) (v : vol.V) :
    vol.graph.degree v = vol.surfaceDegree := by
  have hv0 : (vol.level v : ℕ) = 0 := vol.level_val_eq_zero_of_depth_zero hd v
  have hv_surf : vol.level v = ⟨0, Nat.zero_lt_succ _⟩ := by
    ext; exact hv0
  have h_surf := vol.surface_regular v hv_surf
  have h_split := vol.graph.degreeOn_compl v
    (fun w => vol.level w = ⟨0, Nat.zero_lt_succ _⟩)
  have h_nonsurface_zero : vol.graph.degreeOn v
      (fun w => ¬vol.level w = ⟨0, Nat.zero_lt_succ _⟩) = 0 := by
    unfold Multigraph.degreeOn
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    have hw0 : (vol.level w : ℕ) = 0 := vol.level_val_eq_zero_of_depth_zero hd w
    have : vol.level w = ⟨0, Nat.zero_lt_succ _⟩ := by ext; exact hw0
    exact absurd this hw.2
  omega

/-- Lemma 22.13: for any vertex `v` in an ordinary component of depth `d` of
`G_ℓ(𝔽_q)`, either `deg v ≤ 2` and `v` is on the floor, or `deg v = ℓ + 1` and `v`
is not on the floor. -/
theorem lemma_22_13 (v : vol.V) :
    (vol.graph.degree v ≤ 2 ∧ vol.isFloor v) ∨
    (vol.graph.degree v = ℓ + 1 ∧ ¬vol.isFloor v) := by
  by_cases hd : vol.depth = 0
  ·
    left
    constructor
    · rw [vol.degree_eq_surfaceDegree_of_depth_zero hd v]
      exact vol.surfaceDegree_le
    · unfold isFloor
      have hv0 := vol.level_val_eq_zero_of_depth_zero hd v
      ext
      simp only [Fin.val_last]
      omega

  ·
    have hd_pos : 0 < vol.depth := Nat.pos_of_ne_zero hd
    by_cases hf : (vol.level v : ℕ) = vol.depth
    ·
      left
      constructor
      · rw [vol.floor_degree_eq_one v hf hd_pos]
        omega
      · unfold isFloor; ext; simp [Fin.val_last, hf]
    ·
      right
      have hlt : (vol.level v : ℕ) < vol.depth := by
        have := (vol.level v).isLt
        omega
      constructor
      · exact vol.degree_eq v hlt
      · unfold isFloor
        intro h
        have : (vol.level v : ℕ) = vol.depth := by
          rw [h]; simp [Fin.val_last]
        exact hf this

end IsogenyVolcano

namespace CMIsogeny

/-- Data attached to a CM `ℓ`-isogeny problem: an imaginary quadratic discriminant
`D < 0`, a prime `ℓ`, and a positive conductor `f` of the source order. -/
structure CMIsogenyData where
  D : ℤ
  hD_neg : D < 0
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  f : ℕ
  hf_pos : 0 < f

/-- Counts of `ℓ`-isogenies from a surface (`ℓ ∤ f`) CM elliptic curve, organized by
type. Following Theorem 22.5, there are `1 + (D/ℓ)` horizontal, `ℓ - (D/ℓ)`
descending, and `0` ascending isogenies. -/
structure SurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_ndvd_f : ¬(C.ℓ ∣ C.f)
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : (numHorizontal : ℤ) = 1 + jacobiSym C.D C.ℓ
  descending_eq : (numDescending : ℤ) = ↑C.ℓ - jacobiSym C.D C.ℓ
  ascending_eq : numAscending = 0

/-- Counts of `ℓ`-isogenies from a non-surface (`ℓ ∣ f`) CM elliptic curve: `0`
horizontal, `ℓ` descending, and `1` ascending. -/
structure NonSurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_dvd_f : C.ℓ ∣ C.f
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : numHorizontal = 0
  descending_eq : numDescending = C.ℓ
  ascending_eq : numAscending = 1




/-- Total `ℓ`-isogeny count from a surface CM curve sums to `ℓ + 1`. -/
theorem surface_total_count (C : CMIsogenyData) (S : SurfaceIsogenyCounts C) :
    (S.numHorizontal : ℤ) + S.numDescending + S.numAscending = C.ℓ + 1 := by
  rw [S.horizontal_eq, S.descending_eq, S.ascending_eq]
  push_cast
  ring

/-- Total `ℓ`-isogeny count from a non-surface CM curve sums to `ℓ + 1`. -/
theorem nonsurface_total_count (C : CMIsogenyData) (N : NonSurfaceIsogenyCounts C) :
    (N.numHorizontal : ℤ) + N.numDescending + N.numAscending = C.ℓ + 1 := by
  rw [N.horizontal_eq, N.descending_eq, N.ascending_eq]
  push_cast
  ring

end CMIsogeny

namespace VolcanoStructure

/-- Data for an ordinary component of the `ℓ`-isogeny graph over `𝔽_q`: a prime `ℓ`
coprime to `q`, the Hasse trace `t` (with `t² < 4q`), a fundamental imaginary
quadratic discriminant `D₀`, a positive base conductor `f₀`, and the class number. -/
structure OrdinaryIsogenyComponent where
  q : ℕ
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  t : ℤ
  hHasse : t ^ 2 < 4 * (q : ℤ)
  D₀ : ℤ
  hD₀_neg : D₀ < 0
  f₀ : ℕ
  hf₀_pos : 0 < f₀
  classOrder : ℕ
  hClassOrder_pos : 0 < classOrder

/-- Kohel's structural data for an ordinary `ℓ`-volcano: an `IsogenyVolcano` of
prime degree `ℓ`, equipped with a conductor function `f₀ · ℓ^level` on vertices,
crater data tied to the Kronecker symbol `(D₀/ℓ)`, and the depth-determining
equation `4q = t² - ℓ^{2d} v² D₀`. -/
structure KohelVolcano (C : OrdinaryIsogenyComponent) where
  volcano : IsogenyVolcano C.ℓ
  conductor : volcano.V → ℕ
  conductor_eq_level : ∀ v, conductor v = C.f₀ * C.ℓ ^ (volcano.level v : ℕ)
  surface_degree_eq : (volcano.surfaceDegree : ℤ) = 1 + jacobiSym C.D₀ C.ℓ
  surface_size_nonneg :
    0 ≤ jacobiSym C.D₀ C.ℓ →
    Fintype.card {v : volcano.V // (volcano.level v : ℕ) = 0} = C.classOrder
  surface_size_neg :
    jacobiSym C.D₀ C.ℓ = -1 →
    Fintype.card {v : volcano.V // (volcano.level v : ℕ) = 0} = 1
  v_aux : ℤ
  depth_eq : (4 : ℤ) * C.q = C.t ^ 2 - ↑C.ℓ ^ (2 * volcano.depth) * v_aux ^ 2 * C.D₀
  hℓ_ndvd_v : ¬((C.ℓ : ℤ) ∣ v_aux)
  hℓ_ndvd_f₀ : ¬(C.ℓ ∣ C.f₀)
  index_step : ∀ (i : ℕ), i < volcano.depth → ∀ v w,
    (volcano.level v : ℕ) = i → (volcano.level w : ℕ) = i + 1 →
    conductor w = C.ℓ * conductor v











variable {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)

/-- A surface vertex of the Kohel volcano has conductor equal to the base conductor
`f₀`. -/
theorem surface_conductor_eq (v : K.volcano.V)
    (hv : (K.volcano.level v : ℕ) = 0) :
    K.conductor v = C.f₀ := by
  rw [K.conductor_eq_level v]
  simp [hv]

/-- A floor vertex of the Kohel volcano has conductor `f₀ · ℓ^depth`. -/
theorem floor_conductor_eq (v : K.volcano.V)
    (hv : (K.volcano.level v : ℕ) = K.volcano.depth) :
    K.conductor v = C.f₀ * C.ℓ ^ K.volcano.depth := by
  rw [K.conductor_eq_level v]
  simp [hv]

/-- Moving down one level in the Kohel volcano multiplies the conductor by `ℓ`. -/
theorem conductor_increases_by_ℓ (v w : K.volcano.V)
    (hv : (K.volcano.level v : ℕ) + 1 = (K.volcano.level w : ℕ))
    (_hlt : (K.volcano.level v : ℕ) < K.volcano.depth) :
    K.conductor w = C.ℓ * K.conductor v := by
  have hvi := K.conductor_eq_level v
  have hwi := K.conductor_eq_level w
  rw [hvi, hwi]
  have : (K.volcano.level w : ℕ) = (K.volcano.level v : ℕ) + 1 := hv.symm
  rw [this, pow_succ]
  ring

/-- Re-export: the surface degree of a Kohel volcano is at most `2`. -/
theorem surface_degree_le_two : K.volcano.surfaceDegree ≤ 2 :=
  K.volcano.surfaceDegree_le

/-- For a surface vertex, the crater degree equals `1 + (D₀/ℓ)`. -/
theorem crater_degree_eq_jacobiSym (v : K.volcano.V)
    (hv : K.volcano.isSurface v) :
    (K.volcano.craterGraph.degree v : ℤ) = 1 + jacobiSym C.D₀ C.ℓ := by
  rw [K.volcano.crater_degree_surface v hv]
  exact K.surface_degree_eq

/-- For a non-surface, non-floor vertex of the Kohel volcano, the descending degree
equals `ℓ`. -/
theorem nonsurface_descending_eq_ℓ (v : K.volcano.V)
    (hv_pos : (K.volcano.level v : ℕ) > 0)
    (hv_lt : (K.volcano.level v : ℕ) < K.volcano.depth) :
    K.volcano.graph.degreeOn v
      (fun w => (K.volcano.level v : ℕ) + 1 = (K.volcano.level w : ℕ)) = C.ℓ :=
  K.volcano.nonsurface_descending_degree v hv_pos hv_lt

/-- For a surface vertex of a positive-depth Kohel volcano, the number of edges
leaving the surface equals `ℓ + 1 - surfaceDegree`. -/
theorem surface_descending_eq (v : K.volcano.V)
    (hv : K.volcano.isSurface v) (hd : 0 < K.volcano.depth) :
    K.volcano.graph.degreeOn v
      (fun w => ¬K.volcano.level w = ⟨0, Nat.zero_lt_succ _⟩) =
        C.ℓ + 1 - K.volcano.surfaceDegree :=
  K.volcano.surface_descending_degree v hv hd

end VolcanoStructure

namespace CMSetCardinality

open Elliptic_Curves Elliptic_Curves.Deuring



/-- `D` is contained in `D'` (as orders) iff `D = u² D'` for some positive integer
`u` and `D'` is itself an imaginary quadratic discriminant. -/
def OrderContains (D D' : ℤ) : Prop :=
  (∃ u : ℤ, 0 < u ∧ D = u ^ 2 * D') ∧ IsImagQuadDiscriminant D'

/-- If `D` contains `D'` then `D'` is itself an imaginary quadratic discriminant. -/
theorem orderContains_isDisc
    (D D' : ℤ) (_hD : IsImagQuadDiscriminant D)
    (hcontains : OrderContains D D') :
    IsImagQuadDiscriminant D' :=
  hcontains.2

/-- Coprimality with `|D|` descends to coprimality with `|D'|` along an order
containment. -/
theorem coprime_of_orderContains
    (D D' : ℤ) (q : ℕ)
    (hcop : Nat.Coprime q D.natAbs)
    (hcontains : OrderContains D D') :
    Nat.Coprime q D'.natAbs := by
  obtain ⟨⟨u, _, hD⟩, _⟩ := hcontains
  rw [Nat.Coprime] at hcop ⊢
  have hdvd : D'.natAbs ∣ D.natAbs := by
    rw [hD]
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    exact Dvd.intro_left (u.natAbs ^ 2) rfl
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

/-- A norm-equation solution for `D` lifts to a norm-equation solution for any `D'`
that `D` contains. -/
theorem normEquation_of_orderContains
    (D D' : ℤ) (q : ℕ) (t v : ℤ)
    (hne : Elliptic_Curves.NormEquation D q t v)
    (hcontains : OrderContains D D') :
    ∃ w : ℤ, Elliptic_Curves.NormEquation D' q t w := by
  obtain ⟨⟨u, _, hD⟩, _⟩ := hcontains
  refine ⟨u * v, ?_⟩
  simp only [Elliptic_Curves.NormEquation] at hne ⊢
  rw [hD] at hne
  ring_nf at hne ⊢
  linarith




end CMSetCardinality

namespace IsogenyCount

open Elliptic_Curves Elliptic_Curves.Deuring

/-- Data for counting `ℓ`-isogenies from a CM elliptic curve over `𝔽_q`: an
imaginary quadratic discriminant `D` with class data, a prime `ℓ ∤ q` coprime to
`|D|`, and a conductor `f`. -/
structure CMCurveData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  q : ℕ
  hq : 1 < q
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  hcop : Nat.Coprime q D.natAbs
  f : ℕ
  hf_pos : 0 < f

/-- The discriminant of a descendant order, obtained by multiplying `D` by `ℓ²`. -/
def CMCurveData.descendantDisc (C : CMCurveData) : ℤ := C.ℓ ^ 2 * C.D



end IsogenyCount

namespace CMTorsor

open Elliptic_Curves Elliptic_Curves.Deuring

/-- Data for a CM torsor: an imaginary quadratic discriminant `D` and a prime power
`q` coprime to `|D|`. -/
structure CMTorsorData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  q : ℕ
  hq : 1 < q
  hcop : Nat.Coprime q D.natAbs








end CMTorsor

end
