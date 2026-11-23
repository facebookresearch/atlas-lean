/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.ForestCharacterization

open SimpleGraph Set

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

lemma mem_edgeSet_adj {G : SimpleGraph V} (M : G.Subgraph) {v : V} {e : Sym2 V}
    (he : e ∈ M.edgeSet) (hve : v ∈ e) : ∃ w, M.Adj v w ∧ e = s(v, w) := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Subgraph.edgeSet, Sym2.fromRel_prop] at he
    simp only [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact ⟨b, he, rfl⟩
    · exact ⟨a, he.symm, Sym2.eq_swap⟩

lemma Subgraph.IsMatching.edgeSet_encard_le_of_isVertexCover
    {M : G.Subgraph} (hM : M.IsMatching) {C : Set V}
    (hC : G.IsVertexCover C) : M.edgeSet.encard ≤ C.encard := by
  classical
  have h_endpt : ∀ e ∈ M.edgeSet, ∃ v : V, v ∈ C ∧ v ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Subgraph.edgeSet, Sym2.fromRel_prop] at he
      rcases hC (M.adj_sub he) with hv | hw
      · exact ⟨v, hv, Sym2.mem_mk_left v w⟩
      · exact ⟨w, hw, Sym2.mem_mk_right v w⟩
  let f : Sym2 V → V := fun e =>
    if h : e ∈ M.edgeSet then (h_endpt e h).choose else e.out.1
  have hf_maps : MapsTo f M.edgeSet C := by
    intro e he; simp only [f, dif_pos he]; exact (h_endpt e he).choose_spec.1
  have hf_inj : InjOn f M.edgeSet := by
    intro e₁ he₁ e₂ he₂ hfeq
    simp only [f, dif_pos he₁, dif_pos he₂] at hfeq
    have hv₁_in := (h_endpt e₁ he₁).choose_spec.2
    have hv₂_in := (h_endpt e₂ he₂).choose_spec.2
    obtain ⟨w₁, hadj₁, heq₁⟩ := mem_edgeSet_adj M he₁ hv₁_in
    obtain ⟨w₂, hadj₂, heq₂⟩ := mem_edgeSet_adj M he₂ (hfeq ▸ hv₂_in)
    have := hM.eq_of_adj_left hadj₁ hadj₂
    rw [heq₁, heq₂, this]
  exact Set.encard_le_encard_of_injOn hf_maps hf_inj

theorem matchingNum_le_vertexCoverNum : G.matchingNum ≤ G.vertexCoverNum := by
  apply iSup_le; intro M; apply iSup_le; intro hM
  apply le_iInf; intro C; apply le_iInf; intro hC
  exact hM.edgeSet_encard_le_of_isVertexCover hC

def alternatingForestSet (G : SimpleGraph V) (M : G.Subgraph) (A : Set V) : Set V :=
  {v | IsInAlternatingForest G M A v}

def konigCover (G : SimpleGraph V) (M : G.Subgraph) (A B : Set V) : Set V :=
  (A \ alternatingForestSet G M A) ∪ (B ∩ alternatingForestSet G M A)

lemma unmatched_A_in_forest {M : G.Subgraph} {A : Set V} {v : V}
    (hvA : v ∈ A) (hvM : v ∉ M.verts) : IsInAlternatingForest G M A v :=
  ⟨v, Walk.nil, hvA, hvM, Walk.IsPath.nil, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

lemma Walk.edges_takeUntil_isPrefix {u v w : V} (p : G.Walk u v)
    (hw : w ∈ p.support) : (p.takeUntil w hw).edges <+: p.edges := by
  have heq := congr_arg Walk.edges (Walk.take_spec p hw)
  rw [Walk.edges_append] at heq
  exact ⟨(p.dropUntil w hw).edges, heq⟩

lemma alternatingFrom_takeUntil {u v w : V} {p : G.Walk u v} {M : G.Subgraph}
    (halt : p.IsAlternatingFrom M) (hw : w ∈ p.support) :
    (p.takeUntil w hw).IsAlternatingFrom M := by
  intro i hi
  have hpref := Walk.edges_takeUntil_isPrefix p hw
  have hi' : i < p.edges.length := Nat.lt_of_lt_of_le hi (List.IsPrefix.length_le hpref)
  have hget : (p.takeUntil w hw).edges[i]'hi = p.edges[i]'hi' :=
    List.IsPrefix.getElem hpref hi
  rw [hget]
  exact halt i hi'

lemma forest_edge_not_in_M {A B : Set V} (hBip : G.IsBipartiteWith A B)
    {M : G.Subgraph} (hM : M.IsMatching)
    {a v w : V} {p : G.Walk a v}
    (haA : a ∈ A) (haM : a ∉ M.verts)
    (hvA : v ∈ A) (hpath : p.IsPath) (halt : p.IsAlternatingFrom M)
    (hadj : G.Adj v w) (hw_supp : w ∉ p.support) :
    s(v, w) ∉ M.edgeSet := by
  intro habs
  rw [Subgraph.mem_edgeSet] at habs
  have hv_matched : v ∈ M.verts := M.edge_vert habs

  have heven : Even p.edges.length := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have := (walk_endpoint_parity hBip p).1 haA |>.2 hodd
    exact absurd hvA (Set.disjoint_left.mp hBip.disjoint.symm this)

  by_cases hp0 : p.edges.length = 0
  · have hav : a = v := p.eq_of_length_eq_zero (by rw [← p.length_edges]; omega)
    rw [← hav] at hv_matched; exact haM hv_matched
  ·
    have hpos : 0 < p.edges.length := Nat.pos_of_ne_zero hp0
    have hlast_idx : p.edges.length - 1 < p.edges.length := Nat.sub_lt hpos Nat.one_pos
    have hlast_odd : Odd (p.edges.length - 1) := by
      obtain ⟨k, hk⟩ := heven
      cases k with
      | zero => omega
      | succ j => exact ⟨j, by omega⟩
    have hlast_in_M := (halt _ hlast_idx).2 hlast_odd
    have hlast_eq := Walk.edges_getElem_eq p _ hlast_idx
    rw [show p.edges.length - 1 + 1 = p.edges.length from by omega] at hlast_eq
    have hgetv : p.getVert p.edges.length = v := by rw [p.length_edges]; exact p.getVert_length
    rw [hgetv] at hlast_eq

    rw [hlast_eq] at hlast_in_M
    rw [Subgraph.mem_edgeSet] at hlast_in_M

    have heqw : w = p.getVert (p.edges.length - 1) :=
      hM.eq_of_adj_left habs hlast_in_M.symm
    rw [heqw] at hw_supp
    exact hw_supp (Walk.getVert_mem_support p _)

theorem konig_cover_isVertexCover {A B : Set V} (hBip : G.IsBipartiteWith A B)
    {M : G.Subgraph} (hM : M.IsMatching) (hMax : M.IsMaxMatching) :
    G.IsVertexCover (konigCover G M A B) := by
  open Classical in
  intro v w hadj
  rcases hBip.mem_of_adj hadj with ⟨hvA, hwB⟩ | ⟨hvB, hwA⟩
  ·
    by_cases hvF : v ∈ alternatingForestSet G M A
    ·
      right; apply Set.mem_union_right
      constructor
      · exact hwB
      ·
        obtain ⟨a, p, haA, haM, hpath, halt⟩ := hvF
        show IsInAlternatingForest G M A w
        by_cases hw_supp : w ∈ p.support
        · exact ⟨a, p.takeUntil w hw_supp, haA, haM,
            hpath.takeUntil hw_supp, alternatingFrom_takeUntil halt hw_supp⟩
        · have hedge_not_M : s(v, w) ∉ M.edgeSet :=
            forest_edge_not_in_M hBip hM haA haM hvA hpath halt hadj hw_supp
          refine ⟨a, p.concat hadj, haA, haM, hpath.concat hw_supp hadj, ?_⟩
          intro i hi
          have hlen : (p.concat hadj).edges.length = p.edges.length + 1 := by
            simp only [Walk.edges_concat, List.length_concat]
          by_cases hi_last : i < p.edges.length
          · have hget : (p.concat hadj).edges[i]'hi = p.edges[i]'hi_last := by
              simp only [Walk.edges_concat, List.concat_eq_append]
              exact List.getElem_append_left hi_last
            rw [hget]; exact halt i hi_last
          · have hi_eq : i = p.edges.length := by omega
            subst hi_eq
            have hget : (p.concat hadj).edges[p.edges.length]'hi = s(v, w) := by
              simp only [Walk.edges_concat, List.concat_eq_append,
                List.getElem_concat_length rfl]
            rw [hget]
            exact ⟨fun _ => hedge_not_M, fun hodd => by
              exfalso
              have heven : Even p.edges.length := by
                by_contra h; rw [Nat.not_even_iff_odd] at h
                exact absurd hvA (Set.disjoint_left.mp hBip.disjoint.symm
                  ((walk_endpoint_parity hBip p).1 haA |>.2 h))
              exact (Nat.not_odd_iff_even.mpr heven) hodd⟩
    ·
      left; exact Set.mem_union_left _ ⟨hvA, hvF⟩
  ·
    by_cases hwF : w ∈ alternatingForestSet G M A
    ·
      left; apply Set.mem_union_right
      constructor
      · exact hvB
      · obtain ⟨a, p, haA, haM, hpath, halt⟩ := hwF
        show IsInAlternatingForest G M A v
        by_cases hv_supp : v ∈ p.support
        · exact ⟨a, p.takeUntil v hv_supp, haA, haM,
            hpath.takeUntil hv_supp, alternatingFrom_takeUntil halt hv_supp⟩
        · have hadj' : G.Adj w v := hadj.symm
          have hedge_not_M : s(w, v) ∉ M.edgeSet :=
            forest_edge_not_in_M hBip hM haA haM hwA hpath halt hadj' hv_supp
          refine ⟨a, p.concat hadj', haA, haM, hpath.concat hv_supp hadj', ?_⟩
          intro i hi
          have hlen : (p.concat hadj').edges.length = p.edges.length + 1 := by
            simp only [Walk.edges_concat, List.length_concat]
          by_cases hi_last : i < p.edges.length
          · have hget : (p.concat hadj').edges[i]'hi = p.edges[i]'hi_last := by
              simp only [Walk.edges_concat, List.concat_eq_append]
              exact List.getElem_append_left hi_last
            rw [hget]; exact halt i hi_last
          · have hi_eq : i = p.edges.length := by omega
            subst hi_eq
            have hget : (p.concat hadj').edges[p.edges.length]'hi = s(w, v) := by
              simp only [Walk.edges_concat, List.concat_eq_append,
                List.getElem_concat_length rfl]
            rw [hget]
            exact ⟨fun _ => hedge_not_M, fun hodd => by
              exfalso
              have heven : Even p.edges.length := by
                by_contra h; rw [Nat.not_even_iff_odd] at h
                exact absurd hwA (Set.disjoint_left.mp hBip.disjoint.symm
                  ((walk_endpoint_parity hBip p).1 haA |>.2 h))
              exact (Nat.not_odd_iff_even.mpr heven) hodd⟩
    ·
      right; exact Set.mem_union_left _ ⟨hwA, hwF⟩




end SimpleGraph
