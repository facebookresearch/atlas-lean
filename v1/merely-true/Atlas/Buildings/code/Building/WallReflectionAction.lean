/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.TitsTheoremProof
import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.Uniqueness

open ChamberComplex AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]

namespace WallReflectionAction

/-- Apply a word of vertex maps (e.g. wall reflections) sequentially to a
chamber $C$, taking images at each step. -/
def applyFunWord (word : List (V → V)) (C : Finset V) : Finset V :=
  word.foldl (fun D f => D.image f) C

/-- For adjacent chambers $C, D$, there is a folding fixing $C$ and sending
$D$ to $C$. -/
theorem adj_folding_fix_fold
    {cc : ChamberComplex V} (hsf : HasSufficientFoldings cc)
    {C D : Finset V} (hadj : cc.toSimplicialComplex.Adjacent C D) :
    ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C :=
  TitsTheoremProof.sufficient_foldings_fix_fold cc hsf C D hadj

/-- Each step of a gallery (adjacent pair) admits a folding collapsing it. -/
theorem gallery_step_has_folding
    {cc : ChamberComplex V} (hsf : HasSufficientFoldings cc)
    {C D : Finset V} (hadj : cc.toSimplicialComplex.Adjacent C D) :
    ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C :=
  adj_folding_fix_fold hsf hadj

/-- Extract the head adjacency from a gallery chain `a :: b :: rest`. -/
theorem gallery_chain_head_adj
    {cc : ChamberComplex V}
    {a b : Finset V} {rest : List (Finset V)}
    (hchain : List.IsChain cc.toSimplicialComplex.Adjacent (a :: b :: rest)) :
    cc.toSimplicialComplex.Adjacent a b := by
  rw [List.isChain_cons] at hchain
  exact hchain.1 b rfl

/-- The tail of a gallery chain remains a gallery chain. -/
theorem gallery_chain_tail
    {cc : ChamberComplex V}
    {a b : Finset V} {rest : List (Finset V)}
    (hchain : List.IsChain cc.toSimplicialComplex.Adjacent (a :: b :: rest)) :
    List.IsChain cc.toSimplicialComplex.Adjacent (b :: rest) := by
  rw [List.isChain_cons] at hchain
  exact hchain.2

/-- In a chain, consecutive elements are $R$-related at every index. -/
theorem isChain_getElem_adj {α : Type*} {R : α → α → Prop} {l : List α}
    (hchain : List.IsChain R l) {i : ℕ} (hi : i + 1 < l.length) :
    R l[i] l[i + 1] := by
  rw [List.isChain_iff_getElem] at hchain
  exact hchain i hi

/-- For any gallery of chambers, there exists a list of foldings (one per
adjacency step) collapsing each step. -/
theorem chain_foldings_exist
    {cc : ChamberComplex V} (hsf : HasSufficientFoldings cc)
    (cs : List (Finset V))
    (hchain : List.IsChain cc.toSimplicialComplex.Adjacent cs)
    (hall : ∀ C ∈ cs, cc.toSimplicialComplex.IsMaximal C) :
    ∃ (fs : List (Folding cc)),
      fs.length + 1 = cs.length ∨ (cs.length = 0 ∧ fs = []) := by
  match cs with
  | [] => exact ⟨[], Or.inr ⟨rfl, rfl⟩⟩
  | [_] => exact ⟨[], Or.inl (by simp)⟩
  | a :: b :: rest =>
    have hadj := gallery_chain_head_adj hchain
    have htail := gallery_chain_tail hchain
    obtain ⟨f, _, _⟩ := gallery_step_has_folding hsf hadj
    obtain ⟨fs_tail, htail_prop⟩ := chain_foldings_exist hsf (b :: rest)
      htail (fun C hC => hall C (List.mem_cons_of_mem a hC))
    exact ⟨f :: fs_tail, Or.inl (by
      cases htail_prop with
      | inl h => simp [List.length_cons] at h ⊢; omega
      | inr h => simp [List.length_cons] at h)⟩

end WallReflectionAction
