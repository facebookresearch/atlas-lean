/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Basic

set_option maxHeartbeats 400000

namespace LovaszLocalLemma

open Set Finset

/-- The coloring $c : \mathbb{R} \to \text{Fin}\ k$ is multicolored on the set $T$ if every color $i \in \text{Fin}\ k$ is attained by some $x \in T$. -/
def IsMulticolored (k : ℕ) (c : ℝ → Fin k) (T : Set ℝ) : Prop :=
  ∀ i : Fin k, ∃ x ∈ T, c x = i

/-- The translate of $S \subseteq \mathbb{R}$ by $t$, i.e. $S + t = \{s + t : s \in S\}$. -/
def translate (S : Set ℝ) (t : ℝ) : Set ℝ := (· + t) '' S

/-- The set of $k$-colorings of $\mathbb{R}$ that are multicolored on the translate $S + t$. -/
def goodColorings (k : ℕ) (S : Finset ℝ) (t : ℝ) : Set (ℝ → Fin k) :=
  {c | IsMulticolored k c (translate (↑S) t)}

/-- The evaluation event $\{c : \mathbb{R} \to \text{Fin}\ k \mid c(x) = i\}$ is clopen in the product topology with discrete fibres. -/
lemma isClopen_eval_eq {k : ℕ} (x : ℝ) (i : Fin k) :
    IsClopen {c : ℝ → Fin k | c x = i} := by
  have heq : {c : ℝ → Fin k | c x = i} = (fun c => c x) ⁻¹' {i} := by
    ext c; simp
  rw [heq]
  exact ⟨(isClosed_discrete _).preimage (continuous_apply x),
         (isOpen_discrete _).preimage (continuous_apply x)⟩

/-- For $k \ge 1$, the set of colorings that are multicolored on $S + t$ is closed in the product topology. -/
lemma isClosed_goodColorings {k : ℕ} (_hk : 0 < k) (S : Finset ℝ) (t : ℝ) :
    IsClosed (goodColorings k S t) := by
  suffices h : goodColorings k S t =
      ⋂ (i : Fin k), ⋃ s ∈ S, {c : ℝ → Fin k | c (↑s + t) = i} by
    rw [h]
    apply isClosed_iInter
    intro i
    exact S.finite_toSet.isClosed_biUnion (fun s _ =>
      (isClopen_eval_eq (↑s + t) i).1)
  ext c
  simp only [goodColorings, IsMulticolored, translate, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_iInter, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · intro h i
    obtain ⟨x, ⟨s, hs, hsx⟩, hc⟩ := h i
    exact ⟨s, hs, hsx ▸ hc⟩
  · intro h i
    obtain ⟨s, hs, hc⟩ := h i
    exact ⟨s + t, ⟨s, hs, rfl⟩, hc⟩



end LovaszLocalLemma

noncomputable section

namespace Beck

open Set Topology Finset

/-- The arithmetic progression $a, a+d, \dots, a+(k-1)d$ is monochromatic under the $\{0,1\}$-coloring $c$ of $\mathbb{Z}$ if all of its $k$ terms have the same color as $a$. -/
def IsMonochromaticAP (c : ℤ → Bool) (k : ℕ) (a d : ℤ) : Prop :=
  ∀ i : Fin k, c (a + ↑(i : ℕ) * d) = c a

/-- The set of colorings under which a fixed AP $(a, d, k)$ is monochromatic is open in the product topology with discrete fibres. -/
lemma isOpen_monochromaticAP (k : ℕ) (a d : ℤ) :
    IsOpen {c : ℤ → Bool | IsMonochromaticAP c k a d} := by
  simp only [IsMonochromaticAP, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have h : {c : ℤ → Bool | c (a + ↑(i : ℕ) * d) = c a} =
    (fun c => (c (a + ↑(i : ℕ) * d), c a)) ⁻¹' {p : Bool × Bool | p.1 = p.2} := by
    ext c; simp
  rw [h]
  exact ((continuous_apply _).prodMk (continuous_apply _)).isOpen_preimage _ (isOpen_discrete _)



end Beck
