/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

variable {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]

/-- A **generalized BN-pair** (in the sense of Bourbaki §IV.2.6, Section 5.5):
an ambient group $\tilde G$ with a normal finite-index subgroup $G$ carrying a strict
BN-pair $(B, N, T, W)$, together with enlarged subgroups $\tilde B \supseteq B$,
$\tilde N \supseteq N$ and $\tilde T = \tilde B \cap \tilde N$ satisfying the
analogues of the Bruhat decomposition $\tilde G = \tilde T \cdot \bigsqcup_w BwB$,
plus compatibility conditions making $\tilde T$ normalize $B$, $N$, and act on the
set $S$ of simple reflections by permutations, with finite "twist group"
$\tilde T / (\tilde T \cap G)$. -/
structure GeneralizedBNPair (Gt : Type*) [Group Gt]
    (M : CoxeterMatrix B_idx) where
  G : Subgroup Gt
  strictBNPair : BNPair G M
  Bt : Subgroup Gt
  Nt : Subgroup Gt
  Tt : Subgroup Gt
  Tt_eq : Tt = Bt ⊓ Nt
  B_le_Bt : strictBNPair.B.map G.subtype ≤ Bt
  N_le_Nt : strictBNPair.N.map G.subtype ≤ Nt
  G_normal : G.Normal
  finiteIndex : G.FiniteIndex
  Tt_normalizes_B :
    ∀ (t : Gt) (_ : t ∈ Tt) (b : Gt) (_ : b ∈ strictBNPair.B.map G.subtype),
      t * b * t⁻¹ ∈ strictBNPair.B.map G.subtype
  Tt_normalizes_N :
    ∀ (t : Gt) (_ : t ∈ Tt) (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype),
      t * n * t⁻¹ ∈ strictBNPair.N.map G.subtype
  TtInterG_eq :
    Tt ⊓ G = strictBNPair.T.map G.subtype

  Nt_decomp :
    ∀ (x : Gt) (_ : x ∈ Nt),
      ∃ (t : Gt) (_ : t ∈ Tt) (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype),
        x = t * n
  Tt_stabilizes_S :
    ∀ (t : Gt) (_ : t ∈ Tt),
      ∃ (σ : Equiv.Perm B_idx), ∀ (s : B_idx) (n : strictBNPair.N),
        strictBNPair.π n = M.toCoxeterSystem.simple s →
        ∃ (n' : strictBNPair.N),
          strictBNPair.π n' = M.toCoxeterSystem.simple (σ s) ∧
          ((n' : G) : Gt) = t * ((n : G) : Gt) * t⁻¹

  Tt_inter_Nlifted_eq :
    Tt ⊓ strictBNPair.N.map G.subtype = strictBNPair.T.map G.subtype
  generalized_bruhat :
    ∀ (g : Gt), ∃ (σ : Gt) (_ : σ ∈ Tt) (w : M.Group),
      ∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
        (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
        (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
      (∃ (n' : strictBNPair.N),
        strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
      g = σ * b₁ * n * b₂
  generalized_bruhat_disjoint :
    ∀ (σ₁ σ₂ : Gt) (_ : σ₁ ∈ Tt) (_ : σ₂ ∈ Tt) (w₁ w₂ : M.Group),
      (∃ g,
        (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
           (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
           (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
          (∃ (n' : strictBNPair.N), strictBNPair.π n' = w₁ ∧ (n' : Gt) = n) ∧
          g = σ₁ * b₁ * n * b₂) ∧
        (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
           (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
           (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
          (∃ (n' : strictBNPair.N), strictBNPair.π n' = w₂ ∧ (n' : Gt) = n) ∧
          g = σ₂ * b₁ * n * b₂)) →
      (∃ (t : Gt) (_ : t ∈ strictBNPair.T.map G.subtype), σ₁ = σ₂ * t) ∧ w₁ = w₂
  coset_mul_rule :
    ∀ (σ : Gt) (_ : σ ∈ Tt) (w : M.Group)
      (g : Gt),
      (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
         (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
         (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
        (∃ (n' : strictBNPair.N), strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
        g = σ * b₁ * n * b₂) ↔
      (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
         (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
         (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
        (∃ (n' : strictBNPair.N), strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
        g = b₁ * σ * n * b₂)
  coset_conj_rule :
    ∀ (σ : Gt) (_ : σ ∈ Tt) (w : M.Group)
      (g : Gt),
      (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
         (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
         (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
        (∃ (n' : strictBNPair.N), strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
        g = σ * b₁ * n * b₂) ↔
      (∃ (b₁ : Gt) (_ : b₁ ∈ strictBNPair.B.map G.subtype)
         (n : Gt) (_ : n ∈ strictBNPair.N.map G.subtype)
         (b₂ : Gt) (_ : b₂ ∈ strictBNPair.B.map G.subtype),
        (∃ (n' : strictBNPair.N) (nw : strictBNPair.N),
          strictBNPair.π nw = w ∧
          (n' : Gt) = n ∧
          (n' : Gt) = σ * (nw : Gt) * σ⁻¹) ∧
        g = b₁ * n * b₂ * σ)
  twist_group_finite :
    Finite (Tt ⧸ (Tt ⊓ G).subgroupOf Tt)

namespace GeneralizedBNPair




end GeneralizedBNPair
