/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false


/-- A compact (nonempty) Kähler manifold of complex dimension $n$, abstractly bundled with
its topology and the assumption of compactness. -/
structure CompactKahlerManifold (n : ℕ) where
  carrier : Type*
  topInst : TopologicalSpace carrier
  isCompact : @CompactSpace carrier topInst
  isNonempty : Nonempty carrier


/-- Hodge / bidegree decomposition data for a compact Kähler manifold:
$$b_k = \sum_{p+q=k} h^{p,q}, \qquad h^{p,q} = h^{q,p}, \qquad h^{p,q} = h^{n-q,\,n-p}.$$
The first identity is the Hodge decomposition, the second is complex conjugation
symmetry, and the third is Serre / Hodge $\star$ duality. -/
structure BidegreeDecomposition (n : ℕ) (_M : CompactKahlerManifold n) where
  hodge : ℕ → ℕ → ℕ
  betti : ℕ → ℕ
  hodge_decomposition : ∀ (k : ℕ),
    betti k = (Finset.range (k + 1)).sum (fun p => hodge p (k - p))
  conjugation_symmetry : ∀ p q, hodge p q = hodge q p
  star_symmetry : ∀ p q, hodge p q = hodge (n - q) (n - p)


/-- The "advanced Kähler property": $M$ carries some bidegree decomposition data. A marker
proposition asserting the existence of Hodge data on $M$. -/
def advanced_kahler_property (n : ℕ) (M : CompactKahlerManifold n) : Prop :=
  ∃ (_bd : BidegreeDecomposition n M), True


/-- **Odd Betti numbers of a compact Kähler manifold are even.** Using the Hodge
decomposition $b_k = \sum_{p+q=k} h^{p,q}$ and the conjugation symmetry $h^{p,q} = h^{q,p}$,
pairing $(p, k-p)$ with $(k-p, p)$ shows $b_{2j+1}$ is even. -/
theorem compact_kahler_odd_betti_even_mathlib
    {n : ℕ} {M : CompactKahlerManifold n}
    (bd : BidegreeDecomposition n M)
    (k : ℕ) (hk : k % 2 = 1) :
    ∃ (m : ℕ), bd.betti k = 2 * m := by
  rw [bd.hodge_decomposition k]
  set f := (fun p => bd.hodge p (k - p))
  have hf : ∀ p, p ≤ k → f p = f (k - p) := by
    intro p hp
    simp only [f]
    rw [bd.conjugation_symmetry p (k - p)]
    congr 1; omega
  have ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  subst hj
  have hlen : 2 * j + 1 + 1 = (j + 1) + (j + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  suffices h : (Finset.range (j + 1)).sum (fun x => f (j + 1 + x)) =
               (Finset.range (j + 1)).sum f by
    rw [h]; exact ⟨_, (two_mul _).symm⟩
  apply Finset.sum_bij' (fun a _ => j - a) (fun a _ => j - a)
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha
    simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hp : j + 1 + a ≤ 2 * j + 1 := by omega
    rw [hf (j + 1 + a) hp]
    congr 1; omega
