/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Basic

open MvPolynomial

noncomputable section

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- Zariski-closed subset of `k^n` over an algebraically closed `k`: a set
cut out by the common vanishing of a (radical) ideal of polynomials
(cf. Thm 1.2 identifying closed sets with radical ideals). -/
def ZariskiClosed (S : Set (Fin n → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) k), S = {p | ∀ f ∈ I, MvPolynomial.eval p f = 0}

/-- Zariski topology on affine space (Cor 1, Lec 1): there exists a topology
on `k^n` whose closed sets are exactly the Zariski-closed subsets, exhibited
by checking the closure axioms for the family of vanishing loci. -/
theorem exists_zariskiTopology :
    ∃ τ : TopologicalSpace (Fin n → k),
      ∀ S : Set (Fin n → k), @IsClosed _ τ S ↔ ZariskiClosed k n S := by
  open Set in
  set T : Set (Set (Fin n → k)) := {S | ZariskiClosed k n S}

  have hempty : ∅ ∈ T := by
    show ZariskiClosed k n ∅
    refine ⟨⊤, ?_⟩
    ext p
    simp only [mem_empty_iff_false, mem_setOf_eq]
    exact ⟨False.elim, fun h =>
      one_ne_zero (by rw [← map_one (eval p)]; exact h 1 Submodule.mem_top)⟩

  have hsInter : ∀ A ⊆ T, ⋂₀ A ∈ T := by
    intro A hA
    show ZariskiClosed k n (⋂₀ A)
    choose I hI using fun S (hS : S ∈ A) => (hA hS : ZariskiClosed k n S)
    refine ⟨⨆ (S : A), I S.1 S.2, ?_⟩
    ext p
    simp only [mem_sInter, mem_setOf_eq]
    constructor
    · intro hp f hf
      have hker : (⨆ (S : A), I S.1 S.2) ≤ RingHom.ker (MvPolynomial.eval p) := by
        apply iSup_le
        intro ⟨S, hSA⟩ g hg
        have hpS := hp S hSA
        rw [hI S hSA] at hpS
        exact hpS g hg
      exact hker hf
    · intro hp S hSA
      rw [hI S hSA]
      intro f hfI
      exact hp f (le_iSup (fun (S : A) => I S.1 S.2) ⟨S, hSA⟩ hfI)

  have hunion : ∀ A ∈ T, ∀ B ∈ T, A ∪ B ∈ T := by
    intro A ⟨I, hI⟩ B ⟨J, hJ⟩
    show ZariskiClosed k n (A ∪ B)
    refine ⟨I * J, ?_⟩
    subst hI; subst hJ
    ext p
    simp only [mem_union, mem_setOf_eq]
    constructor
    · rintro (hpI | hpJ)
      · intro f hf
        have : I * J ≤ RingHom.ker (MvPolynomial.eval p) := by
          apply Ideal.mul_le.mpr
          intro a ha b _
          simp [RingHom.mem_ker, map_mul, hpI a ha]
        exact this hf
      · intro f hf
        have : I * J ≤ RingHom.ker (MvPolynomial.eval p) := by
          apply Ideal.mul_le.mpr
          intro a _ b hb
          simp [RingHom.mem_ker, map_mul, hpJ b hb]
        exact this hf
    · intro h
      by_contra hc
      simp only [not_or] at hc
      obtain ⟨hpI, hpJ⟩ := hc
      rw [not_forall] at hpI hpJ
      obtain ⟨f, hfI⟩ := hpI
      obtain ⟨g, hgJ⟩ := hpJ
      rw [Classical.not_imp] at hfI hgJ
      have heval := h (f * g) (Ideal.mul_mem_mul hfI.1 hgJ.1)
      rw [map_mul] at heval
      exact (mul_eq_zero.mp heval).elim hfI.2 hgJ.2

  refine ⟨TopologicalSpace.ofClosed T hempty hsInter hunion, ?_⟩
  intro S
  constructor
  · intro h
    have h2 := @IsClosed.isOpen_compl _ (TopologicalSpace.ofClosed T hempty hsInter hunion) S h
    have : (Sᶜ)ᶜ ∈ T := h2
    rwa [compl_compl] at this
  · intro h
    exact @IsClosed.mk _ (TopologicalSpace.ofClosed T hempty hsInter hunion) S
      (show (Sᶜ)ᶜ ∈ T from by rwa [compl_compl])

end
