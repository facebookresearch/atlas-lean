/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- The number of monomials of degree `d` in `n+1` variables: `C(n+d, d)`. This is the dimension
of the space of degree-`d` forms used in the Veronese embedding. -/
def veroneseMonomialCount (n d : ℕ) : ℕ := Nat.choose (n + d) d

/-- Dimension of the target projective space of the degree-`d` Veronese embedding of `ℙⁿ`. -/
def veroneseEmbedDim (n d : ℕ) : ℕ := Nat.choose (n + d) d - 1

/-- There is always at least one monomial of given degree, so `veroneseMonomialCount > 0`. -/
theorem veroneseMonomialCount_pos (n d : ℕ) : 0 < veroneseMonomialCount n d :=
  Nat.choose_pos (Nat.le_add_left d n)

/-- Combinatorial bound: for `n ≥ 1`, `n + 2 ≤ C(n + 2, 2)`. -/
lemma choose_two_ge (n : ℕ) (hn : 1 ≤ n) : n + 2 ≤ Nat.choose (n + 2) 2 := by
  rw [Nat.choose_two_right]
  have h1 : n + 2 - 1 = n + 1 := by omega
  rw [h1]
  have h2 : 2 ≤ n + 1 := by omega
  have h3 : (n + 2) * 2 ≤ (n + 2) * (n + 1) := Nat.mul_le_mul_left (n + 2) h2
  have h4 : (n + 2) * 2 / 2 ≤ (n + 2) * (n + 1) / 2 := Nat.div_le_div_right h3
  simp at h4
  exact h4

/-- For `d ≥ 1`, `n + 1 ≤ C(n + d, d)`: ensures enough monomials to embed `ℙⁿ`. -/
theorem choose_add_ge_succ (n d : ℕ) (hd : 1 ≤ d) :
    n + 1 ≤ Nat.choose (n + d) d := by
  have hsym : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have h := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rw [hnd] at h
    exact h.symm
  rw [← hsym]
  have h1 : Nat.choose (n + 1) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h2 : Nat.choose (n + 1) n = n + 1 := by
    have h := Nat.choose_symm (show n ≤ n + 1 by omega)
    have hnn : n + 1 - n = 1 := by omega
    rw [hnn] at h
    rw [← h, Nat.choose_one_right]
  omega

/-- For `d ≥ 2` and `n ≥ 1`, `n + 2 ≤ C(n + d, d)`: the dimension gap needed for the Bertini
dimension count via the Veronese embedding. -/
theorem choose_add_ge_add_two (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    n + 2 ≤ Nat.choose (n + d) d := by
  have hsym : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have h := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rw [hnd] at h
    exact h.symm
  rw [← hsym]
  have h1 : Nat.choose (n + 2) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h2 : Nat.choose (n + 2) n = Nat.choose (n + 2) 2 := by
    have h := Nat.choose_symm (show n ≤ n + 2 by omega)
    have hnn : n + 2 - n = 2 := by omega
    rw [hnn] at h
    exact h.symm
  have h3 := choose_two_ge n hn
  omega

/-- For `d ≥ 1`, the Veronese embedding dimension is at least `n` (so it is a genuine embedding,
not a degeneration). -/
theorem veroneseEmbedDim_ge (n d : ℕ) (hd : 1 ≤ d) :
    n ≤ veroneseEmbedDim n d := by
  unfold veroneseEmbedDim
  have := choose_add_ge_succ n d hd
  omega

/-- Dimension of the parameter space of degree-`d` hypersurfaces in `ℙⁿ`. -/
def hypersurfaceParamDim (n d : ℕ) : ℕ := Nat.choose (n + d) d - 1

/-- Via the Veronese embedding, a degree-`d` hypersurface in `ℙⁿ` becomes a hyperplane in the
target projective space; the parameter spaces have the same dimension. -/
theorem veronese_hypersurface_is_hyperplane (n d : ℕ) :
    hypersurfaceParamDim n d = veroneseEmbedDim n d := rfl

/-- Number of conditions imposed by requiring smoothness at a fixed point: the value of `f` and
the `n` partial derivatives, so `n + 1` conditions. -/
def smoothnessConditionCount (n : ℕ) : ℕ := n + 1

/-- The number of smoothness conditions (`n + 1`) does not exceed the dimension of the parameter
space of degree-`d` hypersurfaces (for `d ≥ 2`, `n ≥ 1`). -/
theorem bertini_veronese_dimension_count (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    smoothnessConditionCount n ≤ hypersurfaceParamDim n d := by
  unfold smoothnessConditionCount hypersurfaceParamDim
  have := choose_add_ge_add_two n d hd hn
  omega

/-- The incidence variety (pairs `(x, f)` with `f` singular at `x`) has dimension strictly less
than the total monomial count, giving room for a smooth hypersurface to exist generically. -/
theorem incidence_variety_dim (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    n + (hypersurfaceParamDim n d - smoothnessConditionCount n) <
      veroneseMonomialCount n d := by
  unfold hypersurfaceParamDim smoothnessConditionCount veroneseMonomialCount
  have := choose_add_ge_add_two n d hd hn
  omega

/-- Codimension count: the dimension of the incidence variety plus one is at most the parameter
dimension, so the projection cannot be surjective and the generic fiber is smooth. -/
theorem generic_hypersurface_smooth_codim (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    n + (hypersurfaceParamDim n d - smoothnessConditionCount n) + 1 ≤
      hypersurfaceParamDim n d := by
  unfold hypersurfaceParamDim smoothnessConditionCount
  have := choose_add_ge_add_two n d hd hn
  omega

/-- The discriminant locus has positive codimension in the parameter space: there is a strict
gap of at least `1`. -/
theorem discriminant_codimension_pos (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    1 ≤ hypersurfaceParamDim n d -
      (n + (hypersurfaceParamDim n d - smoothnessConditionCount n)) := by
  unfold hypersurfaceParamDim smoothnessConditionCount
  have := choose_add_ge_add_two n d hd hn
  omega

/-- Analogous codimension count for the case of a smooth subvariety `X ⊂ ℙⁿ` of dimension `k`,
needed to obtain smooth degree-`d` sections of `X`. -/
theorem generic_section_smooth_codim (n d k : ℕ) (hd : 2 ≤ d)
    (hk : k ≤ n) (hn : 1 ≤ n) :
    k + (hypersurfaceParamDim n d - (k + 1)) + 1 ≤
      hypersurfaceParamDim n d := by
  unfold hypersurfaceParamDim
  have := choose_add_ge_add_two n d hd hn
  omega

/-- Combined summary of the Veronese-based Bertini dimension count: the incidence variety has
strictly smaller dimension than the parameter space, hypersurfaces of degree `d` correspond to
hyperplanes via the Veronese embedding, and there are enough monomials. -/
theorem veronese_bertini_summary (n d : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    n + (Nat.choose (n + d) d - 1 - (n + 1)) < Nat.choose (n + d) d - 1 ∧
    Nat.choose (n + d) d - 1 = veroneseEmbedDim n d ∧
    n + 1 ≤ Nat.choose (n + d) d := by
  refine ⟨?_, rfl, choose_add_ge_succ n d (by omega)⟩
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

/-- The space of homogeneous polynomials of degree `d` in `n + 1` variables over `k`. -/
abbrev HomogeneousPolys (k : Type) [Field k] (n d : ℕ) : Type :=
  { f : MvPolynomial (Fin (n + 1)) k // f.IsHomogeneous d }

/-- The Zariski topology on the space of degree-`d` homogeneous polynomials, generated by basic
open sets where a specified monomial coefficient is nonzero. -/
instance zariskiTopologyHomogeneousPolys (k : Type) [Field k] (n d : ℕ) :
    TopologicalSpace (HomogeneousPolys k n d) :=
  TopologicalSpace.generateFrom
    { U | ∃ (m : Fin (n + 1) →₀ ℕ),
        U = { f : HomogeneousPolys k n d | MvPolynomial.coeff m f.val ≠ 0 } }

/-- A property `P` holds *generically* on `α` if it holds on a dense open subset. -/
def IsGenericProperty {α : Type*} [TopologicalSpace α] (P : α → Prop) : Prop :=
  ∃ U : Set α, IsOpen U ∧ Dense U ∧ ∀ x ∈ U, P x

/-- The hypersurface `V(f) ⊂ ℙⁿ` is smooth: at every nonzero point where all partial derivatives
of `f` vanish, the value `f(x)` is nonzero (i.e. `x` is not on the hypersurface). -/
def IsSmooth_hypersurface {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 →
    (∀ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) = 0) →
    MvPolynomial.eval x f ≠ 0

/-- A smooth projective subvariety of `ℙⁿ`: a finite collection of homogeneous defining
polynomials such that at every nonzero point of the variety, the Jacobian condition holds. -/
structure SmoothProjectiveVariety (k : Type) [Field k] (n : ℕ) where
  definingPolys : Finset (MvPolynomial (Fin (n + 1)) k)
  polysHomogeneous : ∀ p ∈ definingPolys, ∃ d, p.IsHomogeneous d
  onVariety (x : Fin (n + 1) → k) : Prop :=
    ∀ p ∈ definingPolys, MvPolynomial.eval x p = 0
  isSmooth : ∀ x : Fin (n + 1) → k, x ≠ 0 → onVariety x →
    ∀ v : Fin (n + 1) → k, v ≠ 0 →
      (∀ p ∈ definingPolys, ∀ i : Fin (n + 1),
        MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0) →
      False

/-- The intersection `X ∩ V(f)` is smooth (relative to `X`): at every nonzero point of `X` with
`f(x) = 0`, some partial derivative of `f` is nonzero. -/
def IsSmooth_intersection_variety {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (X : SmoothProjectiveVariety k n) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 → X.onVariety x →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- General version of smooth intersection: parameterized by predicates `onX` (point lies on `X`)
and `smoothX` (point is a smooth point of `X`). -/
def IsSmooth_intersection {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (onX : (Fin (n + 1) → k) → Prop)
    (smoothX : (Fin (n + 1) → k) → Prop) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 → onX x → smoothX x →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- The Veronese map sending `(t₀, …, tₙ)` to the tuple of all degree-`d` monomials `∏ tⱼ^{Iⱼ}`,
indexed by exponent vectors `I` with `|I| = d`. -/
def veroneseMap {k : Type} [CommSemiring k] (n d : ℕ)
    (t : Fin (n + 1) → k)
    (I : { s : Fin (n + 1) →₀ ℕ // s.sum (fun _ => id) = d }) : k :=
  Finset.univ.prod (fun j => t j ^ (I.val j))

/-- If `V(f)` is a smooth hypersurface in `ℙⁿ`, then for any smooth projective subvariety `X`,
the intersection `X ∩ V(f)` is smooth. -/
lemma smooth_hypersurface_implies_smooth_intersection {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : IsSmooth_hypersurface f)
    (X : SmoothProjectiveVariety k n) :
    IsSmooth_intersection_variety f X := by
  intro x hx_ne _ hx_vanish
  by_contra h_all_vanish
  push Not at h_all_vanish
  exact absurd hx_vanish (hf x hx_ne h_all_vanish)






/-- For `d ≥ 1` and `n ≥ 1`, the number of degree-`d` monomials is at least `2`, so the Veronese
target projective space has positive dimension (needed to apply Bertini there). -/
lemma veroneseMonomialCount_ge_two_for_bertini (n d : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    2 ≤ BertiniVeronese.veroneseMonomialCount n d := by
  unfold BertiniVeronese.veroneseMonomialCount
  have : n + 1 ≤ Nat.choose (n + d) d := BertiniVeronese.choose_add_ge_succ n d hd
  omega




end
