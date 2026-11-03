/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsCoxeterProof
import Atlas.Buildings.code.CoxeterGroup.DeletionCondition
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Tactic.Group

open scoped Classical
open ChamberComplex
open Garrett.ExchangeDeletion
open AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]

/-- Each simple reflection $s_i$ in a Coxeter system is an involution, so $s_i^{-1} = s_i$. -/
lemma CoxeterSystem.simple_inv_eq {B : Type*} {M : CoxeterMatrix B}
    (cs : CoxeterSystem M M.Group) (i : B) :
    (cs.simple i)⁻¹ = cs.simple i :=
  mul_left_cancel (by rw [mul_inv_cancel, cs.simple_mul_simple_self])

/-- A bundle of data realising a chamber complex $\mathcal{C}$ as the Coxeter
complex of a Coxeter system $(W, S)$: chambers are indexed by $W$, the chamber
map intertwines adjacency with right multiplication by simple reflections, the
complex is thin, and the exchange condition together with a folding-from-half
axiom holds. -/
structure CoxeterComplexData (V : Type*) [DecidableEq V] where
  cc : ChamberComplex V
  B : Type*
  M : CoxeterMatrix B
  cs : CoxeterSystem M M.Group
  chamberOf : M.Group → Finset V
  chamberOf_injective : Function.Injective chamberOf
  chamberOf_surj : ∀ C, cc.toSimplicialComplex.IsMaximal C → ∃ w, chamberOf w = C
  chamberOf_maximal : ∀ w, cc.toSimplicialComplex.IsMaximal (chamberOf w)
  adj_of_mul_simple : ∀ w i,
    cc.toSimplicialComplex.Adjacent (chamberOf w) (chamberOf (w * cs.simple i))
  adj_implies_mul_simple : ∀ w C,
    cc.toSimplicialComplex.Adjacent (chamberOf w) C →
    ∃ i, C = chamberOf (w * cs.simple i)
  thin : cc.IsThin
  exchange : SatisfiesExchangeCondition M cs
  folding_from_chamber_map :
    ∀ (f₀ : M.Group → M.Group),
      (∀ w, f₀ (f₀ w) = f₀ w) →
      (∀ w i, chamberOf (f₀ (w * cs.simple i)) = chamberOf (f₀ w) ∨
              cc.toSimplicialComplex.Adjacent
                (chamberOf (f₀ w)) (chamberOf (f₀ (w * cs.simple i)))) →
      (∃ w, f₀ w ≠ w) →
      (∀ w, f₀ w = w → ∃! w', w' ≠ w ∧ f₀ w' = w) →
      ∃ f : Folding cc, ∀ w, (chamberOf w).image f.morph.toFun = chamberOf (f₀ w)

namespace CoxeterComplexData

variable (data : CoxeterComplexData V)

/-- The half-fold map $f_0^s : W \to W$ associated to a simple reflection $s$:
elements $w$ with $\ell(sw) = \ell(w) + 1$ are fixed (the positive half), and
elements with $\ell(sw) = \ell(w) - 1$ are sent to $sw$ (collapsing the
negative half onto the positive half). -/
noncomputable def chamberMapF₀ (s : data.B) (w : data.M.Group) : data.M.Group :=
  if data.cs.length (data.cs.simple s * w) = data.cs.length w + 1
  then w
  else data.cs.simple s * w

/-- $w$ lies in the positive half-space of the wall associated to $s$, i.e.
$\ell(sw) = \ell(w) + 1$. -/
def inPositiveHalf (s : data.B) (w : data.M.Group) : Prop :=
  data.cs.length (data.cs.simple s * w) = data.cs.length w + 1

/-- $w$ lies in the negative half-space of the wall associated to $s$, i.e.
$\ell(sw) + 1 = \ell(w)$. -/
def inNegativeHalf (s : data.B) (w : data.M.Group) : Prop :=
  data.cs.length (data.cs.simple s * w) + 1 = data.cs.length w

/-- Every group element is on exactly one side of the wall: either in the
positive or in the negative half. -/
lemma positive_or_negative (s : data.B) (w : data.M.Group) :
    data.inPositiveHalf s w ∨ data.inNegativeHalf s w := by
  unfold inPositiveHalf inNegativeHalf
  rcases data.cs.length_simple_mul w s with h | h <;> [left; right] <;> exact h

/-- The identity element lies in the positive half for every simple reflection $s$. -/
lemma one_in_positive (s : data.B) : data.inPositiveHalf s 1 := by
  unfold inPositiveHalf; simp [CoxeterSystem.length_one, CoxeterSystem.length_simple]

/-- The simple reflection $s$ itself lies in the negative half for $s$. -/
lemma simple_in_negative (s : data.B) :
    data.inNegativeHalf s (data.cs.simple s) := by
  unfold inNegativeHalf
  rw [CoxeterSystem.simple_mul_simple_self, CoxeterSystem.length_one,
      CoxeterSystem.length_simple]

/-- $f_0^s$ fixes positive-half elements. -/
lemma chamberMapF₀_pos {s : data.B} {w : data.M.Group}
    (hw : data.inPositiveHalf s w) : data.chamberMapF₀ s w = w := by
  unfold chamberMapF₀ inPositiveHalf at *; rw [if_pos hw]

/-- $f_0^s$ sends negative-half elements $w$ to $sw$. -/
lemma chamberMapF₀_neg {s : data.B} {w : data.M.Group}
    (hw : data.inNegativeHalf s w) : data.chamberMapF₀ s w = data.cs.simple s * w := by
  unfold chamberMapF₀ inNegativeHalf at *
  rw [if_neg (by omega)]

/-- Left multiplication by $s$ flips a positive-half element into the negative half. -/
lemma neg_of_mul_pos {s : data.B} {w : data.M.Group}
    (hw : data.inPositiveHalf s w) :
    data.inNegativeHalf s (data.cs.simple s * w) := by
  unfold inPositiveHalf inNegativeHalf at *
  rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega

/-- Left multiplication by $s$ flips a negative-half element into the positive half. -/
lemma pos_of_mul_neg {s : data.B} {w : data.M.Group}
    (hw : data.inNegativeHalf s w) :
    data.inPositiveHalf s (data.cs.simple s * w) := by
  unfold inPositiveHalf inNegativeHalf at *
  rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega

/-- The half-fold map $f_0^s$ is idempotent: $f_0^s \circ f_0^s = f_0^s$. -/
theorem chamberMapF₀_idempotent (s : data.B) (w : data.M.Group) :
    data.chamberMapF₀ s (data.chamberMapF₀ s w) = data.chamberMapF₀ s w := by
  rcases data.positive_or_negative s w with hp | hn
  · rw [data.chamberMapF₀_pos hp, data.chamberMapF₀_pos hp]
  · rw [data.chamberMapF₀_neg hn, data.chamberMapF₀_pos (data.pos_of_mul_neg hn)]

/-- $f_0^s$ fixes the identity. -/
lemma chamberMapF₀_one (s : data.B) : data.chamberMapF₀ s 1 = 1 :=
  data.chamberMapF₀_pos (data.one_in_positive s)

/-- $f_0^s$ folds the simple reflection $s$ onto the identity. -/
lemma chamberMapF₀_simple (s : data.B) :
    data.chamberMapF₀ s (data.cs.simple s) = 1 := by
  rw [data.chamberMapF₀_neg (data.simple_in_negative s),
      CoxeterSystem.simple_mul_simple_self]

/-- Every fixed point $w$ of the half-fold map has a unique preimage outside
itself, namely $sw$ — the map is exactly two-to-one onto the positive half. -/
theorem chamberMapF₀_two_to_one (s : data.B) (w : data.M.Group)
    (hw : data.chamberMapF₀ s w = w) :
    ∃! w', w' ≠ w ∧ data.chamberMapF₀ s w' = w := by
  have hp : data.inPositiveHalf s w := by
    rcases data.positive_or_negative s w with hp | hn
    · exact hp
    · rw [data.chamberMapF₀_neg hn] at hw
      exfalso; unfold inNegativeHalf at hn
      rw [hw] at hn; omega
  refine ⟨data.cs.simple s * w, ⟨?_, ?_⟩, ?_⟩
  · intro h; unfold inPositiveHalf at hp; rw [h] at hp; omega
  · rw [data.chamberMapF₀_neg (data.neg_of_mul_pos hp),
        ← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
  · intro w' ⟨hw'ne, hw'eq⟩
    rcases data.positive_or_negative s w' with hp' | hn'
    · rw [data.chamberMapF₀_pos hp'] at hw'eq; exact absurd hw'eq.symm (Ne.symm hw'ne)
    · rw [data.chamberMapF₀_neg hn'] at hw'eq
      calc w' = data.cs.simple s * (data.cs.simple s * w') := by
            rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
        _ = data.cs.simple s * w := by rw [hw'eq]

/-- A length-descending step $w \mapsto ws_t$ cannot simultaneously cross from
the positive half to the negative half. -/
lemma no_pos_neg_down (s : data.B) (w : data.M.Group) (t : data.B)
    (hp : data.inPositiveHalf s w)
    (hn : data.inNegativeHalf s (w * data.cs.simple t))
    (hdown : data.cs.length (w * data.cs.simple t) + 1 = data.cs.length w) :
    False := by
  unfold inPositiveHalf at hp; unfold inNegativeHalf at hn
  have hassoc : data.cs.simple s * (w * data.cs.simple t) =
    data.cs.simple s * w * data.cs.simple t := by group
  rw [hassoc] at hn
  rcases data.cs.length_mul_simple (data.cs.simple s * w * data.cs.simple t) t with h | h
  · rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one] at h; omega
  · rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one] at h; omega

/-- A length-ascending step $w \mapsto ws_t$ cannot simultaneously cross from
the negative half to the positive half. -/
lemma no_neg_pos_up (s : data.B) (w : data.M.Group) (t : data.B)
    (hn : data.inNegativeHalf s w)
    (hp : data.inPositiveHalf s (w * data.cs.simple t))
    (hup : data.cs.length (w * data.cs.simple t) = data.cs.length w + 1) :
    False := by
  unfold inNegativeHalf at hn; unfold inPositiveHalf at hp
  have hassoc : data.cs.simple s * (w * data.cs.simple t) =
    data.cs.simple s * w * data.cs.simple t := by group
  rw [hassoc] at hp
  rcases data.cs.length_mul_simple (data.cs.simple s * w) t with h | h
  · omega
  · omega

/-- Adjacent chambers $C_w$ and $C_{ws_t}$ are sent by the chamber map of
$f_0^s$ to chambers that are either equal or still adjacent — folds do not
tear adjacencies apart. -/
theorem chamberMapF₀_preserves_adj (s : data.B) (w : data.M.Group) (t : data.B) :
    data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t)) =
      data.chamberOf (data.chamberMapF₀ s w) ∨
    data.cc.toSimplicialComplex.Adjacent
      (data.chamberOf (data.chamberMapF₀ s w))
      (data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t))) := by
  rcases data.positive_or_negative s w with hp_w | hn_w <;>
  rcases data.positive_or_negative s (w * data.cs.simple t) with hp_wt | hn_wt <;>
  rcases data.cs.length_mul_simple w t with h_up | h_down
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_pos hp_wt]
    right; exact data.adj_of_mul_simple w t
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_pos hp_wt]
    right; exact data.adj_of_mul_simple w t
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_neg hn_wt]
    have hex := corollary_of_exchange data.cs data.exchange w s t hp_w h_up
    rcases hex with h_long | h_eq
    · unfold inNegativeHalf at hn_wt
      rw [show data.cs.simple s * (w * data.cs.simple t) =
        data.cs.simple s * w * data.cs.simple t from by group] at hn_wt
      omega
    · left; rw [show data.cs.simple s * (w * data.cs.simple t) =
        data.cs.simple s * w * data.cs.simple t from by group]
      exact congrArg data.chamberOf h_eq
  ·
    exact (data.no_pos_neg_down s w t hp_w hn_wt h_down).elim
  ·
    exact (data.no_neg_pos_up s w t hn_w hp_wt h_up).elim
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_pos hp_wt]
    unfold inNegativeHalf at hn_w; unfold inPositiveHalf at hp_wt
    have hassoc_swt : data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t := by group
    rw [hassoc_swt] at hp_wt
    have h_ssw : data.cs.length (data.cs.simple s * (data.cs.simple s * w)) =
      data.cs.length (data.cs.simple s * w) + 1 := by
      rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega
    have h_swt_up : data.cs.length (data.cs.simple s * w * data.cs.simple t) =
      data.cs.length (data.cs.simple s * w) + 1 := by omega
    have hex := corollary_of_exchange data.cs data.exchange (data.cs.simple s * w) s t
      h_ssw h_swt_up
    rcases hex with h_long | h_eq
    · simp at h_long; omega
    · simp at h_eq
      left; exact congrArg data.chamberOf h_eq
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_neg hn_wt]
    rw [show data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t from by group]
    right; exact data.adj_of_mul_simple (data.cs.simple s * w) t
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_neg hn_wt]
    rw [show data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t from by group]
    right; exact data.adj_of_mul_simple (data.cs.simple s * w) t

/-- Left multiplication by $w$ on $W$ preserves chamber adjacency: if $C_a$
and $C_b$ are adjacent, so are $C_{wa}$ and $C_{wb}$. -/
lemma left_mul_preserves_adj (w a b : data.M.Group)
    (hadj : data.cc.toSimplicialComplex.Adjacent (data.chamberOf a) (data.chamberOf b)) :
    data.cc.toSimplicialComplex.Adjacent
      (data.chamberOf (w * a)) (data.chamberOf (w * b)) := by
  obtain ⟨i, hi⟩ := data.adj_implies_mul_simple a (data.chamberOf b) hadj
  have hab : b = a * data.cs.simple i := data.chamberOf_injective hi
  rw [hab, show w * (a * data.cs.simple i) = w * a * data.cs.simple i from by group]
  exact data.adj_of_mul_simple (w * a) i

/-- The conjugate $u \mapsto w \cdot f_0^s(w^{-1}u)$ of the half-fold map by
left translation by $w$ — gives the folding that pairs the chambers $C_w$ and
$C_{ws}$. -/
noncomputable def conjugatedF₀ (w : data.M.Group) (s : data.B)
    (u : data.M.Group) : data.M.Group :=
  w * data.chamberMapF₀ s (w⁻¹ * u)

/-- The conjugated fold fixes the base chamber $C_w$. -/
lemma conjugatedF₀_fixes (w : data.M.Group) (s : data.B) :
    data.conjugatedF₀ w s w = w := by
  simp [conjugatedF₀, data.chamberMapF₀_one, mul_one]

/-- The conjugated fold sends the neighbour $C_{ws}$ across the wall back to $C_w$. -/
lemma conjugatedF₀_folds (w : data.M.Group) (s : data.B) :
    data.conjugatedF₀ w s (w * data.cs.simple s) = w := by
  simp [conjugatedF₀, inv_mul_cancel_left, data.chamberMapF₀_simple, mul_one]

/-- The conjugated fold is idempotent. -/
lemma conjugatedF₀_idempotent (w : data.M.Group) (s : data.B) (u : data.M.Group) :
    data.conjugatedF₀ w s (data.conjugatedF₀ w s u) =
    data.conjugatedF₀ w s u := by
  simp [conjugatedF₀, data.chamberMapF₀_idempotent]

/-- The conjugated fold is not the identity: it moves at least one element. -/
lemma conjugatedF₀_not_id (w : data.M.Group) (s : data.B) :
    ∃ u, data.conjugatedF₀ w s u ≠ u := by
  use w * data.cs.simple s
  rw [data.conjugatedF₀_folds]
  intro h
  have h1 := data.cs.length_simple s
  have : data.cs.simple s = (1 : data.M.Group) := by
    have := data.chamberOf_injective (congrArg data.chamberOf h)
    rwa [left_eq_mul] at this
  rw [this, CoxeterSystem.length_one] at h1; omega

/-- Each fixed point of the conjugated fold has a unique preimage outside
itself, namely $wsw^{-1}u$. -/
lemma conjugatedF₀_two_to_one (w : data.M.Group) (s : data.B)
    (u : data.M.Group) (hu : data.conjugatedF₀ w s u = u) :
    ∃! u', u' ≠ u ∧ data.conjugatedF₀ w s u' = u := by
  have hv : data.chamberMapF₀ s (w⁻¹ * u) = w⁻¹ * u := by
    have h1 := hu; unfold conjugatedF₀ at h1

    have h2 : w⁻¹ * (w * data.chamberMapF₀ s (w⁻¹ * u)) = w⁻¹ * u :=
      congrArg (w⁻¹ * ·) h1
    rwa [inv_mul_cancel_left] at h2
  obtain ⟨v', ⟨hv'ne, hv'eq⟩, hv'uniq⟩ :=
    data.chamberMapF₀_two_to_one s (w⁻¹ * u) hv
  refine ⟨w * v', ⟨?_, ?_⟩, ?_⟩
  · intro h; apply hv'ne
    have : w⁻¹ * (w * v') = w⁻¹ * (w * (w⁻¹ * u)) := by rw [h, mul_inv_cancel_left]
    rwa [inv_mul_cancel_left, inv_mul_cancel_left] at this
  · unfold conjugatedF₀
    simp only [inv_mul_cancel_left]
    rw [hv'eq, mul_inv_cancel_left]
  · intro u' ⟨hu'ne, hu'eq⟩
    have hv'' : w⁻¹ * u' ≠ w⁻¹ * u := by
      intro h; apply hu'ne
      have : w * (w⁻¹ * u') = w * (w⁻¹ * u) := congrArg (w * ·) h
      rwa [mul_inv_cancel_left, mul_inv_cancel_left] at this
    have hv''eq : data.chamberMapF₀ s (w⁻¹ * u') = w⁻¹ * u := by
      unfold conjugatedF₀ at hu'eq
      have h2 : w⁻¹ * (w * data.chamberMapF₀ s (w⁻¹ * u')) = w⁻¹ * u :=
        congrArg (w⁻¹ * ·) hu'eq
      rwa [inv_mul_cancel_left] at h2
    have := hv'uniq (w⁻¹ * u') ⟨hv'', hv''eq⟩
    calc u' = w * (w⁻¹ * u') := by rw [mul_inv_cancel_left]
      _ = w * v' := by rw [this]

/-- The chamber map of the conjugated fold preserves adjacency: adjacent
chambers $C_u, C_{us_t}$ go to chambers that are equal or still adjacent. -/
lemma conjugatedF₀_preserves_adj (w : data.M.Group) (s : data.B)
    (u : data.M.Group) (t : data.B) :
    data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t)) =
      data.chamberOf (data.conjugatedF₀ w s u) ∨
    data.cc.toSimplicialComplex.Adjacent
      (data.chamberOf (data.conjugatedF₀ w s u))
      (data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t))) := by
  unfold conjugatedF₀
  rw [show w⁻¹ * (u * data.cs.simple t) = w⁻¹ * u * data.cs.simple t from by group]
  rcases data.chamberMapF₀_preserves_adj s (w⁻¹ * u) t with heq | hadj
  · left
    have := data.chamberOf_injective heq
    show data.chamberOf (w * data.chamberMapF₀ s (w⁻¹ * u * data.cs.simple t)) =
         data.chamberOf (w * data.chamberMapF₀ s (w⁻¹ * u))
    rw [this]
  · right; exact data.left_mul_preserves_adj w _ _ hadj

end CoxeterComplexData
