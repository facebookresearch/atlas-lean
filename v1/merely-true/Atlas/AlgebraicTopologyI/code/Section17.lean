/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.Section16
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup

noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The unit $n$-sphere $S^n \subset \mathbb{R}^{n+1}$, defined as the metric sphere of
radius $1$ in $\mathbb{R}^{n+1}$. -/
abbrev Sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The antipodal equivalence on $S^n$: $x \sim y$ iff $y = x$ or $y = -x$. The quotient by
this relation is real projective space $\mathbf{RP}^n$. -/
def antipodalSetoid (n : ℕ) : Setoid (Sphere n) where
  r x y := (x : EuclideanSpace ℝ (Fin (n + 1))) = y ∨
            (x : EuclideanSpace ℝ (Fin (n + 1))) = -↑y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun {_ y} h => h.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (by rw [h]; simp [neg_neg]))
    trans := fun {_ y _} hxy hyz => by
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (by rw [hxy]; exact hyz)
      · exact Or.inr (by rw [hxy, hyz])
      · exact Or.inl (by rw [hxy, hyz, neg_neg])
  }

/-- Real projective $n$-space $\mathbf{RP}^n = S^n / \{\pm 1\}$, the quotient of $S^n$ by the
antipodal action. -/
def RPn (n : ℕ) : Type :=
  Quotient (antipodalSetoid n)

/-- $\mathbf{RP}^n$ carries the quotient topology inherited from $S^n$. -/
instance (n : ℕ) : TopologicalSpace (RPn n) :=
  instTopologicalSpaceQuotient (s := antipodalSetoid n)

/-- **Proposition 17.1**. The integral singular homology of real projective $n$-space:
$H_0(\mathbf{RP}^n) = \mathbb{Z}$,
$H_n(\mathbf{RP}^n) = \mathbb{Z}$ if $n$ is odd,
$H_k(\mathbf{RP}^n) = \mathbb{Z}/2$ for odd $k$ with $0 < k < n$,
and zero otherwise. -/
def homologyGroup (n k : ℕ) : AddCommGrpCat :=
  if k = 0 then AddCommGrpCat.of ℤ
  else if k = n ∧ Odd n then AddCommGrpCat.of ℤ
  else if Odd k ∧ k < n then AddCommGrpCat.of (ZMod 2)
  else AddCommGrpCat.of PUnit

/-- The image subgroup of the cellular differential
$\partial_{k+1} : C_{k+1}(\mathbf{RP}^n) \to C_k(\mathbf{RP}^n) \cong \mathbb{Z}$:
all of $\mathbb{Z}$ when $k > n$, zero when $k = n$ or $k$ is even with $k < n$, and $2\mathbb{Z}$
when $k$ is odd with $k < n$. -/
def rpnImageSubgroup (n k : ℕ) : AddSubgroup ℤ :=
  if k > n then ⊤
  else if k = n then ⊥
  else if Odd k then AddSubgroup.zmultiples (2 : ℤ)
  else ⊥

/-- The cellular chain homology of $\mathbf{RP}^n$ in degree $k$, computed as
$\mathbb{Z} / \text{(image of }\partial_{k+1}\text{)}$. -/
def rpnChainHomology (n k : ℕ) : AddCommGrpCat :=
  if k > n then AddCommGrpCat.of PUnit
  else if k = 0 then AddCommGrpCat.of (ℤ ⧸ rpnImageSubgroup n 0)
  else if Odd k then AddCommGrpCat.of (ℤ ⧸ rpnImageSubgroup n k)
  else AddCommGrpCat.of PUnit

/-- In degree $0$, the image subgroup is trivial: $\partial_1 = 0$ on $C_0(\mathbf{RP}^n)$. -/
lemma rpnImageSubgroup_zero (n : ℕ) : rpnImageSubgroup n 0 = ⊥ := by
  unfold rpnImageSubgroup; simp [Nat.not_odd_zero]

/-- For odd $k$ with $k < n$, the image of $\partial_{k+1}$ is $2\mathbb{Z}$ (so $H_k = \mathbb{Z}/2$). -/
lemma rpnImageSubgroup_odd_lt {n k : ℕ} (hk : Odd k) (hkn : k < n) :
    rpnImageSubgroup n k = AddSubgroup.zmultiples (2 : ℤ) := by
  unfold rpnImageSubgroup
  simp [show ¬(k > n) from by omega, show k ≠ n from by omega, hk]

/-- In the top degree $k = n$, the image of $\partial_{n+1} = 0$ is trivial. -/
lemma rpnImageSubgroup_self (n : ℕ) : rpnImageSubgroup n n = ⊥ := by
  unfold rpnImageSubgroup; simp

/-- The chain-level homology of $\mathbf{RP}^n$ matches the explicit description in
`homologyGroup`. -/
def rpnChainHomology_iso_homologyGroup (n k : ℕ) :
    rpnChainHomology n k ≅ homologyGroup n k := by
  unfold rpnChainHomology homologyGroup
  by_cases hkn : n < k
  ·
    simp only [show k > n from hkn, ite_true]
    simp only [show k ≠ 0 from by omega, show ¬(k = n ∧ Odd n) from by omega,
      show ¬(Odd k ∧ k < n) from by omega, ite_false]
    exact Iso.refl _
  ·
    simp only [show ¬(k > n) from by omega, ite_false]
    by_cases hk0 : k = 0
    ·
      subst hk0; simp only [ite_true]; rw [rpnImageSubgroup_zero]
      exact AddEquiv.toAddCommGrpIso QuotientAddGroup.quotientBot
    · simp only [hk0, ite_false]
      by_cases hkodd : Odd k
      ·
        simp only [hkodd, ite_true]
        by_cases hkeqn : k = n
        ·
          subst hkeqn; simp only [true_and, hkodd, ite_true]
          rw [rpnImageSubgroup_self]
          exact AddEquiv.toAddCommGrpIso QuotientAddGroup.quotientBot
        ·
          have hklt : k < n := by omega
          simp only [show ¬(k = n) from hkeqn, false_and, ite_false, hklt, and_self, ite_true]
          rw [rpnImageSubgroup_odd_lt hkodd hklt]
          exact AddEquiv.toAddCommGrpIso (Int.quotientZMultiplesNatEquivZMod 2)
      ·
        simp only [hkodd, ite_false]
        simp only [show ¬(k = n ∧ Odd n) from fun ⟨h, ho⟩ => by subst h; exact hkodd ho,
          ite_false]
        exact Iso.refl _

/-- The antipodal map $x \mapsto -x$ on $S^n$. -/
def sphereNeg (n : ℕ) (x : Sphere n) : Sphere n :=
  ⟨-↑x, by
    have hx := x.2
    simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
    rw [norm_neg]; exact hx⟩

/-- Unfold the underlying vector of the antipodal map. -/
lemma sphereNeg_val (n : ℕ) (x : Sphere n) :
    (↑(sphereNeg n x) : EuclideanSpace ℝ (Fin (n + 1))) = -↑x := rfl

/-- The antipodal map on $S^n$ is an involution. -/
lemma sphereNeg_involutive (n : ℕ) : Function.Involutive (sphereNeg n) := by
  intro x; apply Subtype.ext; simp [sphereNeg_val, neg_neg]

/-- The antipodal map on $S^n$ is continuous. -/
lemma continuous_sphereNeg (n : ℕ) : Continuous (sphereNeg n) := by
  apply Continuous.subtype_mk
  exact continuous_neg.comp continuous_subtype_val

/-- The antipodal map as a self-homeomorphism of $S^n$. -/
def sphereNegHomeomorph (n : ℕ) : Sphere n ≃ₜ Sphere n :=
  Homeomorph.mk ((sphereNeg_involutive n).toPerm (sphereNeg n))
    (continuous_sphereNeg n)
    ((sphereNeg_involutive n).toPerm_symm ▸ continuous_sphereNeg n)

/-- The quotient map $S^n \to \mathbf{RP}^n$ is open: the saturation $U \cup (-U)$ of an
open set is open. -/
lemma isOpenMap_rpn_mk (n : ℕ) :
    IsOpenMap (Quotient.mk (antipodalSetoid n)) := by
  intro U hU
  rw [isOpen_coinduced]


  change IsOpen (Quotient.mk (antipodalSetoid n) ⁻¹'
      (Quotient.mk (antipodalSetoid n) '' U))

  suffices h : Quotient.mk (antipodalSetoid n) ⁻¹'
      (Quotient.mk (antipodalSetoid n) '' U) = U ∪ sphereNeg n '' U by
    rw [h]; exact hU.union ((sphereNegHomeomorph n).isOpenMap U hU)
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨y, hyU, hxy⟩
    have hrel := Quotient.exact hxy
    rcases hrel with h | h
    · left; rwa [← Subtype.ext h]
    · right; exact ⟨y, hyU, Subtype.ext (by simp [sphereNeg_val, h])⟩
  · rintro (hx | ⟨y, hyU, rfl⟩)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hyU, Quotient.sound (Or.inr (by simp [sphereNeg_val]))⟩

/-- Combining surjectivity, continuity, and openness: $S^n \to \mathbf{RP}^n$ is an open
quotient map. -/
lemma isOpenQuotientMap_rpn_mk (n : ℕ) :
    IsOpenQuotientMap (Quotient.mk (antipodalSetoid n)) :=
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_rpn_mk n⟩

/-- The antipodal equivalence relation on $S^n \times S^n$ is closed: $\{(x, y) : x = \pm y\}$
is a union of two closed graphs. -/
lemma isClosed_antipodal_rel (n : ℕ) :
    IsClosed {p : Sphere n × Sphere n |
      Quotient.mk (antipodalSetoid n) p.1 = Quotient.mk (antipodalSetoid n) p.2} := by

  suffices heq : {p : Sphere n × Sphere n |
      Quotient.mk (antipodalSetoid n) p.1 = Quotient.mk (antipodalSetoid n) p.2} =
    {p | (p.1 : EuclideanSpace ℝ (Fin (n + 1))) = p.2} ∪
    {p | (p.1 : EuclideanSpace ℝ (Fin (n + 1))) = -↑p.2} by
    rw [heq]
    exact (isClosed_eq (continuous_subtype_val.comp continuous_fst)
        (continuous_subtype_val.comp continuous_snd)).union
      (isClosed_eq (continuous_subtype_val.comp continuous_fst)
        (continuous_neg.comp (continuous_subtype_val.comp continuous_snd)))
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_union]
  rw [Quotient.eq]

  rfl

/-- $\mathbf{RP}^n$ is Hausdorff: the open quotient map by a closed equivalence relation
gives a Hausdorff quotient. -/
theorem rpn_t2Space (n : ℕ) : T2Space (RPn n) :=
  (t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_rpn_mk n)).mpr
    (isClosed_antipodal_rel n)

/-- Index type for the CW cells of $\mathbf{RP}^n$ in degree $k$: a single cell when
$k \le n$, none otherwise. -/
def RPnCell (n k : ℕ) : Type := if k ≤ n then PUnit else Empty

/-- Each $\mathbf{RP}^n$ cell-index type is finite. -/
instance RPnCell.finite (n k : ℕ) : Finite (RPnCell n k) := by
  simp only [RPnCell]; split <;> infer_instance

/-- Auxiliary vector in $\mathbb{R}^{n+1}$ used to define the $k$-cell characteristic map:
$x \in B^k$ (i.e.\ first $k$ coordinates) gets extended by $1 - \|x\|$ in the $k$th slot and
zeros afterwards. -/
def rpnRawVec (n k : ℕ) (_hk : k ≤ n) (x : Fin k → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i : Fin (n + 1) =>
    if h : (i : ℕ) < k then x ⟨i, h⟩
    else if (i : ℕ) = k then 1 - ‖x‖
    else 0)

/-- Component formula for `rpnRawVec`: the $i$th coordinate is $x_i$ for $i < k$, $1 - \|x\|$
for $i = k$, and $0$ for $i > k$. -/
lemma rpnRawVec_apply (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) (i : Fin (n + 1)) :
    (rpnRawVec n k hk x) i =
      if h : (i : ℕ) < k then x ⟨i, h⟩
      else if (i : ℕ) = k then 1 - ‖x‖
      else 0 := by
  simp [rpnRawVec, WithLp.equiv]

/-- The auxiliary vector `rpnRawVec` is never zero (so its normalisation is well-defined). -/
lemma rpnRawVec_ne_zero (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) :
    rpnRawVec n k hk x ≠ 0 := by
  intro h
  have hcomp : ∀ i : Fin (n+1), (rpnRawVec n k hk x) i = 0 := fun i => by
    have : rpnRawVec n k hk x = 0 := h
    simp [this]
  have hk_entry := hcomp ⟨k, by omega⟩
  rw [rpnRawVec_apply] at hk_entry
  simp at hk_entry

  have hnorm1 : ‖x‖ = 1 := by linarith
  by_cases hk0 : k = 0
  · subst hk0; simp [Pi.norm_def] at hnorm1
  · have hx_ne : x ≠ 0 := by intro hx0; simp [hx0] at hnorm1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx_ne
    have hi_comp := hcomp ⟨i.val, by omega⟩
    rw [rpnRawVec_apply] at hi_comp
    simp [show (i : ℕ) < k from i.isLt] at hi_comp
    exact hi hi_comp

/-- The forward characteristic map $B^k \to \mathbf{RP}^n$ of the $k$-cell: normalize the
auxiliary vector and project to $\mathbf{RP}^n$. -/
def rpnCharMapFwd (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) : RPn n :=
  let v := rpnRawVec n k hk x
  let hv := rpnRawVec_ne_zero n k hk x
  Quotient.mk (antipodalSetoid n)
    ⟨(‖v‖⁻¹ : ℝ) • v, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)⟩

/-- The inverse to the characteristic map on the open cell: extracts the first $k$ coordinates
of the representative, with a sign and normalisation depending on the $k$th coordinate. -/
def rpnCharMapInv (n k : ℕ) (hk : k ≤ n) (q : RPn n) : Fin k → ℝ :=
  Quotient.lift (fun p : Sphere n =>
    let pv := (p : EuclideanSpace ℝ (Fin (n + 1)))
    let pk := pv ⟨k, by omega⟩
    let firstK : Fin k → ℝ := fun i => pv ⟨i.val, by omega⟩
    let M := ‖firstK‖
    let denom := |pk| + M
    fun i : Fin k => pk.sign * pv ⟨i.val, by omega⟩ / denom
  ) (by
    intro a b hab
    have hab' : (a : EuclideanSpace ℝ (Fin (n + 1))) = b ∨
        (a : EuclideanSpace ℝ (Fin (n + 1))) = -↑b := by
      exact hab
    funext i
    rcases hab' with h | h
    ·
      have : (a : EuclideanSpace ℝ (Fin (n + 1))) = (b : EuclideanSpace ℝ (Fin (n + 1))) := h
      simp [this]
    ·

      have ha : (a : EuclideanSpace ℝ (Fin (n + 1))) = -↑b := h
      have hab_eq : a = sphereNeg n b := Subtype.ext (by simp [sphereNeg_val, ha])
      subst hab_eq
      simp [sphereNeg, Real.sign_neg, abs_neg]
      congr 1
      congr 1
      exact norm_neg _
  ) q

/-- The open $k$-cell in $\mathbf{RP}^n$: points representable by a sphere element whose
coordinates above index $k$ vanish and whose coordinate at index $k$ is nonzero. -/
def rpnOpenCell (n k : ℕ) (hk : k ≤ n) : Set (RPn n) :=
  {q : RPn n | ∃ p : Sphere n, Quotient.mk (antipodalSetoid n) p = q ∧
    (∀ j : Fin (n + 1), k < (j : ℕ) → (p : EuclideanSpace ℝ (Fin (n + 1))) j = 0) ∧
    (p : EuclideanSpace ℝ (Fin (n + 1))) ⟨k, by omega⟩ ≠ 0}





















end RealProjectiveSpace

end
