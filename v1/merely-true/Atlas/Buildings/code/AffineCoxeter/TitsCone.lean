/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.Basic
import Mathlib.Data.Fintype.BigOperators

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **Coxeter wall** $H_s = \{\varphi : \varphi_s = 0\}$ associated to a simple reflection $s$. -/
def coxeterWall (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s = 0}

/-- The positive half-space $H_s^+ = \{\varphi : \varphi_s > 0\}$ cut out by the wall $H_s$. -/
def coxeterUpperHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s > 0}

/-- The negative half-space $H_s^- = \{\varphi : \varphi_s < 0\}$ cut out by the wall $H_s$. -/
def coxeterLowerHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s < 0}

/-- The **open fundamental chamber** $C = \bigcap_s H_s^+ = \{\varphi : \forall s, \varphi_s > 0\}$. -/
def titsFundamentalChamber (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s > 0}

/-- The **standard face** of type $I \subseteq B$: $F_I = \{\varphi : \varphi_s = 0 \text{ for } s \in I,
\ \varphi_s > 0 \text{ for } s \notin I\}$. -/
def titsFaceDual (_M : CoxeterMatrix B) (I : Finset B) : Set (B → ℝ) :=
  {φ | (∀ s ∈ I, φ s = 0) ∧ (∀ s, s ∉ I → φ s > 0)}

/-- The **contragredient action** of a simple reflection $s$ on coordinates:
$\sigma^*_s(x)_t = x_t - 2 x_s \cdot B(\alpha_s, \alpha_t)$. -/
noncomputable def dualSigma (M : CoxeterMatrix B) (s : B) (x : B → ℝ) : B → ℝ :=
  fun t => x t - 2 * x s * formVal M s t

/-- The **closed fundamental chamber** $\overline{C} = \{\varphi : \forall s, \varphi_s \ge 0\}$. -/
def titsFundamentalClosure (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s ≥ 0}

/-- The **Tits cone** $\mathcal U = W \cdot \overline{C}$: $W$-orbit of the closed fundamental
chamber under the contragredient action. -/
def titsConeSet (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {x | ∃ (y : B → ℝ), (∀ s, y s ≥ 0) ∧
    ∃ (ws : List B), x = ws.foldl (fun v s => dualSigma M s v) y}

/-- The dual reflection flips the $s$-coordinate: $\sigma^*_s(x)_s = -x_s$. -/
theorem dualSigma_on_s (M : CoxeterMatrix B) (s : B) (x : B → ℝ) :
    dualSigma M s x s = -x s := by
  simp only [dualSigma, formVal_diag]
  ring

/-- $\overline{C} \subseteq \mathcal U$: the closed fundamental chamber is in the Tits cone
(realized as the orbit of $\overline{C}$ under the empty word). -/
theorem titsFundamentalClosure_subset_titsCone (M : CoxeterMatrix B) :
    titsFundamentalClosure M ⊆ titsConeSet M := by
  intro x hx
  simp only [titsConeSet, Set.mem_setOf_eq, titsFundamentalClosure, Set.mem_setOf_eq] at *
  exact ⟨x, hx, [], rfl⟩

/-- The dual action is an involution: $\sigma^*_s \circ \sigma^*_s = \mathrm{id}$. -/
theorem dualSigma_involutive (M : CoxeterMatrix B) (s : B) (x : B → ℝ) :
    dualSigma M s (dualSigma M s x) = x := by
  ext t
  simp only [dualSigma, formVal_diag]
  ring

end TitsCone

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The Coxeter bilinear form vanishes at the origin: $B(0,0) = 0$. -/
theorem bilinForm_zero (M : CoxeterMatrix B) : bilinForm M 0 0 = 0 := by
  simp [bilinForm]

/-- A symmetric matrix $f$ is **indecomposable** iff no proper subset $\emptyset \ne I \subsetneq B$
is "block-diagonal": every such $I$ has a nonzero off-block entry $f_{ij} \ne 0$ with $i \in I$, $j \notin I$. -/
def FormIndecomposable (f : B → B → ℝ) : Prop :=
  ∀ (I : Finset B), I.Nonempty → I ≠ Finset.univ →
    ∃ i ∈ I, ∃ j, j ∉ I ∧ f i j ≠ 0

/-- Equivalent formulations of "affine Coxeter form": indecomposable + PSD + nondefinite is the
same as indecomposable + PSD + degenerate (existence of a nontrivial null vector). -/
theorem IsAffineCoxeterForm (M : CoxeterMatrix B) :
    (FormIndecomposable (fun s t => formVal M s t) ∧
     (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
     ¬((∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
       (∀ v : B → ℝ, bilinForm M v v = 0 → v = 0))) ↔
    (FormIndecomposable (fun s t => formVal M s t) ∧
     (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
     (∃ v : B → ℝ, v ≠ 0 ∧ bilinForm M v v = 0)) := by
  constructor
  · rintro ⟨hI, hPSD, hNotPD⟩
    refine ⟨hI, hPSD, ?_⟩
    push_neg at hNotPD
    obtain ⟨v, hv1, hv2⟩ := hNotPD hPSD
    exact ⟨v, hv2, le_antisymm (by linarith [hPSD v]) (hPSD v)⟩
  · rintro ⟨hI, hPSD, v, hv, hfv⟩
    refine ⟨hI, hPSD, ?_⟩
    rintro ⟨_, hPD⟩
    exact hv (hPD v hfv)

end CoxeterGroup

section PerronFrobenius

variable {B : Type*} [DecidableEq B] [Fintype B] [Nonempty B]


/-- The **Perron–Frobenius property** for an indecomposable PSD off-diagonal-nonpositive form:
the kernel is 1-dimensional and spanned by a strictly positive vector $v > 0$. -/
class PerronFrobeniusProperty {B : Type*} [Fintype B] (f : B → B → ℝ) : Prop where
  kernel_span :
    CoxeterGroup.FormIndecomposable f →
    (∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0) →
    (∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0) →
    (∀ s t, s ≠ t → f s t ≤ 0) →
    ∃ v : B → ℝ, (∀ s, v s > 0) ∧
      (∀ w : B → ℝ, (∑ s, ∑ t, w s * f s t * w t = 0) →
        ∃ c : ℝ, w = fun b => c * v b)

/-- Convenience accessor: under the Perron–Frobenius hypothesis, the kernel of a degenerate
indecomposable PSD off-diagonal-nonpositive form is 1-dimensional with strictly positive generator. -/
theorem perronFrobenius_kernel_dim_one
    (f : B → B → ℝ) [hPF : PerronFrobeniusProperty f]
    (hIndecomp : CoxeterGroup.FormIndecomposable f)
    (hPSD : ∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0)
    (hNotPD : ∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
    ∃ v : B → ℝ, (∀ s, v s > 0) ∧
      (∀ w : B → ℝ, (∑ s, ∑ t, w s * f s t * w t = 0) →
        ∃ c : ℝ, w = fun b => c * v b) :=
  hPF.kernel_span hIndecomp hPSD hNotPD hOffDiag

/-- Consequence: under PF hypothesis, any nonzero vector $w$ vanishing at a single index $b_0$
satisfies $Q_f(w) > 0$. This is the form-theoretic version of "any proper principal submatrix is PD". -/
theorem perronFrobenius_submatrix_pos_def
    (f : B → B → ℝ) [hPF : PerronFrobeniusProperty f]
    (hIndecomp : CoxeterGroup.FormIndecomposable f)
    (hPSD : ∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
    (b₀ : B) :
    ∀ w : B → ℝ, w b₀ = 0 → w ≠ 0 → ∑ s, ∑ t, w s * f s t * w t > 0 := by
  intro w hw hne

  by_contra hle
  simp only [not_lt] at hle

  have hpsd_w := hPSD w
  have hw_zero : ∑ s, ∑ t, w s * f s t * w t = 0 := le_antisymm hle hpsd_w

  by_cases hPD : ∀ v : B → ℝ, v ≠ 0 → ∑ s, ∑ t, v s * f s t * v t > 0
  ·
    exact absurd hw_zero (ne_of_gt (hPD w hne))
  ·
    simp only [not_forall, not_lt, exists_prop] at hPD
    obtain ⟨v₀, hv₀_ne, hv₀_le⟩ := hPD
    have hNotPD : ∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0 :=
      ⟨v₀, hv₀_ne, le_antisymm hv₀_le (hPSD v₀)⟩
    obtain ⟨v, hv_pos, hv_span⟩ := hPF.kernel_span hIndecomp hPSD hNotPD hOffDiag

    obtain ⟨c, hc⟩ := hv_span w hw_zero

    have hcv : w b₀ = c * v b₀ := congr_fun hc b₀
    rw [hw] at hcv
    have hc_zero : c = 0 := by
      rcases mul_eq_zero.mp hcv.symm with h | h
      · exact h
      · linarith [hv_pos b₀]

    have : w = 0 := by
      ext b; have := congr_fun hc b; simp [this, hc_zero]
    exact hne this

end PerronFrobenius

section Spherical

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Hypothesis class encoding the Coxeter classification theorem: a positive-definite Coxeter form
implies the underlying Coxeter group is **finite** (spherical type). Used as an axiom locally to
avoid invoking the full classification. -/
class SphericalFiniteProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  finite_of_pos_def :
    (∀ v : B → ℝ, v ≠ 0 → CoxeterGroup.bilinForm M v v > 0) → Finite (M.Group)

/-- Convenience accessor: positive-definite Coxeter form implies finite Coxeter group. -/
theorem spherical_implies_finite_group (M : CoxeterMatrix B)
    [hSF : SphericalFiniteProperty M]
    (h : ∀ v : B → ℝ, v ≠ 0 → CoxeterGroup.bilinForm M v v > 0) :
    Finite (M.Group) :=
  hSF.finite_of_pos_def h

end Spherical

section AffineProper

variable {B : Type*} [DecidableEq B] [Fintype B] [Nonempty B]

open CoxeterGroup

/-- Restriction of a Coxeter matrix $M$ to the parabolic subset $I \subseteq B$ of generators. -/
def CoxeterMatrix.restrict (M : CoxeterMatrix B) (I : Finset B) : CoxeterMatrix ↥I where
  M := fun ⟨i, _⟩ ⟨j, _⟩ => M i j
  isSymm := by ext ⟨i, _⟩ ⟨j, _⟩; simp [Matrix.transpose, M.symmetric]
  diagonal := by intro ⟨i, _⟩; simp
  off_diagonal := by
    intro ⟨i, _⟩ ⟨j, _⟩ h
    exact M.off_diagonal _ _ (fun heq => h (Subtype.ext heq))

/-- Extend a vector $v : I \to \mathbb R$ to all of $B \to \mathbb R$ by setting components outside $I$ to zero. -/
noncomputable def extendByZero (I : Finset B) (v : ↥I → ℝ) : B → ℝ :=
  fun b => if h : b ∈ I then v ⟨b, h⟩ else 0

/-- $\mathrm{extendByZero}(v)$ vanishes outside $I$. -/
theorem extendByZero_outside {I : Finset B} {b : B} (hb : b ∉ I) (v : ↥I → ℝ) :
    extendByZero I v b = 0 := dif_neg hb

/-- $\mathrm{extendByZero}$ is injective on nonzero vectors. -/
theorem extendByZero_ne_zero {I : Finset B} {v : ↥I → ℝ} (hv : v ≠ 0) :
    extendByZero I v ≠ 0 := by
  intro h
  apply hv
  ext ⟨b, hb⟩
  have := congr_fun h b
  simp only [extendByZero, dif_pos hb, Pi.zero_apply] at this
  exact this

/-- A sum over $B$ restricts to a sum over $I$ when the summand vanishes outside $I$. -/
lemma sum_restrict_of_vanish (I : Finset B) (f : B → ℝ) (hf : ∀ b, b ∉ I → f b = 0) :
    ∑ b : B, f b = ∑ b : ↥I, f b.1 := by
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (Finset.subset_univ I)
  intro x _ hxI; exact hf x hxI

/-- The restricted Coxeter form on $I$ agrees with the original form on the zero-extension:
$B_{M|_I}(v, v) = B_M(\bar v, \bar v)$ where $\bar v$ is $\mathrm{extendByZero}(v)$. -/
theorem bilinForm_restrict_eq_extend (M : CoxeterMatrix B) (I : Finset B)
    (v : ↥I → ℝ) :
    bilinForm (M.restrict I) v v =
    bilinForm M (extendByZero I v) (extendByZero I v) := by
  simp only [bilinForm, formVal, CoxeterMatrix.restrict]
  symm
  rw [sum_restrict_of_vanish I _ (by
    intro s hs
    simp only [extendByZero, dif_neg hs, zero_mul, Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro ⟨s, hs⟩ _
  rw [sum_restrict_of_vanish I _ (by
    intro t ht
    simp only [extendByZero, dif_neg ht, mul_zero])]
  apply Finset.sum_congr rfl
  intro ⟨t, ht⟩ _
  simp only [extendByZero, dif_pos hs, dif_pos ht]

/-- **Main corollary** of Perron–Frobenius for affine Coxeter forms: the form restricted to any
proper subset of generators $I \subsetneq B$ is **positive definite**. -/
theorem perronFrobenius_proper_subset_pos_def
    (M : CoxeterMatrix B)
    [hPF : PerronFrobeniusProperty (fun s t => formVal M s t)]
    (hIndecomp : FormIndecomposable (fun s t => formVal M s t))
    (hPSD : ∀ v : B → ℝ, bilinForm M v v ≥ 0)
    (hOffDiag : ∀ s t : B, s ≠ t → formVal M s t ≤ 0)
    (I : Finset B) (hI : I ≠ Finset.univ) :
    ∀ v : ↥I → ℝ, v ≠ 0 → bilinForm (M.restrict I) v v > 0 := by
  intro v hv

  have hb₀ : ∃ b₀ : B, b₀ ∉ I := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hI (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨b₀, hb₀⟩ := hb₀

  rw [bilinForm_restrict_eq_extend]

  have hvanish : extendByZero I v b₀ = 0 := extendByZero_outside hb₀ v

  have hne : extendByZero I v ≠ 0 := extendByZero_ne_zero hv

  exact perronFrobenius_submatrix_pos_def
    (fun s t => formVal M s t) hIndecomp hPSD hOffDiag b₀
    (extendByZero I v) hvanish hne

end AffineProper

namespace GeomRealization

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

/-- A point of the geometric realization: barycentric weights $\sum_v p_v = 1$, $p_v \ge 0$. -/
structure GeomRealizationPoint (V : Type*) [Fintype V] where
  wt : V → ℝ
  wt_nonneg : ∀ v, wt v ≥ 0
  wt_sum : ∑ v : V, wt v = 1

/-- $\ell^\infty$ distance between two geometric-realization points. -/
noncomputable def geomRealizationDist (p q : GeomRealizationPoint V) : ℝ :=
  Finset.univ.sup' ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    (fun v => |p.wt v - q.wt v|)

/-- The $\delta_v$-point: vertex $v$ embedded as a geometric realization point. -/
noncomputable def vertexPoint (v : V) : GeomRealizationPoint V where
  wt := fun w => if w = v then 1 else 0
  wt_nonneg := by
    intro w
    split_ifs <;> norm_num
  wt_sum := by
    simp [Finset.sum_ite_eq']

end GeomRealization
