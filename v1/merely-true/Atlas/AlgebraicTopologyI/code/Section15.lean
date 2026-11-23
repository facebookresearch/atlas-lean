/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval

open Topology

/-- **Definition 15.1.** A subcomplex of a CW-complex $X$ is a closed subspace
$Y \subseteq X$ that inherits a CW-structure from $X$: for each $n$ there is a
subset $B_n$ of the $n$-cells $A_n$ such that $Y_n = Y \cap X_n$ is given a
CW-structure by the characteristic maps $\{g_\beta : \beta \in B_n\}$.

In this formalization a `CWSubcomplex X` is unfolded to Mathlib's
`Topology.CWComplex.Subcomplex (Set.univ : Set X)`. -/
abbrev CWSubcomplex (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Type _ :=
  Topology.CWComplex.Subcomplex (Set.univ : Set X)

namespace CWSubcomplex

variable {X : Type*} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- The indexing set of $n$-cells of the subcomplex `E`, viewed as a subset of
the indexing set of $n$-cells of the ambient CW-complex `X`. -/
abbrev cells (E : CWSubcomplex X) (n : ℕ) : Set (CWComplex.cells X n) :=
  E.I n

/-- A subcomplex of a CW-complex is a closed subspace. -/
theorem isClosed (E : CWSubcomplex X) : IsClosed (E : Set X) :=
  E.closed

/-- A subcomplex sits inside the ambient space; trivial inclusion into `Set.univ`. -/
theorem subset_univ (E : CWSubcomplex X) : (E : Set X) ⊆ Set.univ :=
  Set.subset_univ _

/-- A subcomplex `E` is *finite* if, with its induced CW-structure, it has only
finitely many cells in total. -/
def IsFinite [T2Space X] (E : CWSubcomplex X) : Prop :=
  haveI := E.instRelCWComplex
  Topology.RelCWComplex.Finite (E : Set X)

end CWSubcomplex



noncomputable section

open unitInterval

namespace SphereInfty

/-- The Hilbert space $\ell^2(\mathbb{N}, \mathbb{R})$ of square-summable
sequences of real numbers. This serves as the ambient space for the model of
$\mathbb{R}^{\infty}$ and $S^{\infty}$ used below. -/
abbrev l2 := ↥(lp (fun _ : ℕ => ℝ) 2)

/-- The subspace $\mathbb{R}^{\infty} \subseteq \ell^2$ consisting of sequences
with finite support, i.e. those that are nonzero in only finitely many
coordinates. This is the increasing union of all $\mathbb{R}^n$. -/
def RInfty : Set l2 :=
  {x : l2 | Set.Finite (Function.support (x : ℕ → ℝ))}

/-- The infinite sphere $S^{\infty} = \mathbb{R}^{\infty} \cap S(\ell^2, 1)$:
unit vectors in $\ell^2$ with finite support. Proposition 15.5 asserts this
space is contractible. -/
abbrev Sphere := ↥(RInfty ∩ Metric.sphere (0 : l2) 1)


/-- The sum of two finitely supported sequences in $\ell^2$ is again finitely
supported; closure of $\mathbb{R}^{\infty}$ under addition. -/
lemma RInfty.add_mem {x y : l2} (hx : x ∈ RInfty) (hy : y ∈ RInfty) :
    x + y ∈ RInfty :=
  (hx.union hy).subset (Function.support_add _ _)

/-- Scaling a finitely supported sequence by a scalar preserves finite support;
closure of $\mathbb{R}^{\infty}$ under scalar multiplication. -/
lemma RInfty.smul_mem (c : ℝ) {x : l2} (hx : x ∈ RInfty) :
    c • x ∈ RInfty := by
  apply Set.Finite.subset hx
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro hx_n; apply hn
  show (c • x : l2).1 n = 0; simp [hx_n]


/-- Every point of $S^{\infty}$ has $\ell^2$-norm equal to $1$. -/
lemma norm_eq_one (x : Sphere) : ‖(x.1 : l2)‖ = 1 := by
  have := x.2.2; rwa [Metric.mem_sphere, dist_zero_right] at this

/-- A point of $S^{\infty}$ has finite support, i.e. lies in $\mathbb{R}^{\infty}$. -/
lemma Sphere.mem_RInfty (x : Sphere) : (x.1 : l2) ∈ RInfty := x.2.1


/-- The shift operator on sequences sending $(x_0, x_1, x_2, \ldots)$ to
$(0, x_0, x_1, \ldots)$. Used to build a sequence-level model of the operator
$T : \ell^2 \to \ell^2$ that underlies the contraction of $S^{\infty}$. -/
def shiftRight (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => x n

/-- `shiftRight` preserves finite support; used to show $T$ maps
$\mathbb{R}^{\infty}$ into itself. -/
lemma finite_support_shiftRight {x : ℕ → ℝ} (hx : Set.Finite (Function.support x)) :
    Set.Finite (Function.support (shiftRight x)) := by
  apply Set.Finite.subset (hx.image (· + 1))
  intro n hn
  simp only [Function.mem_support] at hn
  cases n with
  | zero => simp [shiftRight] at hn
  | succ n =>
    simp only [Set.mem_image, Function.mem_support]
    exact ⟨n, by intro h; exact hn (by simp [shiftRight, h]), rfl⟩

/-- `shiftRight` preserves membership in $\ell^2$, since shifting does not
change the multiset of nonzero values. -/
lemma memℓp_shiftRight {x : ℕ → ℝ} (hx : Memℓp x 2) : Memℓp (shiftRight x) 2 := by
  unfold Memℓp at *
  simp only [two_ne_zero, ENNReal.ofNat_ne_top, ↓reduceIte] at *
  rw [← summable_nat_add_iff 1]; simp only [shiftRight]; exact hx

/-- The right-shift operator $T : \ell^2 \to \ell^2$, sending $(x_0, x_1, \ldots)$
to $(0, x_0, x_1, \ldots)$. It is a linear isometry of $\ell^2$ which is *not*
surjective; this defect drives the contraction of $S^{\infty}$. -/
def T (x : l2) : l2 := ⟨shiftRight x.1, memℓp_shiftRight x.2⟩

/-- The shift operator $T$ preserves $\ell^2$-norm: $\|T x\| = \|x\|$. -/
lemma T_norm (x : l2) : ‖T x‖ = ‖x‖ := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]; congr 1
  rw [(lp.memℓp (T x)).summable hp |>.tsum_eq_zero_add]
  simp only [T, shiftRight, norm_zero, Real.zero_rpow (ne_of_gt hp), zero_add]

/-- The shift operator $T$ is additive on subtractions: $T x - T y = T(x - y)$. -/
lemma T_sub (x y : l2) : T x - T y = T (x - y) := by
  ext n; show (shiftRight x.1 - shiftRight y.1) n = shiftRight (x.1 - y.1) n
  cases n with
  | zero => simp [shiftRight]
  | succ _ => rfl

/-- The shift operator $T : \ell^2 \to \ell^2$ is an isometry, combining
`T_sub` and `T_norm`. -/
lemma T_isometry : Isometry (T : l2 → l2) := by
  rw [isometry_iff_dist_eq]; intro x y
  rw [dist_eq_norm, dist_eq_norm, T_sub, T_norm]

/-- Continuity of the shift operator $T$, an immediate consequence of being an
isometry. -/
lemma continuous_T : Continuous (T : l2 → l2) := T_isometry.continuous

/-- `T` preserves $\mathbb{R}^{\infty}$: the shift of a finitely supported
sequence is finitely supported. -/
lemma T_mem_RInfty {x : l2} (hx : x ∈ RInfty) : T x ∈ RInfty :=
  finite_support_shiftRight hx

/-- The shift $T$ maps $S^{\infty}$ to itself: it preserves both finite support
and unit norm. -/
lemma T_mem_sphere_set (x : Sphere) :
    T x.1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 :=
  ⟨T_mem_RInfty x.mem_RInfty, by
    rw [Metric.mem_sphere, dist_zero_right, T_norm]; exact norm_eq_one x⟩

/-- The shift operator $T$ restricted to a continuous self-map of $S^{\infty}$. -/
def TOnSphere : C(Sphere, Sphere) where
  toFun x := ⟨T x.1, T_mem_sphere_set x⟩
  continuous_toFun := (continuous_T.comp continuous_subtype_val).subtype_mk _


/-- Coordinate-level key lemma: if $t > 0$ and the affine combination
$t \cdot x + (1 - t) \cdot \text{shiftRight}(x)$ vanishes identically, then
$x = 0$. Used to prove that the affine homotopy from $\text{id}$ to $T$ never
passes through $0$. -/
lemma shiftRight_affine_zero_imp {x : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (h : ∀ n, t * x n + (1 - t) * shiftRight x n = 0) : ∀ n, x n = 0 := by
  intro n; induction n with
  | zero =>
    have h0 := h 0; simp [shiftRight] at h0
    exact h0.resolve_left (ne_of_gt ht)
  | succ n ih =>
    have hn := h (n + 1); simp [shiftRight] at hn
    rw [ih, mul_zero, add_zero] at hn
    exact (mul_eq_zero.mp hn).resolve_left (ne_of_gt ht)

/-- For a unit vector $x$ and any $t \in [0, 1]$, the affine combination
$t \cdot x + (1 - t) \cdot T x$ is nonzero. This ensures the straight-line
homotopy from $T$ to the identity is well-defined after normalization. -/
lemma norm_affine_id_T_pos (x : l2) (hx : ‖x‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (_ : t ≤ 1) :
    0 < ‖t • x + (1 - t) • T x‖ := by
  rw [norm_pos_iff]; intro h
  by_cases ht : t = 0
  · subst ht; simp at h
    linarith [show ‖T x‖ = 0 from by rw [h, norm_zero], T_norm x]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hcoord : ∀ n, (x : ℕ → ℝ) n = 0 :=
      shiftRight_affine_zero_imp ht_pos (fun n => congr_fun (congr_arg Subtype.val h) n)
    have hx0 : x = 0 := by ext n; exact hcoord n
    rw [hx0, norm_zero] at hx; exact one_ne_zero hx.symm


/-- The standard first basis vector $e_1 = (1, 0, 0, \ldots) \in \ell^2$. This
will be the basepoint to which all of $S^{\infty}$ is contracted. -/
def e1 : l2 := lp.single 2 0 (1 : ℝ)

/-- The basis vector $e_1$ has unit norm. -/
lemma e1_norm : ‖e1‖ = 1 := by simp [e1, lp.norm_single]

/-- The basis vector $e_1$ has finite support, so lies in $\mathbb{R}^{\infty}$. -/
lemma e1_mem_RInfty : e1 ∈ RInfty := by
  apply Set.Finite.subset (Set.finite_singleton 0)
  intro n hn
  simp only [Function.mem_support, Set.mem_singleton_iff] at hn ⊢
  by_contra h; apply hn
  show (lp.single 2 0 (1 : ℝ) : ℕ → ℝ) n = 0
  simp [lp.single_apply, h]

/-- The basis vector $e_1$ lies in $S^{\infty}$, since it has unit norm and
finite support. -/
lemma e1_mem_sphere_set : e1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 :=
  ⟨e1_mem_RInfty, by rw [Metric.mem_sphere, dist_zero_right]; exact e1_norm⟩

/-- For a unit vector $x$ and any $t \in [0, 1]$, the affine combination
$t \cdot T x + (1 - t) \cdot e_1$ is nonzero. This ensures the straight-line
homotopy from the constant map $e_1$ to $T$ is well-defined after
normalization. -/
lemma norm_affine_T_e1_pos (x : l2) (hx : ‖x‖ = 1) (t : ℝ) (_ : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ‖t • T x + (1 - t) • e1‖ := by
  rw [norm_pos_iff]; intro h
  have h0 : (t • T x + (1 - t) • e1).1 0 = 0 := congr_fun (congr_arg Subtype.val h) 0
  have h0' : 1 - t = 0 := by
    have : (t • T x + (1 - t) • e1).1 0 = 1 - t := by
      show t * (T x).1 0 + (1 - t) * e1.1 0 = 1 - t
      simp [T, shiftRight, e1, lp.single]
    linarith
  have ht_eq : t = 1 := by linarith
  subst ht_eq; simp at h
  linarith [show ‖T x‖ = 0 from by rw [h, norm_zero], T_norm x]


/-- A continuous family of nonzero vectors can be continuously normalized to
unit vectors. -/
lemma continuous_normalize_comp {α : Type*} [TopologicalSpace α]
    (v : α → l2) (hv_cont : Continuous v) (hv_ne : ∀ x, v x ≠ 0) :
    Continuous (fun x => ‖v x‖⁻¹ • v x) :=
  (Continuous.inv₀ (continuous_norm.comp hv_cont)
    (fun x => norm_ne_zero_iff.mpr (hv_ne x))).smul hv_cont

/-- Normalizing a nonzero vector yields a unit vector, i.e. a point on the unit
sphere in $\ell^2$. -/
lemma norm_normalize (v : l2) (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ Metric.sphere (0 : l2) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)


/-- Given a nonzero finitely supported vector $v \in \mathbb{R}^{\infty}$, its
normalization $v / \|v\|$ as a point of $S^{\infty}$. -/
def normalizeToSphere (v : l2) (hv : v ≠ 0) (hR : v ∈ RInfty) : Sphere :=
  ⟨‖v‖⁻¹ • v, RInfty.smul_mem _ hR, norm_normalize v hv⟩


/-- The straight-line family in $\ell^2$ joining $T x$ to $x$: at time $t$, the
vector $t \cdot x + (1 - t) \cdot T x$. After normalization this gives the
homotopy from $T$ (at $t = 0$) to the identity (at $t = 1$) on $S^{\infty}$. -/
def v_id_T (p : I × Sphere) : l2 :=
  (p.1 : ℝ) • (p.2.1 : l2) + (1 - (p.1 : ℝ)) • T (p.2.1 : l2)

/-- The affine combination `v_id_T p` is finitely supported, since both
$x$ and $T x$ are. -/
lemma v_id_T_mem_RInfty (p : I × Sphere) : v_id_T p ∈ RInfty :=
  RInfty.add_mem (RInfty.smul_mem _ p.2.mem_RInfty)
    (RInfty.smul_mem _ (T_mem_RInfty p.2.mem_RInfty))

/-- The straight-line family `v_id_T` depends continuously on $(t, x)$. -/
lemma continuous_v_id_T : Continuous v_id_T := by
  unfold v_id_T
  exact ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_T.comp (continuous_subtype_val.comp continuous_snd)))

/-- The straight-line family `v_id_T` never vanishes, so normalization is
well-defined throughout. -/
lemma v_id_T_ne_zero (p : I × Sphere) : v_id_T p ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (norm_affine_id_T_pos _ (norm_eq_one p.2) _ p.1.2.1 p.1.2.2))


/-- The straight-line family in $\ell^2$ joining $e_1$ to $T x$: at time $t$,
the vector $t \cdot T x + (1 - t) \cdot e_1$. After normalization this gives
the homotopy from the constant map $e_1$ (at $t = 0$) to $T$ (at $t = 1$) on
$S^{\infty}$. -/
def v_T_e1 (p : I × Sphere) : l2 :=
  (p.1 : ℝ) • T (p.2.1 : l2) + (1 - (p.1 : ℝ)) • e1

/-- The straight-line family `v_T_e1` is finitely supported. -/
lemma v_T_e1_mem_RInfty (p : I × Sphere) : v_T_e1 p ∈ RInfty :=
  RInfty.add_mem (RInfty.smul_mem _ (T_mem_RInfty p.2.mem_RInfty))
    (RInfty.smul_mem _ e1_mem_RInfty)

/-- The straight-line family `v_T_e1` depends continuously on $(t, x)$. -/
lemma continuous_v_T_e1 : Continuous v_T_e1 := by
  unfold v_T_e1
  exact ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_T.comp (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const)

/-- The straight-line family `v_T_e1` never vanishes. -/
lemma v_T_e1_ne_zero (p : I × Sphere) : v_T_e1 p ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (norm_affine_T_e1_pos _ (norm_eq_one p.2) _ p.1.2.1 p.1.2.2))

/-- The constant continuous map from $S^{\infty}$ to itself sending every point
to the basepoint $e_1$. -/
def constE1 : C(Sphere, Sphere) :=
  ContinuousMap.const _ ⟨e1, e1_mem_sphere_set⟩


/-- A homotopy on $S^{\infty}$ from the shift map $T$ to the identity, obtained
by normalizing the straight-line family `v_id_T`. -/
def homotopy_T_to_id : ContinuousMap.Homotopy TOnSphere (ContinuousMap.id Sphere) where
  toFun p := normalizeToSphere (v_id_T p) (v_id_T_ne_zero p) (v_id_T_mem_RInfty p)
  continuous_toFun :=
    (continuous_normalize_comp v_id_T continuous_v_id_T v_id_T_ne_zero).subtype_mk _
  map_zero_left := by
    intro x; apply Subtype.ext
    simp only [v_id_T, Set.Icc.coe_zero, zero_smul, zero_add, sub_zero, one_smul,
      normalizeToSphere, TOnSphere, ContinuousMap.coe_mk]
    have hT : ‖T (x.1 : l2)‖ = 1 := by rw [T_norm]; exact norm_eq_one x
    simp [hT]
  map_one_left := by
    intro x; apply Subtype.ext
    simp only [v_id_T, Set.Icc.coe_one, one_smul, sub_self, zero_smul, add_zero,
      normalizeToSphere, ContinuousMap.id_apply]
    simp [norm_eq_one x]


/-- A homotopy on $S^{\infty}$ from the constant map at $e_1$ to the shift map
$T$, obtained by normalizing the straight-line family `v_T_e1`. -/
def homotopy_e1_to_T : ContinuousMap.Homotopy constE1 TOnSphere where
  toFun p := normalizeToSphere (v_T_e1 p) (v_T_e1_ne_zero p) (v_T_e1_mem_RInfty p)
  continuous_toFun :=
    (continuous_normalize_comp v_T_e1 continuous_v_T_e1 v_T_e1_ne_zero).subtype_mk _
  map_zero_left := by
    intro x; apply Subtype.ext
    simp only [v_T_e1, Set.Icc.coe_zero, zero_smul, zero_add, sub_zero, one_smul,
      normalizeToSphere, constE1, ContinuousMap.const_apply]
    simp [e1_norm]
  map_one_left := by
    intro x; apply Subtype.ext
    simp only [v_T_e1, Set.Icc.coe_one, one_smul, sub_self, zero_smul, add_zero,
      normalizeToSphere, TOnSphere, ContinuousMap.coe_mk]
    have hT : ‖T (x.1 : l2)‖ = 1 := by rw [T_norm]; exact norm_eq_one x
    simp [hT]


/-- **Proposition 15.5.** $S^{\infty}$ is contractible.

Proof: We compose the two homotopies $\text{const}_{e_1} \simeq T$ and
$T \simeq \text{id}$ to obtain $\text{const}_{e_1} \simeq \text{id}$, showing
the identity on $S^{\infty}$ is nullhomotopic. -/
instance contractibleSpace : ContractibleSpace Sphere := by
  rw [contractible_iff_id_nullhomotopic]
  have h1 : ContinuousMap.Homotopic TOnSphere (ContinuousMap.id Sphere) :=
    ⟨homotopy_T_to_id⟩
  have h2 : ContinuousMap.Homotopic constE1 TOnSphere :=
    ⟨homotopy_e1_to_T⟩
  exact ⟨⟨e1, e1_mem_sphere_set⟩, (h2.trans h1).symm⟩

end SphereInfty

end
