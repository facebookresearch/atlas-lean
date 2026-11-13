/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsCone

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup

namespace PerronFrobeniusProof

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The quadratic form $Q_f(v) = \sum_{s,t} v_s f_{st} v_t$ associated to a real symmetric matrix $f$. -/
noncomputable def QF (f : B → B → ℝ) (v : B → ℝ) : ℝ :=
  ∑ s : B, ∑ t : B, v s * f s t * v t

/-- The bilinear form $B_f(v, w) = \sum_{s,t} v_s f_{st} w_t$ associated to a real symmetric matrix $f$. -/
noncomputable def BF (f : B → B → ℝ) (v w : B → ℝ) : ℝ :=
  ∑ s : B, ∑ t : B, v s * f s t * w t

/-- The quadratic form is the diagonal of the bilinear form: $Q_f(v) = B_f(v, v)$. -/
lemma QF_eq_BF (f : B → B → ℝ) (v : B → ℝ) : QF f v = BF f v v := rfl

/-- Bilinearity (left): $B_f(u + v, w) = B_f(u, w) + B_f(v, w)$. -/
lemma BF_add_left (f : B → B → ℝ) (u v w : B → ℝ) :
    BF f (fun b => u b + v b) w = BF f u w + BF f v w := by
  simp only [BF]; simp_rw [add_mul, Finset.sum_add_distrib]

/-- Bilinearity (right): $B_f(u, v + w) = B_f(u, v) + B_f(u, w)$. -/
lemma BF_add_right (f : B → B → ℝ) (u v w : B → ℝ) :
    BF f u (fun b => v b + w b) = BF f u v + BF f u w := by
  simp only [BF]; rw [← Finset.sum_add_distrib]
  congr 1; funext s; simp_rw [mul_add, ← Finset.sum_add_distrib]

/-- Scalar compatibility (left): $B_f(c \cdot v, w) = c \cdot B_f(v, w)$. -/
lemma BF_smul_left (f : B → B → ℝ) (c : ℝ) (v w : B → ℝ) :
    BF f (fun b => c * v b) w = c * BF f v w := by
  simp only [BF, Finset.mul_sum]; congr 1; funext s; congr 1; funext t; ring

/-- Scalar compatibility (right): $B_f(v, c \cdot w) = c \cdot B_f(v, w)$. -/
lemma BF_smul_right (f : B → B → ℝ) (c : ℝ) (v w : B → ℝ) :
    BF f v (fun b => c * w b) = c * BF f v w := by
  simp only [BF, Finset.mul_sum]; congr 1; funext s; congr 1; funext t; ring

/-- Polarization identity: $Q_f(v + cw) = Q_f(v) + c(B_f(v,w) + B_f(w,v)) + c^2 Q_f(w)$. -/
lemma QF_add_smul (f : B → B → ℝ) (v w : B → ℝ) (c : ℝ) :
    QF f (fun b => v b + c * w b) =
    QF f v + c * (BF f v w + BF f w v) + c ^ 2 * QF f w := by
  show BF f (fun b => v b + c * w b) (fun b => v b + c * w b) = _
  rw [BF_add_left, BF_add_right, BF_add_right, BF_smul_left, BF_smul_right,
      BF_smul_left, BF_smul_right]; simp only [QF_eq_BF]; ring

/-- Evaluation at a basis vector on the left: $B_f(e_i, v) = \sum_t f_{i,t} v_t = (f v)_i$. -/
lemma BF_left_single (f : B → B → ℝ) (v : B → ℝ) (i : B) :
    BF f (Pi.single i 1) v = ∑ t, f i t * v t := by
  simp only [BF, Pi.single_apply]
  have h1 : ∀ s : B, (∑ t : B, (if s = i then (1 : ℝ) else 0) * f s t * v t) =
    if s = i then (∑ t, f s t * v t) else 0 := by
    intro s; split_ifs with h
    · congr 1; funext t; ring
    · apply Finset.sum_eq_zero; intro t _; simp
  simp_rw [h1]; rw [Finset.sum_ite_eq']; simp

/-- Evaluation at a basis vector on the right: $B_f(v, e_i) = \sum_s v_s f_{s,i} = (v f)_i$. -/
lemma BF_right_single (f : B → B → ℝ) (v : B → ℝ) (i : B) :
    BF f v (Pi.single i 1) = ∑ s, v s * f s i := by
  simp only [BF, Pi.single_apply]
  congr 1; funext s
  have : ∀ t : B, v s * f s t * (if t = i then (1 : ℝ) else 0) =
    if t = i then v s * f s t else 0 := by intro t; split_ifs <;> ring
  simp_rw [this]; rw [Finset.sum_ite_eq']; simp

/-- Kernel orthogonality: if $Q_f(v) = 0$ and the form is PSD, then $B_f(v, w) + B_f(w, v) = 0$ for
all $w$. (This is essentially that $v$ is in the radical of the symmetrized form.) -/
lemma BF_sum_eq_zero (f : B → B → ℝ) (v : B → ℝ)
    (hPSD : ∀ u : B → ℝ, QF f u ≥ 0) (hQv : QF f v = 0) (w : B → ℝ) :
    BF f v w + BF f w v = 0 := by
  set L := BF f v w + BF f w v
  have hkey : ∀ c : ℝ, c * L + c ^ 2 * QF f w ≥ 0 := by
    intro c; have := hPSD (fun b => v b + c * w b)
    rw [QF_add_smul, hQv] at this; linarith
  by_contra hL
  by_cases hQw : QF f w = 0
  · have h1 := hkey 1; have h2 := hkey (-1)
    simp [hQw] at h1 h2
    exact hL (le_antisymm (by linarith) (by linarith))
  · have hQw_pos : QF f w > 0 := lt_of_le_of_ne (hPSD w) (Ne.symm hQw)
    have h := hkey (-L / (2 * QF f w))
    have hL2 : 0 < L ^ 2 := by positivity
    suffices hsuff : -L ^ 2 / (4 * QF f w) ≥ 0 by
      rcases (div_nonneg_iff (b := 4 * QF f w)).mp hsuff with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith [show 4 * QF f w > 0 from by positivity]
    suffices -L / (2 * QF f w) * L + (-L / (2 * QF f w)) ^ 2 * QF f w =
      -L ^ 2 / (4 * QF f w) by linarith
    field_simp; ring

/-- Row equation: orthogonality of $v$ to $e_i$ gives $\sum_t (f_{it} + f_{ti}) v_t = 0$ for each row $i$. -/
lemma combined_row_sum (f : B → B → ℝ) (v : B → ℝ) (i : B)
    (hBF_zero : ∀ w, BF f v w + BF f w v = 0) :
    ∑ t, (f i t + f t i) * v t = 0 := by
  have h := hBF_zero (Pi.single i 1)
  rw [BF_right_single, BF_left_single] at h
  convert h using 1
  rw [← Finset.sum_add_distrib]; congr 1; funext t; ring

/-- $|a| \cdot c \cdot |a| = a \cdot c \cdot a$ since $|a|^2 = a^2$. -/
lemma abs_sq_mul (a c : ℝ) : |a| * c * |a| = a * c * a := by
  have : |a| * |a| = a * a := abs_mul_abs_self a
  calc |a| * c * |a| = c * (|a| * |a|) := by ring
    _ = c * (a * a) := by rw [this]
    _ = a * c * a := by ring

/-- Sign-flip inequality: for $c \le 0$, $|a| \cdot c \cdot |b| \le a \cdot c \cdot b$ (note the
direction reversal from the Cauchy–Schwarz inequality $a b \le |a| |b|$ scaled by a negative). -/
lemma abs_mul_neg_le (a b c : ℝ) (hc : c ≤ 0) : |a| * c * |b| ≤ a * c * b := by
  have hab : a * b ≤ |a| * |b| := by
    calc a * b ≤ |a * b| := le_abs_self _
      _ = |a| * |b| := abs_mul a b
  nlinarith

/-- Absolute-value monotonicity: for a matrix with $f_{st} \le 0$ off-diagonal,
$Q_f(|v|) \le Q_f(v)$ (i.e. taking absolute values only decreases the quadratic form). -/
lemma QF_abs_le (f : B → B → ℝ) (v : B → ℝ)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
    QF f (fun b => |v b|) ≤ QF f v := by
  simp only [QF]
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro t _
  by_cases hst : s = t
  · subst hst; rw [abs_sq_mul]
  · exact abs_mul_neg_le _ _ _ (hOffDiag s t hst)

/-- A sum of nonpositive reals which equals zero must be termwise zero. -/
lemma sum_eq_zero_of_nonpos' {ι : Type*} {s : Finset ι} {g : ι → ℝ}
    (h_nonpos : ∀ i ∈ s, g i ≤ 0) (h_sum : ∑ i ∈ s, g i = 0) :
    ∀ i ∈ s, g i = 0 := by
  have h1 : ∀ i ∈ s, 0 ≤ -g i := fun i hi => by linarith [h_nonpos i hi]
  have h2 : ∑ i ∈ s, (-g i) = 0 := by rw [Finset.sum_neg_distrib]; linarith
  intro i hi; have := (Finset.sum_eq_zero_iff_of_nonneg h1).mp h2 i hi; linarith

/-- Zero-block lemma: if the row equation $\sum_t (f_{it} + f_{ti}) v_t = 0$ holds with $v \ge 0$,
$v_i = 0$, $v_j > 0$, and $f_{st} \le 0$ off-diagonal, then $f_{ij} = f_{ji} = 0$. -/
lemma offdiag_zero_from_row (f : B → B → ℝ) (v : B → ℝ) (i j : B)
    (hij : i ≠ j)
    (hv_nonneg : ∀ b, v b ≥ 0)
    (hvi : v i = 0)
    (hvj : v j > 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
    (hrow : ∑ t, (f i t + f t i) * v t = 0) :
    f i j = 0 ∧ f j i = 0 := by

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  have hi_term : (f i i + f i i) * v i = 0 := by rw [hvi]; ring
  rw [hi_term, zero_add] at hrow
  have h_nonpos : ∀ t ∈ Finset.univ.erase i, (f i t + f t i) * v t ≤ 0 := by
    intro t ht
    have ht' : t ≠ i := Finset.ne_of_mem_erase ht
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [hOffDiag i t (Ne.symm ht'), hOffDiag t i ht']
    · exact hv_nonneg t
  have h_each := sum_eq_zero_of_nonpos' h_nonpos hrow
  have hj_mem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hj_eq := h_each j hj_mem
  have hfij_sum : f i j + f j i = 0 := by
    rcases mul_eq_zero.mp hj_eq with h | h
    · exact h
    · linarith
  constructor
  · linarith [hOffDiag i j hij, hOffDiag j i hij.symm]
  · linarith [hOffDiag i j hij, hOffDiag j i hij.symm]

/-- **Perron–Frobenius positivity**: a nonnegative null vector $v \ge 0$, $Q_f(v) = 0$, $v \ne 0$ in
the kernel of an indecomposable PSD off-diagonal-nonpositive form $f$ must be **strictly positive**
component-wise. -/
lemma nonneg_kernel_pos (f : B → B → ℝ) (v : B → ℝ) [Nonempty B]
    (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
    (hQv : QF f v = 0)
    (hv_nonneg : ∀ b, v b ≥ 0)
    (hv_ne : v ≠ 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
    (hIndecomp : FormIndecomposable f) :
    ∀ b, v b > 0 := by
  have hBF := BF_sum_eq_zero f v hPSD hQv
  have hrow : ∀ i, ∑ t, (f i t + f t i) * v t = 0 :=
    fun i => combined_row_sum f v i hBF
  by_contra h_not_all_pos
  push_neg at h_not_all_pos
  obtain ⟨i₀, hi₀⟩ := h_not_all_pos
  have hvi₀ : v i₀ = 0 := le_antisymm hi₀ (hv_nonneg i₀)
  have hJ_ne : ∃ j₀, v j₀ > 0 := by
    by_contra h; push_neg at h
    have : v = 0 := funext (fun b => le_antisymm (h b) (hv_nonneg b))
    exact hv_ne this
  obtain ⟨j₀, hj₀⟩ := hJ_ne
  set I := Finset.univ.filter (fun b => v b = 0)
  have hI_ne : I.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi₀⟩⟩
  have hI_ne_univ : I ≠ Finset.univ := by
    intro h
    have := Finset.mem_filter.mp (h ▸ Finset.mem_univ j₀ : j₀ ∈ I)
    linarith [this.2]
  obtain ⟨i, hi_mem, j, hj_nmem, hfij⟩ := hIndecomp I hI_ne hI_ne_univ
  have hvi : v i = 0 := (Finset.mem_filter.mp hi_mem).2
  have hvj_pos : v j > 0 := by
    have : ¬ v j = 0 := by
      intro h; exact hj_nmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact lt_of_le_of_ne (hv_nonneg j) (Ne.symm (Ne.intro this))
  have hij : i ≠ j := by
    intro h; subst h; linarith [hvi]
  exact hfij (offdiag_zero_from_row f v i j hij hv_nonneg hvi hvj_pos hOffDiag (hrow i)).1

/-- **One-dimensional kernel** (positive case): any two strictly positive null vectors $v, w > 0$
of an indecomposable PSD off-diagonal-nonpositive form are scalar multiples: $w = c \cdot v$. -/
lemma positive_kernel_proportional (f : B → B → ℝ) (v w : B → ℝ) [Nonempty B]
    (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
    (hQv : QF f v = 0) (hQw : QF f w = 0)
    (hv_pos : ∀ b, v b > 0) (_hw_pos : ∀ b, w b > 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
    (hIndecomp : FormIndecomposable f) :
    ∃ c : ℝ, w = fun b => c * v b := by
  let b₀ := Classical.arbitrary B
  have hv_pos_b₀ : v b₀ > 0 := hv_pos b₀
  set c := w b₀ / v b₀
  use c
  set u := fun b => w b - c * v b with hu_def
  have hu_b₀ : u b₀ = 0 := by
    show w b₀ - w b₀ / v b₀ * v b₀ = 0
    field_simp; ring
  have hQu : QF f u = 0 := by
    have hBFwv := BF_sum_eq_zero f w hPSD hQw v
    have : QF f (fun b => w b + (-c) * v b) =
      QF f w + (-c) * (BF f w v + BF f v w) + (-c) ^ 2 * QF f v :=
      QF_add_smul f w v (-c)
    rw [hQw, hQv, hBFwv] at this
    show QF f (fun b => w b - c * v b) = 0
    have : QF f (fun b => w b + (-c) * v b) = 0 := by linarith
    convert this using 2
    funext b; ring
  have hQu_abs : QF f (fun b => |u b|) = 0 := by
    have h1 := QF_abs_le f u hOffDiag
    have h2 := hPSD (fun b => |u b|)
    linarith
  have hu_zero : u = fun _ => (0 : ℝ) := by
    by_contra hu_ne
    have hu_abs_ne : (fun b => |u b|) ≠ 0 := by
      intro h
      have : ∀ b, u b = 0 := fun b => abs_eq_zero.mp (congr_fun h b)
      exact hu_ne (funext this)
    have h_all_pos := nonneg_kernel_pos f (fun b => |u b|) hPSD hQu_abs
      (fun b => abs_nonneg _) hu_abs_ne hOffDiag hIndecomp b₀
    simp [hu_b₀] at h_all_pos
  funext b
  have := congr_fun hu_zero b
  simp only [hu_def] at this
  linarith

/-- **One-dimensional kernel** (general case): given a strictly positive null vector $v > 0$, any
other null vector $w$ is a scalar multiple of $v$: $w = c \cdot v$. -/
lemma kernel_scalar_multiple (f : B → B → ℝ) (v w : B → ℝ) [Nonempty B]
    (hPSD : ∀ u : B → ℝ, QF f u ≥ 0)
    (hv_pos : ∀ b, v b > 0)
    (hQv : QF f v = 0)
    (hQw : QF f w = 0)
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0)
    (hIndecomp : FormIndecomposable f) :
    ∃ c : ℝ, w = fun b => c * v b := by
  have hQw_abs : QF f (fun b => |w b|) = 0 := by
    have h1 := QF_abs_le f w hOffDiag
    have h2 := hPSD (fun b => |w b|)
    linarith
  by_cases hw_zero : w = fun _ => (0 : ℝ)
  · exact ⟨0, by simp [hw_zero]⟩
  · have hw_abs_ne : (fun b => |w b|) ≠ 0 := by
      intro h
      exact hw_zero (funext (fun b => abs_eq_zero.mp (congr_fun h b)))
    have hw_abs_pos := nonneg_kernel_pos f (fun b => |w b|) hPSD hQw_abs
      (fun b => abs_nonneg _) hw_abs_ne hOffDiag hIndecomp
    obtain ⟨c₁, hc₁⟩ := positive_kernel_proportional f v (fun b => |w b|)
      hPSD hQv hQw_abs hv_pos hw_abs_pos hOffDiag hIndecomp
    have hc₁_pos : c₁ > 0 := by
      have h1 := hw_abs_pos (Classical.arbitrary B)
      have h2 := hv_pos (Classical.arbitrary B)
      have h3 := congr_fun hc₁ (Classical.arbitrary B)
      simp at h3; nlinarith


    have hBF_wv := BF_sum_eq_zero f w hPSD hQw v
    have hQu₁ : QF f (fun b => w b - c₁ * v b) = 0 := by
      have step := QF_add_smul f w v (-c₁)
      rw [hQw, hQv, hBF_wv] at step
      have : QF f (fun b => w b + (-c₁) * v b) = 0 := by linarith
      convert this using 2; funext b; ring
    by_cases hw_eq : w = fun b => c₁ * v b
    · exact ⟨c₁, hw_eq⟩
    ·
      set u₁ := fun b => w b - c₁ * v b
      have hu₁_ne : u₁ ≠ fun _ => (0 : ℝ) := by
        intro h; exact hw_eq (funext fun b => by
          have := congr_fun h b; simp [u₁] at this; linarith)

      have hQu₁_abs : QF f (fun b => |u₁ b|) = 0 := by
        have h1 := QF_abs_le f u₁ hOffDiag; linarith [hPSD (fun b => |u₁ b|)]

      have hu₁_abs_ne : (fun b => |u₁ b|) ≠ 0 := by
        intro h; exact hu₁_ne (funext fun b => abs_eq_zero.mp (congr_fun h b))

      have h_u₁_pos := nonneg_kernel_pos f (fun b => |u₁ b|) hPSD hQu₁_abs
        (fun b => abs_nonneg _) hu₁_abs_ne hOffDiag hIndecomp


      by_cases hw_neg : w = fun b => -c₁ * v b
      · exact ⟨-c₁, hw_neg⟩
      ·
        have : ∃ b₀, w b₀ ≠ -c₁ * v b₀ := by
          by_contra h; push_neg at h
          exact hw_neg (funext h)
        obtain ⟨b₀, hb₀⟩ := this
        have habs_b₀ : |w b₀| = c₁ * v b₀ := congr_fun hc₁ b₀

        have hw_b₀ : w b₀ = c₁ * v b₀ := by
          rcases abs_cases (w b₀) with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h] at habs_b₀; exact habs_b₀
          · rw [h] at habs_b₀; exfalso; exact hb₀ (by linarith)
        have hu₁_b₀ : u₁ b₀ = 0 := by simp [u₁, hw_b₀, sub_self]
        have : |u₁ b₀| = 0 := by rw [hu₁_b₀, abs_zero]
        linarith [h_u₁_pos b₀]

/-- **Perron–Frobenius instance**: every off-diagonal-nonpositive real matrix on a nonempty index
type automatically satisfies the `PerronFrobeniusProperty`. -/
instance perronFrobeniusInstance (f : B → B → ℝ) [Nonempty B] :
    PerronFrobeniusProperty f where
  kernel_span := by
    intro hIndecomp hPSD hNotPD hOffDiag
    obtain ⟨v₀, hv₀_ne, hQv₀⟩ := hNotPD

    have hPSD' : ∀ u : B → ℝ, QF f u ≥ 0 := hPSD
    have hQv₀' : QF f v₀ = 0 := hQv₀

    have hQv₀_abs : QF f (fun b => |v₀ b|) = 0 := by
      have h1 := QF_abs_le f v₀ hOffDiag
      have h2 := hPSD' (fun b => |v₀ b|)
      linarith

    have hv₀_abs_ne : (fun b => |v₀ b|) ≠ 0 := by
      intro h
      have : ∀ b, v₀ b = 0 := fun b => abs_eq_zero.mp (congr_fun h b)
      exact hv₀_ne (funext this)

    have hv₀_abs_pos := nonneg_kernel_pos f (fun b => |v₀ b|) hPSD' hQv₀_abs
      (fun b => abs_nonneg _) hv₀_abs_ne hOffDiag hIndecomp

    refine ⟨fun b => |v₀ b|, hv₀_abs_pos, ?_⟩

    intro w hQw
    exact kernel_scalar_multiple f (fun b => |v₀ b|) w hPSD' hv₀_abs_pos hQv₀_abs hQw hOffDiag hIndecomp

end PerronFrobeniusProof
