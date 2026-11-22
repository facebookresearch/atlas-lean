/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Basic

namespace Lecture6


structure Circle where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius

def Circle.toSet (C : Circle) : Set ℂ :=
  Metric.sphere C.center C.radius

def Circle.Nonintersecting (A B : Circle) : Prop :=
  Disjoint A.toSet B.toSet

def Circle.Concentric (A B : Circle) : Prop :=
  A.center = B.center

inductive GeneralizedCircle
  | circle : Circle → GeneralizedCircle
  | line : ℝ → ℝ → ℝ → GeneralizedCircle

def GeneralizedCircle.toSet : GeneralizedCircle → Set ℂ
  | .circle C => C.toSet
  | .line a b c => {z : ℂ | a * z.re + b * z.im = c}

structure MoebiusTransformation where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

noncomputable def MoebiusTransformation.apply (T : MoebiusTransformation) (z : ℂ) : ℂ :=
  (T.a * z + T.b) / (T.c * z + T.d)

def MoebiusTransformation.MapsSetTo (T : MoebiusTransformation) (S₁ S₂ : Set ℂ) : Prop :=
  (∀ z ∈ S₁, T.c * z + T.d ≠ 0 → T.apply z ∈ S₂) ∧
  (∀ w ∈ S₂, ∃ z ∈ S₁, T.c * z + T.d ≠ 0 ∧ T.apply z = w)

def MoebiusTransformation.MapsCircle (T : MoebiusTransformation) (A B : Circle) : Prop :=
  T.MapsSetTo A.toSet B.toSet

def MoebiusTransformation.MapsGenCircle (T : MoebiusTransformation)
    (G₁ G₂ : GeneralizedCircle) : Prop :=
  T.MapsSetTo G₁.toSet G₂.toSet

noncomputable def MoebiusTransformation.comp (S T : MoebiusTransformation) :
    MoebiusTransformation where
  a := S.a * T.a + S.b * T.c
  b := S.a * T.b + S.b * T.d
  c := S.c * T.a + S.d * T.c
  d := S.c * T.b + S.d * T.d
  det_ne_zero := by
    have hS := S.det_ne_zero
    have hT := T.det_ne_zero
    have : (S.a * T.a + S.b * T.c) * (S.c * T.b + S.d * T.d) -
           (S.a * T.b + S.b * T.d) * (S.c * T.a + S.d * T.c) =
           (S.a * S.d - S.b * S.c) * (T.a * T.d - T.b * T.c) := by ring
    rw [this]
    exact mul_ne_zero hS hT


noncomputable def invTranslation (p : ℂ) : MoebiusTransformation where
  a := 0
  b := 1
  c := 1
  d := -p
  det_ne_zero := by
    simp only [zero_mul, one_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero

lemma circle_nonempty (C : Circle) : (C.toSet).Nonempty := by
  unfold Circle.toSet
  exact NormedSpace.sphere_nonempty.mpr (le_of_lt C.radius_pos)

lemma circle_exists_ne (C : Circle) (p : ℂ) :
    ∃ z ∈ C.toSet, z ≠ p := by
  by_contra h
  push Not at h
  have h1 : C.center + ↑C.radius ∈ C.toSet := by
    rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq]
    simp [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg C.radius_pos.le]
  have h2 : C.center - ↑C.radius ∈ C.toSet := by
    rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq,
      show C.center - ↑C.radius - C.center = -(↑C.radius : ℂ) from by ring,
      norm_neg, Complex.norm_real, Real.norm_of_nonneg C.radius_pos.le]
  have : C.center + ↑C.radius = C.center - ↑C.radius :=
    (h _ h1).trans (h _ h2).symm
  have h3 : (↑C.radius : ℂ) = -(↑C.radius : ℂ) := by
    have := congr_arg (· - C.center) this
    simp only [add_sub_cancel_left, sub_sub_cancel_left] at this
    exact this
  have : (C.radius : ℝ) = -C.radius := by
    have := congr_arg Complex.re h3
    simp at this
    exact this
  linarith [C.radius_pos]

lemma inv_circle_line_re (z p c₀ : ℂ)
    (hcirc : Complex.normSq (z - c₀) = Complex.normSq (p - c₀))
    (hne : z ≠ p) :
    ((p - c₀) / (z - p)).re = -1/2 := by
  have hzc : z - c₀ = (z - p) + (p - c₀) := by ring
  rw [hzc, Complex.normSq_add] at hcirc
  have hns : Complex.normSq (z - p) ≠ 0 := by simp [sub_ne_zero.mpr hne]
  have hmul_re : ((z - p) * starRingEnd ℂ (p - c₀)).re =
    (z - p).re * (p - c₀).re + (z - p).im * (p - c₀).im := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have hkey : Complex.normSq (z - p) +
    2 * ((z - p).re * (p - c₀).re + (z - p).im * (p - c₀).im) = 0 := by
    rw [← hmul_re]; linarith
  rw [Complex.div_re]; field_simp; linarith

lemma normSq_add_inv_of_re_eq (d w : ℂ) (hw : w ≠ 0)
    (hre : d.re * w.re - d.im * w.im = -1/2) :
    Complex.normSq (d + 1/w) = Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  rw [Complex.div_re, Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_sub, zero_div, add_zero]
  have hnsw : (Complex.normSq w : ℝ) ≠ 0 := by simp [hw]
  have hns_eq : Complex.normSq w = w.re * w.re + w.im * w.im := by
    simp [Complex.normSq_apply]
  field_simp
  nlinarith [hns_eq, sq_nonneg w.re, sq_nonneg w.im]

theorem invTranslation_maps_circle_through_pole_to_line
    (C : Circle) (p : ℂ) (hp : p ∈ C.toSet) :
    ∃ (L : GeneralizedCircle),
      (∃ a b c : ℝ, L = GeneralizedCircle.line a b c) ∧
      (invTranslation p).MapsGenCircle (.circle C) L := by
  set d := p - C.center with hd_def
  refine ⟨GeneralizedCircle.line d.re (-d.im) ((-1 : ℝ) / 2),
    ⟨d.re, -d.im, (-1 : ℝ) / 2, rfl⟩, ?_, ?_⟩
  ·
    intro z hz hdef
    change z ∈ C.toSet at hz
    simp only [GeneralizedCircle.toSet, Set.mem_setOf_eq, invTranslation, MoebiusTransformation.apply]
    simp only [invTranslation] at hdef
    have hzp : z - p ≠ 0 := by convert hdef using 1; ring
    have hne : z ≠ p := sub_ne_zero.mp hzp
    have hnormeq : Complex.normSq (z - C.center) = Complex.normSq (p - C.center) := by
      unfold Circle.toSet at hz hp
      rw [Metric.mem_sphere, Complex.dist_eq] at hz hp
      have h2 : ‖z - C.center‖ ^ 2 = ‖p - C.center‖ ^ 2 := by rw [hz, hp]
      rwa [Complex.sq_norm, Complex.sq_norm] at h2
    have hre := inv_circle_line_re z p C.center hnormeq hne
    have hw_eq : (0 * z + 1) / (1 * z + -p) = 1 / (z - p) := by ring
    rw [hw_eq]
    have h1 : d.re * (1 / (z - p)).re + (-d.im) * (1 / (z - p)).im =
      ((p - C.center) * (1 / (z - p))).re := by rw [Complex.mul_re]; ring
    have h2 : (p - C.center) * (1 / (z - p)) = (p - C.center) / (z - p) := by ring
    rw [h1, h2, hre]
  ·
    intro w hw
    simp only [GeneralizedCircle.toSet, Set.mem_setOf_eq] at hw
    have hline : d.re * w.re - d.im * w.im = -1/2 := by linarith
    have hw0 : w ≠ 0 := by intro h; subst h; simp at hw; linarith
    refine ⟨p + 1/w, ?_, ?_, ?_⟩
    ·
      change p + 1/w ∈ C.toSet
      unfold Circle.toSet
      rw [Metric.mem_sphere, Complex.dist_eq]
      have hpc : p + 1/w - C.center = d + 1/w := by rw [hd_def]; ring
      rw [hpc]
      have hns := normSq_add_inv_of_re_eq d w hw0 hline
      have hnorm_eq : ‖d + 1/w‖ = ‖d‖ := by
        nlinarith [Complex.sq_norm (d + 1/w), Complex.sq_norm d,
                   norm_nonneg (d + 1/w), norm_nonneg d,
                   sq_nonneg (‖d + 1/w‖ - ‖d‖)]
      rw [hnorm_eq]
      unfold Circle.toSet at hp
      rw [Metric.mem_sphere, Complex.dist_eq] at hp
      rw [hd_def]; exact hp
    ·
      simp only [invTranslation]
      show 1 * (p + 1/w) + -p ≠ 0
      have : 1 * (p + 1/w) + -p = 1/w := by ring
      rw [this]; exact div_ne_zero one_ne_zero hw0
    ·
      simp only [invTranslation, MoebiusTransformation.apply]
      field_simp; ring


lemma invTranslation_apply_eq (p z : ℂ) :
    (invTranslation p).apply z = 1 / (z - p) := by
  simp only [invTranslation, MoebiusTransformation.apply]; ring


lemma invTranslation_denom_eq (p z : ℂ) :
    (invTranslation p).c * z + (invTranslation p).d = z - p := by
  simp only [invTranslation]; ring


open Complex in
lemma key_normSq_fwd (w d : ℂ) (R : ℝ)
    (hcirc : normSq (w - d) = R ^ 2) :
    normSq ((↑(normSq d - R ^ 2) : ℂ) - w * starRingEnd ℂ d) = R ^ 2 * normSq w := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im,
             conj_re, conj_im, ofReal_re, ofReal_im] at *
  nlinarith [sq_nonneg w.re, sq_nonneg w.im, sq_nonneg d.re, sq_nonneg d.im, sq_nonneg R,
             sq_nonneg (w.re * d.re + w.im * d.im), sq_nonneg (w.re * d.im - w.im * d.re)]


open Complex in
lemma normSq_image_fwd {w d : ℂ} {R : ℝ}
    (hw : w ≠ 0) (hcirc : normSq (w - d) = R ^ 2) (hD : normSq d - R ^ 2 ≠ 0) :
    normSq (1 / w - starRingEnd ℂ d / (↑(normSq d - R ^ 2) : ℂ)) =
    R ^ 2 / (normSq d - R ^ 2) ^ 2 := by
  rw [one_div]
  have hDc : (↑(normSq d - R ^ 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  have : w⁻¹ - starRingEnd ℂ d / ↑(normSq d - R ^ 2) =
    (↑(normSq d - R ^ 2) - w * starRingEnd ℂ d) / (w * ↑(normSq d - R ^ 2)) := by
    field_simp
  rw [this, normSq_div, normSq_mul, normSq_ofReal, key_normSq_fwd w d R hcirc]
  have hnsq : normSq w ≠ 0 := by rwa [ne_eq, normSq_eq_zero]
  field_simp


open Complex in
lemma normSq_preimage_bwd {w d : ℂ} {R : ℝ}
    (hw : w ≠ 0) (hD : normSq d - R ^ 2 ≠ 0)
    (himg : normSq (w - starRingEnd ℂ d / ↑(normSq d - R ^ 2)) =
      R ^ 2 / (normSq d - R ^ 2) ^ 2) :
    normSq (1 / w - d) = R ^ 2 := by
  rw [show (1 : ℂ) / w - d = (1 - w * d) / w from by field_simp, normSq_div]
  have hDc : (↑(normSq d - R ^ 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
  have : w - starRingEnd ℂ d / ↑(normSq d - R ^ 2) =
    (w * ↑(normSq d - R ^ 2) - starRingEnd ℂ d) / ↑(normSq d - R ^ 2) := by field_simp
  rw [this, normSq_div, normSq_ofReal] at himg
  have hDsq : (normSq d - R ^ 2) * (normSq d - R ^ 2) ≠ 0 := mul_ne_zero hD hD
  rw [div_eq_div_iff hDsq (pow_ne_zero 2 hD)] at himg
  have hnsqw : normSq w ≠ 0 := by rwa [ne_eq, normSq_eq_zero]
  rw [div_eq_iff hnsqw]
  have himg' : normSq (w * ↑(normSq d - R ^ 2) - starRingEnd ℂ d) = R ^ 2 := by
    rw [sq (normSq d - R ^ 2)] at himg; exact mul_right_cancel₀ hDsq himg
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, one_re, one_im,
             conj_re, conj_im, ofReal_re, ofReal_im] at himg' ⊢
  set a := w.re; set b := w.im; set c := d.re; set e := d.im
  set D' := c * c + e * e - R ^ 2
  simp only [mul_zero, sub_zero] at himg'
  have hfact : D' * (D' * (a * a + b * b) - 2 * (a * c - b * e) + 1) = 0 := by
    nlinarith [sq_nonneg (a * D' - c), sq_nonneg (b * D' + e)]
  have key := (mul_eq_zero.mp hfact).resolve_left hD
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a * c), sq_nonneg (b * e),
             sq_nonneg (a * e), sq_nonneg (b * c)]


lemma norm_eq_of_normSq_eq (x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : Complex.normSq x = r ^ 2) : ‖x‖ = r :=
  (sq_eq_sq₀ (norm_nonneg x) hr).mp (by rw [Complex.sq_norm]; exact h)


lemma normSq_of_norm_eq (x : ℂ) (r : ℝ) (h : ‖x‖ = r) : Complex.normSq x = r ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, h]

theorem invTranslation_maps_circle_away_from_pole_to_circle
    (C : Circle) (p : ℂ) (hp : p ∉ C.toSet) :
    ∃ (B₁ : Circle), (invTranslation p).MapsCircle C B₁ := by
  set c₀ := C.center
  set R := C.radius
  set d₀ := c₀ - p
  set D := Complex.normSq d₀ - R ^ 2

  have hD_ne : D ≠ 0 := by
    intro hD0
    apply hp
    rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq]
    have hnd : ‖d₀‖ = R := norm_eq_of_normSq_eq _ _ (le_of_lt C.radius_pos) (by linarith)
    rw [show p - c₀ = -d₀ from by ring, norm_neg]
    exact hnd

  have hR' : 0 < R / |D| := div_pos C.radius_pos (abs_pos.mpr hD_ne)
  let B₁ : Circle := ⟨starRingEnd ℂ d₀ / ↑D, R / |D|, hR'⟩
  use B₁
  rw [MoebiusTransformation.MapsCircle, MoebiusTransformation.MapsSetTo]
  refine ⟨fun z hz => ?_, fun w hw => ?_⟩
  ·
    have hzc : ‖z - c₀‖ = R := by rwa [Circle.toSet, Metric.mem_sphere, Complex.dist_eq] at hz
    have hzp : z - p ≠ 0 := by
      intro h; apply hp; rw [sub_eq_zero] at h; rw [h] at hz; exact hz
    intro _hdef
    rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq, invTranslation_apply_eq]
    set w := z - p
    have hwd : w - d₀ = z - c₀ := by ring
    have hcirc : Complex.normSq (w - d₀) = R ^ 2 := by rw [hwd]; exact normSq_of_norm_eq _ _ hzc
    apply norm_eq_of_normSq_eq _ _ (le_of_lt hR')
    rw [normSq_image_fwd hzp hcirc hD_ne, div_pow, sq_abs]
  ·
    have hwc : ‖w - starRingEnd ℂ d₀ / ↑D‖ = R / |D| := by
      rwa [Circle.toSet, Metric.mem_sphere, Complex.dist_eq] at hw

    have hwne : w ≠ 0 := by
      intro hw0; rw [hw0, zero_sub, norm_neg, norm_div, Complex.norm_conj,
                      Complex.norm_real] at hwc
      have : ‖d₀‖ = R := (div_left_inj' (ne_of_gt (abs_pos.mpr hD_ne))).mp hwc
      apply hp
      rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq,
          show p - c₀ = -d₀ from by ring, norm_neg]
      exact this

    refine ⟨p + 1 / w, ?_, ?_, ?_⟩
    ·
      rw [Circle.toSet, Metric.mem_sphere, Complex.dist_eq,
          show p + 1 / w - c₀ = 1 / w - d₀ from by ring]
      apply norm_eq_of_normSq_eq _ _ (le_of_lt C.radius_pos)
      exact normSq_preimage_bwd hwne hD_ne (by rw [normSq_of_norm_eq _ _ hwc, div_pow, sq_abs])
    ·
      rw [invTranslation_denom_eq]; simp only [add_sub_cancel_left]
      exact div_ne_zero one_ne_zero hwne
    ·
      rw [invTranslation_apply_eq]; simp only [add_sub_cancel_left]; field_simp


lemma ipc_normSq_eq_line (u v a b α' β' : ℝ)
    (hline : α' * u + β' * v = -(a + b) * (α' ^ 2 + β' ^ 2) / 2) :
    (u + a * α') ^ 2 + (v + a * β') ^ 2 =
    (u + b * α') ^ 2 + (v + b * β') ^ 2 := by
  linear_combination 2 * (a - b) * hline

lemma ipc_normSq_ratio_circle (u v a b α' β' rsq : ℝ)
    (hcirc : u ^ 2 + v ^ 2 = rsq)
    (hab : a * b * (α' ^ 2 + β' ^ 2) = rsq) :
    b * ((u + a * α') ^ 2 + (v + a * β') ^ 2) =
    a * ((u + b * α') ^ 2 + (v + b * β') ^ 2) := by
  linear_combination (b - a) * hcirc - (b - a) * hab

lemma ipc_line_from_normSq_eq (u v a b α' β' : ℝ) (hab : a ≠ b)
    (h : (u + a * α') ^ 2 + (v + a * β') ^ 2 =
         (u + b * α') ^ 2 + (v + b * β') ^ 2) :
    α' * u + β' * v = -(a + b) * (α' ^ 2 + β' ^ 2) / 2 := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key : (a - b) * (2 * (α' * u + β' * v) + (a + b) * (α' ^ 2 + β' ^ 2)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp key with h1 | h1
  · exact absurd h1 hab'
  · linarith

lemma ipc_circle_normSq_identity (wr wi a b N2 rsq : ℝ)
    (hnsw : a = b * (wr ^ 2 + wi ^ 2))
    (hab : a * b * N2 = rsq) :
    ((b * wr - a) ^ 2 + (b * wi) ^ 2) * N2 =
    ((1 - wr) ^ 2 + wi ^ 2) * rsq := by
  subst hnsw; linear_combination (wr ^ 2 + wi ^ 2 - 2 * wr + 1) * hab

lemma ipc_disjoint_bound (α β γ : ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hN : 0 < α ^ 2 + β ^ 2)
    (hdisj : Disjoint {z : ℂ | α * z.re + β * z.im = γ} (Metric.sphere c r)) :
    (α * c.re + β * c.im - γ) ^ 2 > r ^ 2 * (α ^ 2 + β ^ 2) := by
  by_contra h; push_neg at h
  set N2 := α ^ 2 + β ^ 2; set D := α * c.re + β * c.im
  have hN2_ne : N2 ≠ 0 := ne_of_gt hN
  have harg : 0 ≤ (r ^ 2 * N2 - (D - γ) ^ 2) / N2 ^ 2 := by
    apply div_nonneg _ (sq_nonneg N2); linarith
  set t := Real.sqrt ((r ^ 2 * N2 - (D - γ) ^ 2) / N2 ^ 2)
  have ht_sq : t ^ 2 = (r ^ 2 * N2 - (D - γ) ^ 2) / N2 ^ 2 := Real.sq_sqrt harg
  set δ := (D - γ) / N2
  set z : ℂ := ⟨c.re - δ * α - t * β, c.im - δ * β + t * α⟩
  have hz_L : z ∈ {z : ℂ | α * z.re + β * z.im = γ} := by
    simp only [Set.mem_setOf_eq]
    show α * (c.re - δ * α - t * β) + β * (c.im - δ * β + t * α) = γ
    have : δ * N2 = D - γ := div_mul_cancel₀ (D - γ) hN2_ne
    linarith
  have hz_sphere : z ∈ Metric.sphere c r := by
    rw [Metric.mem_sphere, dist_eq_norm]
    have hzc_re : (z - c).re = -(δ * α + t * β) := by simp [z]; ring
    have hzc_im : (z - c).im = -(δ * β - t * α) := by simp [z]; ring
    have hns : ‖z - c‖ ^ 2 = r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hzc_re, hzc_im]
      have h1 : (-(δ * α + t * β)) * (-(δ * α + t * β)) +
        (-(δ * β - t * α)) * (-(δ * β - t * α)) = (δ ^ 2 + t ^ 2) * N2 := by
        rw [show N2 = α ^ 2 + β ^ 2 from rfl]; ring
      rw [h1, ht_sq]; have : δ = (D - γ) / N2 := rfl; rw [this]; field_simp; ring
    nlinarith [norm_nonneg (z - c), sq_nonneg (‖z - c‖ - r)]
  exact Set.disjoint_left.mp hdisj hz_L hz_sphere

lemma ipc_normSq_components (z c : ℂ) (t α' β' : ℝ) :
    Complex.normSq (z - (c - (↑t : ℂ) * ((↑α' : ℂ) + (↑β' : ℂ) * Complex.I))) =
    (z.re - c.re + t * α') * (z.re - c.re + t * α') +
    (z.im - c.im + t * β') * (z.im - c.im + t * β') := by
  rw [Complex.normSq_apply]
  have hre : (z - (c - (↑t : ℂ) * ((↑α' : ℂ) + (↑β' : ℂ) * Complex.I))).re =
    z.re - c.re + t * α' := by
    simp [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im]; ring
  have him : (z - (c - (↑t : ℂ) * ((↑α' : ℂ) + (↑β' : ℂ) * Complex.I))).im =
    z.im - c.im + t * β' := by
    simp [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im]; ring
  rw [hre, him]

lemma ipc_n_ne_zero (α β : ℝ) (hN : 0 < α ^ 2 + β ^ 2) :
    (↑α : ℂ) + (↑β : ℂ) * Complex.I ≠ 0 := by
  intro h
  have := Complex.normSq_eq_zero.mpr h
  rw [Complex.normSq_apply] at this
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] at this
  nlinarith

lemma ipc_normSq_n (α β : ℝ) :
    Complex.normSq ((↑α : ℂ) + (↑β : ℂ) * Complex.I) = α ^ 2 + β ^ 2 := by
  rw [Complex.normSq_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]; ring

set_option maxHeartbeats 800000 in
theorem inverse_points_maps_circle (α β γ : ℝ) (B₁ : Circle)
    (hN : 0 < α ^ 2 + β ^ 2)
    (hdisj : Disjoint {z : ℂ | α * z.re + β * z.im = γ} B₁.toSet) :
    ∃ (p₁ p₂ : ℂ) (ρ : ℝ),
      p₁ ≠ p₂ ∧ 0 < ρ ∧ ρ ≠ 1 ∧
      (∀ z : ℂ, α * z.re + β * z.im = γ →
        Complex.normSq (z - p₁) = Complex.normSq (z - p₂)) ∧
      (∀ w : ℂ, ‖w‖ = 1 → w ≠ 1 →
        ∃ z : ℂ, α * z.re + β * z.im = γ ∧ z ≠ p₂ ∧
          (z - p₁) / (z - p₂) = w) ∧
      (∀ z ∈ B₁.toSet, z ≠ p₂ →
        ‖(z - p₁) / (z - p₂)‖ = ρ) ∧
      (∀ w : ℂ, ‖w‖ = ρ → w ≠ 1 →
        ∃ z ∈ B₁.toSet, z ≠ p₂ ∧ (z - p₁) / (z - p₂) = w) := by

  set c := B₁.center; set r := B₁.radius; have hr : 0 < r := B₁.radius_pos
  set N2 := α ^ 2 + β ^ 2 with hN2_def
  set n : ℂ := (↑α : ℂ) + (↑β : ℂ) * Complex.I with hn_def
  have hN2_ne : N2 ≠ 0 := ne_of_gt hN
  have hn_ne : n ≠ 0 := ipc_n_ne_zero α β hN
  have hnsn : Complex.normSq n = N2 := ipc_normSq_n α β
  set D := α * c.re + β * c.im

  have hbound : (D - γ) ^ 2 > r ^ 2 * N2 := by
    show (α * c.re + β * c.im - γ) ^ 2 > r ^ 2 * N2
    exact ipc_disjoint_bound α β γ c r hr hN
      (show Disjoint {z : ℂ | α * z.re + β * z.im = γ} (Metric.sphere c r) from hdisj)
  set δ := (D - γ) / N2
  have hδN2 : δ * N2 = D - γ := div_mul_cancel₀ (D - γ) hN2_ne
  have hδ_sq_bound : δ ^ 2 > r ^ 2 / N2 := by
    rw [gt_iff_lt, div_lt_iff₀ hN]
    have hsq : δ ^ 2 * N2 = (D - γ) ^ 2 / N2 := by
      rw [eq_div_iff hN2_ne]
      have h2 : (δ * N2) ^ 2 = (D - γ) ^ 2 := by rw [hδN2]
      ring_nf at h2 ⊢; linarith
    rw [hsq]; rw [lt_div_iff₀ hN]; linarith
  have ht_arg : 0 < δ ^ 2 - r ^ 2 / N2 := by linarith
  set t := Real.sqrt (δ ^ 2 - r ^ 2 / N2)
  have ht_pos : 0 < t := Real.sqrt_pos_of_pos ht_arg
  have ht_sq : t ^ 2 = δ ^ 2 - r ^ 2 / N2 := Real.sq_sqrt (le_of_lt ht_arg)
  set a := δ - t; set b := δ + t
  have hab_ne : a ≠ b := by intro h; linarith
  have hab_sum : a + b = 2 * δ := by simp [a, b]; ring
  have hab_prod : a * b = r ^ 2 / N2 := by
    show (δ - t) * (δ + t) = r ^ 2 / N2
    have : (δ - t) * (δ + t) = δ ^ 2 - t ^ 2 := by ring
    rw [this, ht_sq]; ring
  have hab_prodN2 : a * b * N2 = r ^ 2 := by rw [hab_prod]; field_simp
  have hab_pos : 0 < a * b := by rw [hab_prod]; exact div_pos (sq_pos_of_pos hr) hN
  have hb_ne : b ≠ 0 := by intro h; rw [h, mul_zero] at hab_pos; exact lt_irrefl 0 hab_pos
  have ha_ne : a ≠ 0 := by intro h; rw [h, zero_mul] at hab_pos; exact lt_irrefl 0 hab_pos
  have hab_div_pos : 0 < a / b := by
    rcases (mul_pos_iff.mp hab_pos) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact div_pos ha hb
    · exact div_pos_of_neg_of_neg ha hb

  set p₁ := c - (↑a : ℂ) * n; set p₂ := c - (↑b : ℂ) * n
  set ρ := Real.sqrt (a / b)
  have hp_ne : p₁ ≠ p₂ := by
    intro heq
    have h1 : (↑a : ℂ) * n = (↑b : ℂ) * n := by
      exact sub_right_injective heq
    have h2 : (↑a : ℂ) = (↑b : ℂ) := mul_right_cancel₀ hn_ne h1
    exact hab_ne (by exact_mod_cast h2)
  have hp12_ne : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hp_ne
  refine ⟨p₁, p₂, ρ, hp_ne, Real.sqrt_pos_of_pos hab_div_pos, ?_, ?_, ?_, ?_, ?_⟩

  · intro h1
    have h2 : a / b = 1 := by
      have h_sq : ρ ^ 2 = a / b := Real.sq_sqrt (le_of_lt hab_div_pos)
      rw [h1] at h_sq; linarith
    exact hab_ne (by rwa [div_eq_iff hb_ne, one_mul] at h2)

  · intro z hz
    rw [ipc_normSq_components z c a α β, ipc_normSq_components z c b α β]
    have key : (z.re - c.re + a * α) ^ 2 + (z.im - c.im + a * β) ^ 2 =
               (z.re - c.re + b * α) ^ 2 + (z.im - c.im + b * β) ^ 2 := by
      apply ipc_normSq_eq_line; rw [hab_sum]; linarith [hz, hδN2]
    linarith [key]

  · intro w hw hw1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    set z := (p₁ - w * p₂) / ((1 : ℂ) - w)
    have hnsw : Complex.normSq w = 1 := by rw [← Complex.sq_norm, hw]; norm_num
    have hz1 : z - p₁ = w * (p₁ - p₂) / ((1 : ℂ) - w) := by
      simp only [z]; field_simp; ring
    have hz2 : z - p₂ = (p₁ - p₂) / ((1 : ℂ) - w) := by
      simp only [z]; field_simp; ring
    refine ⟨z, ?_, ?_, ?_⟩
    ·
      have hns_eq : Complex.normSq (z - p₁) = Complex.normSq (z - p₂) := by
        rw [hz1, hz2, map_div₀, map_div₀, Complex.normSq_mul, hnsw, one_mul]
      rw [ipc_normSq_components z c a α β, ipc_normSq_components z c b α β] at hns_eq
      have hns_sq : (z.re - c.re + a * α) ^ 2 + (z.im - c.im + a * β) ^ 2 =
                    (z.re - c.re + b * α) ^ 2 + (z.im - c.im + b * β) ^ 2 := by nlinarith
      have hline := ipc_line_from_normSq_eq _ _ a b α β hab_ne hns_sq
      rw [hab_sum] at hline; linarith [hδN2]
    ·
      intro heq; have : z - p₂ = 0 := sub_eq_zero.mpr heq; rw [hz2] at this
      rcases div_eq_zero_iff.mp this with h | h
      · exact hp12_ne h
      · exact h1w h
    ·
      rw [hz1, hz2, div_div_div_cancel_right₀ h1w, mul_div_cancel_right₀ w hp12_ne]

  · intro z hz hzp2
    have hzc : dist z c = r := by rwa [show B₁.toSet = Metric.sphere c r from rfl, Metric.mem_sphere] at hz
    rw [dist_eq_norm] at hzc
    have hzc_sq : Complex.normSq (z - c) = r ^ 2 := by
      rw [← Complex.sq_norm, hzc]
    set u := z.re - c.re; set v := z.im - c.im
    have hcirc : u ^ 2 + v ^ 2 = r ^ 2 := by
      have := Complex.normSq_apply (z - c)
      simp [Complex.sub_re, Complex.sub_im] at this
      nlinarith [this, hzc_sq]
    have hratio := ipc_normSq_ratio_circle u v a b α β (r ^ 2) hcirc hab_prodN2
    have hns1 := ipc_normSq_components z c a α β
    have hns2 := ipc_normSq_components z c b α β
    have hb_ns1_eq : b * Complex.normSq (z - p₁) = a * Complex.normSq (z - p₂) := by
      rw [hns1, hns2]; nlinarith [hratio]
    have hzp2' : z - p₂ ≠ 0 := sub_ne_zero.mpr hzp2
    rw [norm_div]
    have hns2_pos : 0 < Complex.normSq (z - p₂) := Complex.normSq_pos.mpr hzp2'
    have hns_ratio : Complex.normSq (z - p₁) / Complex.normSq (z - p₂) = a / b := by
      rw [div_eq_div_iff (ne_of_gt hns2_pos) hb_ne]; linarith
    have hnsq : (‖z - p₁‖ / ‖z - p₂‖) ^ 2 = a / b := by
      rw [div_pow, Complex.sq_norm, Complex.sq_norm]; exact hns_ratio
    have h_div_nn : 0 ≤ ‖z - p₁‖ / ‖z - p₂‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    rwa [← Real.sqrt_sq h_div_nn, Real.sqrt_inj (sq_nonneg _) (le_of_lt hab_div_pos)]

  · intro w hw hw1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    set z := (p₁ - w * p₂) / ((1 : ℂ) - w)

    have hnsw : Complex.normSq w = a / b := by
      rw [Complex.normSq_eq_norm_sq, hw]
      exact Real.sq_sqrt (le_of_lt hab_div_pos)

    have hnsw_ab : a = b * (w.re ^ 2 + w.im ^ 2) := by
      have hnsw2 : w.re * w.re + w.im * w.im = a / b := by
        have := Complex.normSq_apply w; rw [hnsw] at this; exact this.symm
      have : b * (w.re ^ 2 + w.im ^ 2) = a := by
        have : w.re ^ 2 + w.im ^ 2 = a / b := by nlinarith
        rw [this, mul_div_cancel₀ a hb_ne]
      linarith

    have hident := ipc_circle_normSq_identity w.re w.im a b N2 (r ^ 2) hnsw_ab hab_prodN2

    have hz1 : z - p₁ = w * (p₁ - p₂) / ((1 : ℂ) - w) := by
      simp only [z]; field_simp; ring
    have hz2 : z - p₂ = (p₁ - p₂) / ((1 : ℂ) - w) := by
      simp only [z]; field_simp; ring
    have hzc : z - c = (w * (↑b : ℂ) - (↑a : ℂ)) * n / ((1 : ℂ) - w) := by
      simp only [z]; field_simp; ring
    refine ⟨z, ?_, ?_, ?_⟩
    ·
      rw [show B₁.toSet = Metric.sphere c r from rfl, Metric.mem_sphere, dist_eq_norm]
      apply norm_eq_of_normSq_eq _ _ (le_of_lt hr)
      rw [hzc, map_div₀, Complex.normSq_mul, hnsn]

      have hns_wb : Complex.normSq (w * (↑b : ℂ) - (↑a : ℂ)) =
        (w.re * b - a) ^ 2 + (w.im * b) ^ 2 := by
        rw [Complex.normSq_apply]
        simp [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]; ring
      have hns_1w : Complex.normSq ((1 : ℂ) - w) = (1 - w.re) ^ 2 + w.im ^ 2 := by
        rw [Complex.normSq_apply]
        simp [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]; ring
      rw [hns_wb, hns_1w]
      have h1w_ns_pos : 0 < (1 - w.re) ^ 2 + w.im ^ 2 := by
        have := Complex.normSq_pos.mpr h1w; rw [hns_1w] at this; exact this
      rw [div_eq_iff (ne_of_gt h1w_ns_pos)]
      linear_combination hident
    ·
      intro heq; have : z - p₂ = 0 := sub_eq_zero.mpr heq; rw [hz2] at this
      rcases div_eq_zero_iff.mp this with h | h
      · exact hp12_ne h
      · exact h1w h
    ·
      rw [hz1, hz2, div_div_div_cancel_right₀ h1w, mul_div_cancel_right₀ w hp12_ne]

theorem line_nondeg_of_disjoint (α β γ : ℝ) (B₁ : Circle)
    (hne : Set.Nonempty {z : ℂ | α * z.re + β * z.im = γ})
    (hdisj : Disjoint {z : ℂ | α * z.re + β * z.im = γ} B₁.toSet) :
    0 < α ^ 2 + β ^ 2 := by
  by_contra h
  push Not at h
  have h0 : α ^ 2 + β ^ 2 = 0 := le_antisymm h (by positivity)
  have hα : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
  have hβ : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
  subst hα; subst hβ
  simp only [zero_mul, zero_add] at hne hdisj
  obtain ⟨z, hz⟩ := hne
  simp only [Set.mem_setOf_eq] at hz
  subst hz
  have huniv : {z : ℂ | (0 : ℝ) = 0} = Set.univ := by ext; simp
  rw [huniv] at hdisj
  have hcirc := circle_nonempty B₁
  rw [Set.disjoint_left] at hdisj
  obtain ⟨w, hw⟩ := hcirc
  exact hdisj (Set.mem_univ w) hw

theorem moebius_line_circle_to_concentric (L : GeneralizedCircle) (B₁ : Circle)
    (hL : ∃ a b c : ℝ, L = GeneralizedCircle.line a b c)
    (hLne : L.toSet.Nonempty)
    (hdisj : Disjoint L.toSet B₁.toSet) :
    ∃ (T₂ : MoebiusTransformation) (A₂ B₂ : Circle),

      (∀ z ∈ L.toSet, T₂.c * z + T₂.d ≠ 0 → T₂.apply z ∈ A₂.toSet) ∧

      (∀ w ∈ A₂.toSet, (T₂.c = 0 ∨ w ≠ T₂.a / T₂.c) →
        ∃ z ∈ L.toSet, T₂.c * z + T₂.d ≠ 0 ∧ T₂.apply z = w) ∧
      T₂.MapsCircle B₁ B₂ ∧
      A₂.Concentric B₂ ∧
      (T₂.c ≠ 0 → T₂.a / T₂.c ∈ A₂.toSet) := by

  obtain ⟨α, β, γ, hL_eq⟩ := hL
  subst hL_eq

  simp only [GeneralizedCircle.toSet] at hdisj hLne ⊢

  have hN : 0 < α ^ 2 + β ^ 2 := line_nondeg_of_disjoint α β γ B₁ hLne hdisj

  obtain ⟨p₁, p₂, ρ, hp_ne, hρ_pos, hρ_ne1, hL_normSq, hL_back,
    hB₁_fwd, hB₁_back⟩ :=
    inverse_points_maps_circle α β γ B₁ hN hdisj

  have hdet : (1 : ℂ) * (-p₂) - (-p₁) * 1 ≠ 0 := by
    have : (1 : ℂ) * (-p₂) - (-p₁) * 1 = p₁ - p₂ := by ring
    rw [this]; exact sub_ne_zero.mpr hp_ne

  refine ⟨⟨1, -p₁, 1, -p₂, hdet⟩, ⟨0, 1, one_pos⟩, ⟨0, ρ, hρ_pos⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz hdef
    simp only [Set.mem_setOf_eq] at hz
    have hzp₂ : z ≠ p₂ := by
      intro heq; apply hdef; show 1 * z + -p₂ = 0; rw [heq]; ring
    have heq_ns := hL_normSq z hz
    change (1 * z + -p₁) / (1 * z + -p₂) ∈ Metric.sphere 0 1
    rw [show (1 * z + -p₁) / (1 * z + -p₂) = (z - p₁) / (z - p₂) from by ring_nf,
        Metric.mem_sphere, dist_zero_right, norm_div]
    have hzp₂' : z - p₂ ≠ 0 := sub_ne_zero.mpr hzp₂
    have hnorm_eq : ‖z - p₁‖ = ‖z - p₂‖ := by
      nlinarith [Complex.sq_norm (z - p₁), Complex.sq_norm (z - p₂),
                 norm_nonneg (z - p₁), norm_nonneg (z - p₂),
                 sq_nonneg (‖z - p₁‖ - ‖z - p₂‖)]
    rw [hnorm_eq, div_self (norm_ne_zero_iff.mpr hzp₂')]
  ·
    intro w hw hfilter
    change dist w 0 = 1 at hw
    rw [dist_zero_right] at hw

    have hw1 : w ≠ 1 := by
      rcases hfilter with h | h
      · exact absurd (show (1 : ℂ) = 0 from h) one_ne_zero
      · have : (1 : ℂ) / 1 = 1 := div_self one_ne_zero
        rwa [show ((⟨1, -p₁, 1, -p₂, hdet⟩ : MoebiusTransformation).a /
          (⟨1, -p₁, 1, -p₂, hdet⟩ : MoebiusTransformation).c) = (1 : ℂ) / 1 from rfl,
          this] at h
    obtain ⟨z, hz_line, hz_ne_p₂, hz_eq⟩ := hL_back w hw hw1
    refine ⟨z, hz_line, ?_, ?_⟩
    · show 1 * z + -p₂ ≠ 0
      have : 1 * z + -p₂ = z - p₂ := by ring
      rw [this]; exact sub_ne_zero.mpr hz_ne_p₂
    · show (1 * z + -p₁) / (1 * z + -p₂) = w
      rw [show (1 * z + -p₁) / (1 * z + -p₂) = (z - p₁) / (z - p₂) from by ring_nf, hz_eq]
  ·
    refine ⟨?_, ?_⟩
    ·
      intro z hz hdef
      have hzp₂ : z ≠ p₂ := by
        intro heq; apply hdef; show 1 * z + -p₂ = 0; rw [heq]; ring
      have hρ_eq := hB₁_fwd z hz hzp₂
      change (1 * z + -p₁) / (1 * z + -p₂) ∈ Metric.sphere 0 ρ
      rw [show (1 * z + -p₁) / (1 * z + -p₂) = (z - p₁) / (z - p₂) from by ring_nf,
          Metric.mem_sphere, dist_zero_right, hρ_eq]
    ·
      intro w hw
      change dist w 0 = ρ at hw
      rw [dist_zero_right] at hw
      have hw1 : w ≠ 1 := by
        intro heq; subst heq; norm_num at hw; exact hρ_ne1 hw.symm
      obtain ⟨z, hz_B₁, hz_ne_p₂, hz_eq⟩ := hB₁_back w hw hw1
      refine ⟨z, hz_B₁, ?_, ?_⟩
      · show 1 * z + -p₂ ≠ 0
        have : 1 * z + -p₂ = z - p₂ := by ring
        rw [this]; exact sub_ne_zero.mpr hz_ne_p₂
      · show (1 * z + -p₁) / (1 * z + -p₂) = w
        rw [show (1 * z + -p₁) / (1 * z + -p₂) = (z - p₁) / (z - p₂) from by ring_nf, hz_eq]
  ·
    rfl
  ·
    intro _
    change dist ((1 : ℂ) / 1) 0 = 1
    rw [dist_zero_right, div_self (one_ne_zero), norm_one]

lemma comp_denom_factor (T₁ T₂ : MoebiusTransformation) (z : ℂ)
    (hdef : T₁.c * z + T₁.d ≠ 0) :
    (T₂.comp T₁).c * z + (T₂.comp T₁).d =
      (T₂.c * T₁.apply z + T₂.d) * (T₁.c * z + T₁.d) := by
  simp only [MoebiusTransformation.comp, MoebiusTransformation.apply]
  field_simp
  ring

lemma comp_apply_eq (T₁ T₂ : MoebiusTransformation) (z : ℂ)
    (hdef : T₁.c * z + T₁.d ≠ 0) :
    (T₂.comp T₁).apply z = T₂.apply (T₁.apply z) := by
  simp only [MoebiusTransformation.apply, MoebiusTransformation.comp]
  field_simp
  ring

theorem moebius_comp_maps (T₁ T₂ : MoebiusTransformation) (S₁ S₂ S₃ : Set ℂ)
    (h₁ : T₁.MapsSetTo S₁ S₂) (h₂ : T₂.MapsSetTo S₂ S₃)
    (h₁_defined : ∀ z ∈ S₁, T₁.c * z + T₁.d ≠ 0) :
    (T₂.comp T₁).MapsSetTo S₁ S₃ := by
  obtain ⟨h₁f, h₁b⟩ := h₁
  obtain ⟨h₂f, h₂b⟩ := h₂
  refine ⟨?_, ?_⟩
  ·
    intro z hz hcomp_def
    have h1def := h₁_defined z hz
    have hmid : T₁.apply z ∈ S₂ := h₁f z hz h1def
    rw [comp_denom_factor T₁ T₂ z h1def] at hcomp_def
    have h2def : T₂.c * T₁.apply z + T₂.d ≠ 0 := (mul_ne_zero_iff.mp hcomp_def).1
    rw [comp_apply_eq T₁ T₂ z h1def]
    exact h₂f (T₁.apply z) hmid h2def
  ·
    intro w hw
    obtain ⟨w', hw'S₂, h2def, h2eq⟩ := h₂b w hw
    obtain ⟨z, hzS₁, h1def, h1eq⟩ := h₁b w' hw'S₂
    refine ⟨z, hzS₁, ?_, ?_⟩
    · rw [comp_denom_factor T₁ T₂ z h1def]
      exact mul_ne_zero (h1eq ▸ h2def) h1def
    · rw [comp_apply_eq T₁ T₂ z h1def, h1eq, h2eq]

lemma MoebiusTransformation.apply_injective (T : MoebiusTransformation)
    (z₁ z₂ : ℂ) (h1 : T.c * z₁ + T.d ≠ 0) (h2 : T.c * z₂ + T.d ≠ 0)
    (heq : T.apply z₁ = T.apply z₂) : z₁ = z₂ := by
  simp only [MoebiusTransformation.apply] at heq
  rw [div_eq_div_iff h1 h2] at heq
  have key : (T.a * T.d - T.b * T.c) * (z₁ - z₂) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h T.det_ne_zero
  · exact sub_eq_zero.mp h

theorem moebius_preserves_nonintersecting_line (T₁ : MoebiusTransformation)
    (A B : Circle) (L : GeneralizedCircle) (B₁ : Circle)
    (hAB : Circle.Nonintersecting A B)
    (hA : T₁.MapsGenCircle (.circle A) L)
    (hB : T₁.MapsCircle B B₁) :
    Disjoint L.toSet B₁.toSet := by
  rw [Set.disjoint_iff]
  intro w ⟨hwL, hwB₁⟩
  obtain ⟨z₁, hz₁A, h1def, h1eq⟩ := hA.2 w hwL
  obtain ⟨z₂, hz₂B, h2def, h2eq⟩ := hB.2 w hwB₁
  have hinj : z₁ = z₂ := T₁.apply_injective z₁ z₂ h1def h2def (by rw [h1eq, h2eq])
  have : z₁ ∈ A.toSet ⊓ B.toSet := ⟨hz₁A, hinj ▸ hz₂B⟩
  exact (hAB.le_bot this).elim


theorem nonintersecting_circles_concentric (A B : Circle)
    (h : Circle.Nonintersecting A B) :
    ∃ (T : MoebiusTransformation) (A' B' : Circle),
      T.MapsCircle A A' ∧ T.MapsCircle B B' ∧ A'.Concentric B' := by

  obtain ⟨p, hp⟩ := circle_nonempty A
  have hpB : p ∉ B.toSet := Set.disjoint_left.mp h hp
  obtain ⟨L, hLline, hAL⟩ := invTranslation_maps_circle_through_pole_to_line A p hp
  obtain ⟨B₁, hBB₁⟩ := invTranslation_maps_circle_away_from_pole_to_circle B p hpB

  have hdisj : Disjoint L.toSet B₁.toSet :=
    moebius_preserves_nonintersecting_line (invTranslation p) A B L B₁ h hAL hBB₁

  have hLne : L.toSet.Nonempty := by
    obtain ⟨z, hz, hzp⟩ := circle_exists_ne A p
    have hndef : (invTranslation p).c * z + (invTranslation p).d ≠ 0 := by
      simp only [invTranslation]
      show 1 * z + -p ≠ 0
      have : 1 * z + -p = z - p := by ring
      rw [this]; exact sub_ne_zero.mpr hzp
    exact ⟨(invTranslation p).apply z, hAL.1 z hz hndef⟩

  obtain ⟨T₂, A₂, B₂, hLA₂_fwd, hLA₂_bwd, hB₁B₂, hconc, hinfty⟩ :=
    moebius_line_circle_to_concentric L B₁ hLline hLne hdisj


  set T₁ := invTranslation p with hT₁_def

  have hB_defined : ∀ z ∈ B.toSet, T₁.c * z + T₁.d ≠ 0 := by
    intro z hz
    simp only [invTranslation, hT₁_def]
    show 1 * z + -p ≠ 0
    have hne : z ≠ p := fun h => hpB (h ▸ hz)
    have : 1 * z + -p = z - p := by ring
    rw [this]; exact sub_ne_zero.mpr hne
  have hB_comp : (T₂.comp T₁).MapsSetTo B.toSet B₂.toSet :=
    moebius_comp_maps T₁ T₂ B.toSet B₁.toSet B₂.toSet hBB₁ hB₁B₂ hB_defined


  have hA_comp : (T₂.comp T₁).MapsSetTo A.toSet A₂.toSet := by
    refine ⟨?_, ?_⟩
    ·
      intro z hz hcomp_def
      by_cases h1def : T₁.c * z + T₁.d = 0
      ·

        simp only [invTranslation, hT₁_def] at h1def
        have hzp : z = p := by have := h1def; linear_combination this


        have hcomp_c_eq : (T₂.comp T₁).c * z + (T₂.comp T₁).d = T₂.c := by
          subst hzp
          simp only [MoebiusTransformation.comp, invTranslation, hT₁_def]
          ring
        rw [hcomp_c_eq] at hcomp_def


        have hcomp_apply_eq : (T₂.comp T₁).apply z = T₂.a / T₂.c := by
          subst hzp
          simp only [MoebiusTransformation.apply, MoebiusTransformation.comp,
            invTranslation, hT₁_def]
          congr 1 <;> ring
        rw [hcomp_apply_eq]
        exact hinfty hcomp_def
      ·
        have hmid : T₁.apply z ∈ L.toSet := (hAL.1 z hz h1def)
        rw [comp_denom_factor T₁ T₂ z h1def] at hcomp_def
        have h2def : T₂.c * T₁.apply z + T₂.d ≠ 0 := (mul_ne_zero_iff.mp hcomp_def).1
        rw [comp_apply_eq T₁ T₂ z h1def]
        exact hLA₂_fwd (T₁.apply z) hmid h2def
    ·
      intro w hw
      by_cases hcase : T₂.c = 0 ∨ w ≠ T₂.a / T₂.c
      ·
        obtain ⟨w', hw'L, h2def, h2eq⟩ := hLA₂_bwd w hw hcase
        obtain ⟨z, hzA, h1def, h1eq⟩ := hAL.2 w' hw'L
        refine ⟨z, hzA, ?_, ?_⟩
        · rw [comp_denom_factor T₁ T₂ z h1def]
          exact mul_ne_zero (h1eq ▸ h2def) h1def
        · rw [comp_apply_eq T₁ T₂ z h1def, h1eq, h2eq]
      ·
        simp only [not_or, not_not] at hcase
        obtain ⟨hc_ne, hw_eq⟩ := hcase
        refine ⟨p, hp, ?_, ?_⟩
        ·
          show (T₂.comp T₁).c * p + (T₂.comp T₁).d ≠ 0
          have : (T₂.comp T₁).c * p + (T₂.comp T₁).d = T₂.c := by
            simp only [MoebiusTransformation.comp, invTranslation, hT₁_def]
            ring
          rw [this]; exact hc_ne
        ·
          rw [hw_eq]
          show (T₂.comp T₁).apply p = T₂.a / T₂.c
          simp only [MoebiusTransformation.apply, MoebiusTransformation.comp,
            invTranslation, hT₁_def]
          congr 1 <;> ring

  exact ⟨T₂.comp T₁, A₂, B₂, hA_comp, hB_comp, hconc⟩

end Lecture6
