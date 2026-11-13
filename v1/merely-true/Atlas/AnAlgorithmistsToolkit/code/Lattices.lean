/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
noncomputable section

open MeasureTheory MeasureTheory.Measure Submodule Module ZSpan Set Metric

namespace Lattices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem blichfeldt (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : NullMeasurableSet S μ)
    (hvol : ENNReal.ofReal (ZLattice.covolume L μ) < μ S) :
    ∃ z₁ ∈ S, ∃ z₂ ∈ S, z₁ ≠ z₂ ∧ z₁ - z₂ ∈ (L : Set E) := by

  set b := Free.chooseBasis ℤ L
  set F := fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain L F μ := ZLattice.isAddFundamentalDomain b μ

  have hcovol_eq : ZLattice.covolume L μ = μ.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ hfund
  have hfund_fin : μ F < ⊤ := (fundamentalDomain_isBounded _).measure_lt_top
  have hlt : μ F < μ S := by
    rw [hcovol_eq, Measure.real] at hvol
    rwa [ENNReal.ofReal_toReal (ne_of_lt hfund_fin)] at hvol

  haveI : Countable L.toAddSubgroup := (inferInstance : Countable L)

  have hfund' : IsAddFundamentalDomain L.toAddSubgroup F μ := hfund
  obtain ⟨x, y, hxy, hnd⟩ :=
    MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd hfund' hS hlt

  obtain ⟨p, hp1, hp2⟩ := not_disjoint_iff.mp hnd
  rw [mem_vadd_set] at hp1 hp2
  obtain ⟨s₁, hs₁, hps₁⟩ := hp1
  obtain ⟨s₂, hs₂, hps₂⟩ := hp2
  simp only [AddSubgroup.vadd_def, vadd_eq_add] at hps₁ hps₂
  refine ⟨s₁, hs₁, s₂, hs₂, ?_, ?_⟩
  · intro heq
    apply hxy
    have h_eq : (x : E) + s₁ = (y : E) + s₂ := by rw [hps₁, hps₂]
    rw [heq] at h_eq
    exact Subtype.ext (add_right_cancel h_eq)
  · have h_eq : (x : E) + s₁ = (y : E) + s₂ := by rw [hps₁, hps₂]
    have hsub : s₁ - s₂ = (↑y : E) - (↑x : E) := by
      have h1 : s₁ = -(x : E) + p := by rw [← hps₁]; abel
      have h2 : s₂ = -(y : E) + p := by rw [← hps₂]; abel
      rw [h1, h2]; abel
    rw [hsub]
    exact L.sub_mem y.2 x.2

theorem minkowski (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (h_symm : ∀ x ∈ S, -x ∈ S) (h_conv : Convex ℝ S)
    (hvol : ENNReal.ofReal (ZLattice.covolume L μ) * 2 ^ finrank ℝ E < μ S) :
    ∃ x ∈ (L : Set E), x ≠ 0 ∧ x ∈ S := by
  set b := Free.chooseBasis ℤ L
  set F := fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain L F μ := ZLattice.isAddFundamentalDomain b μ
  have hcovol_eq : ZLattice.covolume L μ = μ.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ hfund
  have hfund_fin : μ F < ⊤ := (fundamentalDomain_isBounded _).measure_lt_top
  have hlt : μ F * 2 ^ finrank ℝ E < μ S := by
    rw [hcovol_eq, Measure.real] at hvol
    rwa [ENNReal.ofReal_toReal (ne_of_lt hfund_fin)] at hvol
  haveI : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have hfund' : IsAddFundamentalDomain L.toAddSubgroup F μ := hfund
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      hfund' h_symm h_conv hlt
  exact ⟨(x : E), x.2, by exact_mod_cast Subtype.coe_injective.ne hx_ne, hx_mem⟩

section MinkowskiCorollary

variable {n : ℕ} [NeZero n]

theorem minkowski_shortest_vector_bound
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ x ∈ (L : Set (Fin n → ℝ)), x ≠ 0 ∧
      Real.sqrt (∑ i, x i ^ 2) ≤
        Real.sqrt n * (ZLattice.covolume L volume) ^ ((1 : ℝ) / n) := by
  set c := ZLattice.covolume L volume with hc_def
  set s := c ^ ((1 : ℝ) / ↑n) with hs_def
  have hc_pos : 0 < c := ZLattice.covolume_pos L volume
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hc_pos _
  have hs_nonneg : 0 ≤ s := hs_pos.le
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set b := Free.chooseBasis ℤ L
  set F := fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  have hfund_fin : volume F < ⊤ := (fundamentalDomain_isBounded _).measure_lt_top
  have hcovol_eq : c = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund
  have hs_pow : s ^ (n : ℕ) = c := by
    rw [hs_def, ← Real.rpow_natCast s n, ← Real.rpow_mul hc_pos.le]; simp [hn_ne]
  have hvol_cube : volume (closedBall (0 : Fin n → ℝ) s) =
      ENNReal.ofReal ((2 * s) ^ n) := by
    have := Real.volume_pi_closedBall (0 : Fin n → ℝ) hs_nonneg
    rwa [Fintype.card_fin] at this
  have h2s_pow : (2 * s) ^ n = 2 ^ n * c := by rw [mul_pow, ← hs_pow]
  have hvol_le : volume F * 2 ^ finrank ℝ (Fin n → ℝ) ≤
      volume (closedBall (0 : Fin n → ℝ) s) := by
    rw [hvol_cube, h2s_pow, finrank_pi, Fintype.card_fin, hcovol_eq, Measure.real,
        mul_comm (2 ^ n : ℝ), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (ne_of_lt hfund_fin),
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
    norm_cast
  haveI : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have hfund' : IsAddFundamentalDomain L.toAddSubgroup F volume := hfund
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      hfund'
      (fun x hx => by simp only [mem_closedBall, dist_zero_right] at hx ⊢; simp [hx])
      (convex_closedBall 0 s) (isCompact_closedBall 0 s) hvol_le
  refine ⟨(x : Fin n → ℝ), x.2, Subtype.coe_injective.ne hx_ne, ?_⟩
  rw [mem_closedBall, dist_zero_right] at hx_mem
  have hcoord : ∀ i, |((x : Fin n → ℝ) i)| ≤ s := by
    rwa [pi_norm_le_iff_of_nonneg hs_nonneg] at hx_mem
  rw [show Real.sqrt n * s = Real.sqrt (n * s ^ 2) from by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hs_nonneg]]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ((x : Fin n → ℝ) i) ^ 2
      ≤ ∑ _i : Fin n, s ^ 2 := Finset.sum_le_sum fun i _ =>
        sq_le_sq' (by linarith [abs_le.mp (hcoord i)]) ((abs_le.mp (hcoord i)).2)
      _ = n * s ^ 2 := by simp [Finset.sum_const]

end MinkowskiCorollary

end Lattices

namespace Lattice2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsReducedBasis (u v : E) : Prop :=
  ‖u‖ ≤ ‖v‖ ∧ 2 * |@inner ℝ E _ u v| ≤ ‖u‖ ^ 2

def IsLatticeVector (u v : E) (w : E) : Prop :=
  ∃ a b : ℤ, w = (a : ℝ) • u + (b : ℝ) • v

theorem norm_lattice_vec_ge_norm_u (u v : E) (hred : IsReducedBasis u v)
    (a b : ℤ) (hab : ¬(a = 0 ∧ b = 0)) :
    ‖u‖ ≤ ‖(a : ℝ) • u + (b : ℝ) • v‖ := by
  suffices h : ‖u‖ ^ 2 ≤ ‖(a : ℝ) • u + (b : ℝ) • v‖ ^ 2 by
    nlinarith [norm_nonneg ((a : ℝ) • u + (b : ℝ) • v),
              sq_nonneg (‖(a : ℝ) • u + (b : ℝ) • v‖ - ‖u‖)]
  have hnorm_ord := hred.1
  have hinner := hred.2

  have key : ‖(a : ℝ) • u + (b : ℝ) • v‖ ^ 2 =
      (a : ℝ) ^ 2 * ‖u‖ ^ 2 + 2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v +
      (b : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    rw [@norm_add_sq_real E]
    simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, mul_pow]
    nlinarith [sq_abs (a : ℝ), sq_abs (b : ℝ)]

  have hcross : -(|(a : ℝ) * (b : ℝ)|) * ‖u‖ ^ 2 ≤
      2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v := by
    have bound : |2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v| ≤
        |(a : ℝ) * (b : ℝ)| * ‖u‖ ^ 2 := by
      have : |2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v| =
          |(a : ℝ) * (b : ℝ)| * (2 * |@inner ℝ E _ u v|) := by
        rw [show 2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v =
          ((a : ℝ) * (b : ℝ)) * (2 * @inner ℝ E _ u v) from by ring]
        rw [abs_mul, abs_mul (2 : ℝ), abs_of_pos (show (0:ℝ) < 2 from by norm_num)]
      linarith [mul_le_mul_of_nonneg_left hinner (abs_nonneg ((a : ℝ) * (b : ℝ)))]
    linarith [neg_abs_le (2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v)]

  have hv_ge : (b : ℝ) ^ 2 * ‖u‖ ^ 2 ≤ (b : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [norm_nonneg u]

  have hint : (1 : ℤ) ≤ a ^ 2 - |a| * |b| + b ^ 2 := by
    rcases Classical.em (b = 0) with hb | hb
    · have ha : a ≠ 0 := fun h => hab ⟨h, hb⟩
      simp [hb]; nlinarith [Int.one_le_abs ha, sq_abs a]
    · nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, Int.one_le_abs hb, abs_nonneg a]

  have hint_real : (1 : ℝ) ≤ (a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)| + (b : ℝ) ^ 2 := by
    have h : ((a ^ 2 - |a| * |b| + b ^ 2 : ℤ) : ℝ) ≥ 1 := by exact_mod_cast hint
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_abs] at h
    rw [show |(a : ℝ) * (b : ℝ)| = |(a : ℝ)| * |(b : ℝ)| from abs_mul _ _]
    linarith

  have hab_eq : |(a : ℝ) * (b : ℝ)| = |(a : ℝ)| * |(b : ℝ)| := abs_mul _ _
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ((a : ℝ) ^ 2 - |(a : ℝ)| * |(b : ℝ)|)]

theorem norm_lattice_vec_ge_norm_v (u v : E) (hred : IsReducedBasis u v)
    (a b : ℤ) (hb : b ≠ 0) :
    ‖v‖ ≤ ‖(a : ℝ) • u + (b : ℝ) • v‖ := by
  suffices h : ‖v‖ ^ 2 ≤ ‖(a : ℝ) • u + (b : ℝ) • v‖ ^ 2 by
    nlinarith [norm_nonneg ((a : ℝ) • u + (b : ℝ) • v),
              sq_nonneg (‖(a : ℝ) • u + (b : ℝ) • v‖ - ‖v‖)]
  have hnorm_ord := hred.1
  have hinner := hred.2
  have key : ‖(a : ℝ) • u + (b : ℝ) • v‖ ^ 2 =
      (a : ℝ) ^ 2 * ‖u‖ ^ 2 + 2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v +
      (b : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    rw [@norm_add_sq_real E]
    simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, mul_pow]
    nlinarith [sq_abs (a : ℝ), sq_abs (b : ℝ)]
  have hcross : -(|(a : ℝ) * (b : ℝ)|) * ‖u‖ ^ 2 ≤
      2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v := by
    have bound : |2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v| ≤
        |(a : ℝ) * (b : ℝ)| * ‖u‖ ^ 2 := by
      have : |2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v| =
          |(a : ℝ) * (b : ℝ)| * (2 * |@inner ℝ E _ u v|) := by
        rw [show 2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v =
          ((a : ℝ) * (b : ℝ)) * (2 * @inner ℝ E _ u v) from by ring]
        rw [abs_mul, abs_mul (2 : ℝ), abs_of_pos (show (0:ℝ) < 2 from by norm_num)]
      linarith [mul_le_mul_of_nonneg_left hinner (abs_nonneg ((a : ℝ) * (b : ℝ)))]
    linarith [neg_abs_le (2 * ((a : ℝ) * (b : ℝ)) * @inner ℝ E _ u v)]

  suffices hkey : (0 : ℝ) ≤ ((a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)|) * ‖u‖ ^ 2 +
      ((b : ℝ) ^ 2 - 1) * ‖v‖ ^ 2 by linarith
  have hb_sq : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by
    nlinarith [sq_abs (b : ℝ), show (1 : ℝ) ≤ |(b : ℝ)| from by exact_mod_cast Int.one_le_abs hb]
  have hv_sq : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith [norm_nonneg u]
  by_cases hle : |(a : ℝ) * (b : ℝ)| ≤ (a : ℝ) ^ 2
  ·
    have h1 : (0 : ℝ) ≤ ((a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)|) * ‖u‖ ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) * ‖v‖ ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  ·
    simp only [not_le] at hle
    have h_neg : (a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)| < 0 := by linarith

    have h_bd : ((a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)|) * ‖v‖ ^ 2 ≤
        ((a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)|) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonpos_left hv_sq (by linarith)

    have hint : (1 : ℤ) ≤ a ^ 2 - |a| * |b| + b ^ 2 := by
      nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, Int.one_le_abs hb, abs_nonneg a]
    have hint_real : (0 : ℝ) ≤ (a : ℝ) ^ 2 - |(a : ℝ) * (b : ℝ)| + (b : ℝ) ^ 2 - 1 := by
      have h : ((a ^ 2 - |a| * |b| + b ^ 2 : ℤ) : ℝ) ≥ 1 := by exact_mod_cast hint
      simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_abs] at h
      rw [show |(a : ℝ) * (b : ℝ)| = |(a : ℝ)| * |(b : ℝ)| from abs_mul _ _]
      linarith
    nlinarith [sq_nonneg ‖v‖]

theorem reduced_basis_successive_minima
    (u v : E) (_hu : u ≠ 0) (_hv : v ≠ 0)
    (_hli : LinearIndependent ℝ ![u, v])
    (hred : IsReducedBasis u v) :
    (∀ w, IsLatticeVector u v w → w ≠ 0 → ‖u‖ ≤ ‖w‖) ∧
    (∀ w, IsLatticeVector u v w → (∀ c : ℝ, w ≠ c • u) → ‖v‖ ≤ ‖w‖) := by
  refine ⟨fun w ⟨a, b, hw⟩ hw_ne => ?_, fun w ⟨a, b, hw⟩ hw_indep => ?_⟩
  · rw [hw]
    exact norm_lattice_vec_ge_norm_u u v hred a b (fun ⟨ha, hb⟩ => by
      apply hw_ne; rw [hw, ha, hb]; simp)
  · rw [hw]
    have hb : b ≠ 0 := by
      intro hb_eq
      apply hw_indep (a : ℝ)
      rw [hw, hb_eq]; simp
    exact norm_lattice_vec_ge_norm_v u v hred a b hb

end Lattice2D

open InnerProductSpace Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gramSchmidtCoeff (f : Fin n → E) (i k : Fin n) : ℝ :=
  @inner ℝ E _ (gramSchmidt ℝ f k) (f i) / (‖gramSchmidt ℝ f k‖ ^ 2)

structure IsLLLReduced (f : Fin n → E) : Prop where
  sizeReduced : ∀ (i k : Fin n), k < i → |gramSchmidtCoeff f i k| ≤ 1 / 2
  lovasz : ∀ (i : Fin n) (hi : i.val + 1 < n),
    ‖gramSchmidt ℝ f i‖ ^ 2 ≤
      4 / 3 * ‖gramSchmidt ℝ f ⟨i.val + 1, hi⟩ +
        gramSchmidtCoeff f ⟨i.val + 1, hi⟩ i • gramSchmidt ℝ f i‖ ^ 2
