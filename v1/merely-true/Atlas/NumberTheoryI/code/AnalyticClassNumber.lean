/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.ModularLattice
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units

noncomputable section

namespace Section19

section LipschitzParametrizable

def IsLipschitzContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Prop :=
  ∃ K : ℝ≥0, LipschitzWith K f

def IsLipschitzParametrizable {X : Type*} [PseudoMetricSpace X] (B : Set X) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → ((Fin d → ℝ) → X)),
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧
    B ⊆ ⋃ i, (f i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1))

theorem IsLipschitzParametrizable.image_linearEquiv {n d : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsLipschitzParametrizable B d)
    (e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    IsLipschitzParametrizable (e '' B) d := by
  obtain ⟨m, f, hLip, hCov⟩ := hB
  refine ⟨m, fun i => e ∘ (f i), fun i => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hLip i
    exact ⟨‖(e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖₊ * K, e.lipschitz.comp hK⟩
  · intro x hx
    obtain ⟨b, hbB, rfl⟩ := hx
    have hb := hCov hbB
    simp only [Set.mem_iUnion, Set.mem_image] at hb ⊢
    obtain ⟨i, y, hy, rfl⟩ := hb
    exact ⟨i, y, hy, rfl⟩

theorem IsLipschitzParametrizable.union {X : Type*} [PseudoMetricSpace X]
    {A B : Set X} {d : ℕ} (hA : IsLipschitzParametrizable A d.succ)
    (hB : IsLipschitzParametrizable B d.succ) :
    IsLipschitzParametrizable (A ∪ B) d.succ := by
  obtain ⟨mA, fA, hLipA, hCovA⟩ := hA; obtain ⟨mB, fB, hLipB, hCovB⟩ := hB
  refine ⟨mA + mB, Fin.addCases fA fB, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]; exact hLipA j
    · simp only [Fin.addCases_right]; exact hLipB j
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_image]
    rcases hx with hxA | hxB
    · have hx' := hCovA hxA; rw [Set.mem_iUnion] at hx'
      obtain ⟨j, y, hy, rfl⟩ := hx'
      exact ⟨Fin.castAdd mB j, y, hy, by simp [Fin.addCases_left]⟩
    · have hx' := hCovB hxB; rw [Set.mem_iUnion] at hx'
      obtain ⟨j, y, hy, rfl⟩ := hx'
      exact ⟨Fin.natAdd mA j, y, hy, by simp [Fin.addCases_right]⟩

end LipschitzParametrizable

lemma floor_diff_bound' {a b D : ℝ} (hab : |a - b| ≤ D) :
    |⌊a⌋ - ⌊b⌋| ≤ (⌈D⌉ : ℤ) := by
  rw [abs_le]; have hab' := abs_le.mp hab
  constructor
  · suffices ⌊b⌋ - ⌊a⌋ ≤ ⌈D⌉ by omega
    linarith [Int.floor_le_floor (show b ≤ a + D by linarith [hab'.1]),
      show ⌊a + D⌋ < ⌊a⌋ + ⌈D⌉ + 1 from by
        rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one a, Int.le_ceil D]]
  · linarith [Int.floor_le_floor (show a ≤ b + D by linarith [hab'.2]),
      show ⌊b + D⌋ < ⌊b⌋ + ⌈D⌉ + 1 from by
        rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one b, Int.le_ceil D]]

lemma scaled_coord_diff_le_K {n d : ℕ} {f : (Fin d → ℝ) → (Fin n → ℝ)}
    {K : ℝ≥0} (hf : LipschitzWith K f) {y y' : Fin d → ℝ}
    {t : ℝ} (ht_pos : 0 < t) {T : ℝ} (hT_pos : 0 < T) (ht_le : t ≤ T)
    (hdist : dist y y' ≤ 1 / T) (i : Fin n) :
    |t * (f y) i - t * (f y') i| ≤ (K : ℝ) := by
  have h1 : |f y i - f y' i| ≤ ↑K * (1 / T) := by
    calc |f y i - f y' i| = dist (f y i) (f y' i) := (Real.dist_eq _ _).symm
      _ ≤ dist (f y) (f y') := dist_le_pi_dist (f y) (f y') i
      _ ≤ ↑K * dist y y' := hf.dist_le_mul y y'
      _ ≤ ↑K * (1 / T) := by gcongr
  rw [show t * (f y) i - t * (f y') i = t * ((f y) i - (f y') i) by ring,
      abs_mul, abs_of_pos ht_pos]
  calc t * |f y i - f y' i| ≤ t * (↑K * (1 / T)) := by nlinarith
    _ = ↑K * (t / T) := by ring
    _ ≤ ↑K * 1 := by gcongr; exact div_le_one_of_le₀ ht_le (le_of_lt hT_pos)
    _ = ↑K := by ring

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1024 in
theorem lipschitz_floor_image_card_bound {n d : ℕ}
    (f : (Fin d → ℝ) → (Fin n → ℝ)) (K : ℝ≥0) (hf : LipschitzWith K f)
    (t : ℝ) (ht : 1 ≤ t) :
    Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1} ≤
    ⌈t⌉₊ ^ d * (2 * ⌈(↑K : ℝ) * Real.sqrt d⌉₊ + 3) ^ n := by
  set T := ⌈t⌉₊; set L := ⌈(↑K : ℝ) * Real.sqrt d⌉₊; set M := 2 * L + 3
  have hT_pos : 0 < T := Nat.ceil_pos.mpr (by linarith)
  have hT' : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  have ht_pos : (0 : ℝ) < t := by linarith
  have ht_le_T : t ≤ (T : ℝ) := Nat.le_ceil t
  set S := {v : Fin n → ℤ | ∃ y ∈ pi univ (fun _ => Icc (0 : ℝ) 1),
    ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1}
  let cube_idx : (Fin d → ℝ) → (Fin d → Fin T) :=
    fun y j => ⟨min (⌊(T : ℝ) * y j⌋₊) (T - 1), by omega⟩
  let y₀ : (Fin d → Fin T) → (Fin d → ℝ) := fun c j => (c j : ℕ) / (T : ℝ)
  let ref_vec : (Fin d → Fin T) → (Fin n → ℤ) := fun c i => ⌊t * (f (y₀ c)) i⌋
  have dist_bound : ∀ y, y ∈ pi univ (fun _ => Icc (0 : ℝ) 1) →
      dist y (y₀ (cube_idx y)) ≤ 1 / (T : ℝ) := by
    intro y hy; rw [dist_pi_le_iff (by positivity)]; intro j
    have hyj0 : 0 ≤ y j := (hy j (mem_univ j)).1
    have hyj1 : y j ≤ 1 := (hy j (mem_univ j)).2
    change dist (y j) ((⟨min (⌊(T : ℝ) * y j⌋₊) (T - 1), _⟩ : Fin T).val / (T : ℝ)) ≤ 1 / T
    set c := min (⌊(T : ℝ) * y j⌋₊) (T - 1)
    have hfl : (⌊(T : ℝ) * y j⌋₊ : ℝ) ≤ (T : ℝ) * y j := Nat.floor_le (by positivity)
    have hfl_lt : (T : ℝ) * y j < (⌊(T : ℝ) * y j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hc_le_fl : (c : ℝ) ≤ (⌊(T : ℝ) * y j⌋₊ : ℝ) := by exact_mod_cast Nat.min_le_left _ _
    have hc_le : (c : ℝ) ≤ (T : ℝ) * y j := le_trans hc_le_fl hfl
    rw [Real.dist_eq,
      show y j - (c : ℝ) / (T : ℝ) = ((T : ℝ) * y j - (c : ℝ)) / (T : ℝ) by field_simp,
      abs_div, abs_of_pos hT', abs_of_nonneg (by linarith)]
    apply (div_le_div_iff_of_pos_right hT').mpr
    by_cases hle : ⌊(T : ℝ) * y j⌋₊ ≤ T - 1
    · have hc_eq : c = ⌊(T : ℝ) * y j⌋₊ := Nat.min_eq_left hle
      rw [hc_eq]; push_cast; linarith
    · have hc_eq : c = T - 1 := Nat.min_eq_right (by omega)
      rw [hc_eq]
      have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ T)]; simp
      rw [hT1]
      nlinarith [mul_le_mul_of_nonneg_left hyj1 (le_of_lt hT')]
  have offset_bound : ∀ y, y ∈ pi univ (fun _ => Icc (0 : ℝ) 1) →
      ∀ i : Fin n, |⌊t * (f y) i⌋ - ref_vec (cube_idx y) i| ≤ (L : ℤ) := by
    intro y hy i
    by_cases hd : d = 0
    · subst hd
      have heq_y : y = y₀ (cube_idx y) := Subsingleton.elim _ _
      show |⌊t * f y i⌋ - ⌊t * f (y₀ (cube_idx y)) i⌋| ≤ ↑L
      have : f y = f (y₀ (cube_idx y)) := congrArg f heq_y
      simp [this]
    · have hdist := dist_bound y hy
      have hcoord := scaled_coord_diff_le_K hf ht_pos hT' ht_le_T hdist i
      calc |⌊t * f y i⌋ - ref_vec (cube_idx y) i| ≤ ⌈(K : ℝ)⌉ := floor_diff_bound' hcoord
        _ ≤ (L : ℤ) := by
          have h_nonneg : 0 ≤ (↑K : ℝ) * Real.sqrt d :=
            mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)
          rw [show (L : ℤ) = ⌈(↑K : ℝ) * Real.sqrt d⌉ from by
            rw [show (L : ℤ) = (⌈(↑K : ℝ) * Real.sqrt d⌉₊ : ℤ) from rfl]
            exact_mod_cast (Int.toNat_of_nonneg (Int.ceil_nonneg h_nonneg))]
          exact Int.ceil_le_ceil (le_mul_of_one_le_right K.coe_nonneg
            (by rw [← Real.sqrt_one]
                exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))))
  let choose_y : S → (Fin d → ℝ) := fun ⟨_, hv⟩ => hv.choose
  have choose_mem : ∀ sv : S, choose_y sv ∈ pi univ (fun _ => Icc (0 : ℝ) 1) :=
    fun ⟨_, hv⟩ => hv.choose_spec.1
  have choose_prop : ∀ (sv : S) (i : Fin n),
      (sv.val i : ℝ) ≤ t * (f (choose_y sv)) i ∧
      t * (f (choose_y sv)) i < (sv.val i : ℝ) + 1 :=
    fun ⟨_, hv⟩ i => hv.choose_spec.2 i
  have v_eq : ∀ (sv : S) (i : Fin n), sv.val i = ⌊t * (f (choose_y sv)) i⌋ := by
    intro sv i
    exact (Int.floor_eq_iff.mpr ⟨(choose_prop sv i).1, (choose_prop sv i).2⟩).symm
  have off_in_range : ∀ (sv : S) (i : Fin n),
      0 ≤ sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1 ∧
      (sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1).toNat < M := by
    intro sv i; rw [v_eq sv i]
    have := abs_le.mp (offset_bound _ (choose_mem sv) i)
    exact ⟨by omega, by rw [Int.toNat_lt (by omega)]; omega⟩
  let φ : S → (Fin d → Fin T) × (Fin n → Fin M) := fun sv =>
    (cube_idx (choose_y sv),
     fun i => ⟨(sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1).toNat,
       (off_in_range sv i).2⟩)
  have hφ_inj : Function.Injective φ := by
    intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
    have heq1 : cube_idx (choose_y ⟨v₁, hv₁⟩) = cube_idx (choose_y ⟨v₂, hv₂⟩) :=
      congr_arg Prod.fst heq
    ext i
    have h1 := (off_in_range ⟨v₁, hv₁⟩ i).1
    have h2 := (off_in_range ⟨v₂, hv₂⟩ i).1
    have heq_snd := congr_arg Prod.snd heq
    have heq_i := congr_fun heq_snd i
    change v₁ i = v₂ i
    have hv1 : (φ ⟨v₁, hv₁⟩).2 i = (φ ⟨v₂, hv₂⟩).2 i := heq_i
    have hval := Fin.val_eq_of_eq hv1
    show v₁ i = v₂ i
    dsimp only [φ] at hval
    rw [heq1] at hval h1
    have h1' := Int.toNat_of_nonneg h1
    have h2' := Int.toNat_of_nonneg h2
    simp only [] at h1' h2'
    omega
  calc Nat.card S
      ≤ Nat.card ((Fin d → Fin T) × (Fin n → Fin M)) :=
        Nat.card_le_card_of_injective φ hφ_inj
    _ = T ^ d * M ^ n := by
        rw [Nat.card_prod, Nat.card_pi, Nat.card_pi, Finset.prod_const, Finset.prod_const,
            Finset.card_fin, Finset.card_fin, Nat.card_fin, Nat.card_fin]

theorem lipschitz_floor_image_finite {n d : ℕ}
    (f : (Fin d → ℝ) → (Fin n → ℝ)) (K : ℝ≥0) (hf : LipschitzWith K f)
    (t : ℝ) (ht : 1 ≤ t) :
    Set.Finite {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1} := by
  have ht_pos : (0 : ℝ) < t := by linarith
  set y₀ : Fin d → ℝ := 0

  have hcoord_bound : ∀ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ i : Fin n, |f y i - f y₀ i| ≤ (K : ℝ) * Real.sqrt d := by
    intro y hy i
    calc |f y i - f y₀ i|
        ≤ dist (f y) (f y₀) := dist_le_pi_dist (f y) (f y₀) i
      _ ≤ K * dist y y₀ := hf.dist_le_mul y y₀
      _ ≤ K * Real.sqrt d := by
        apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
        rw [dist_pi_le_iff (Real.sqrt_nonneg d)]
        intro j
        have hyj := hy j (Set.mem_univ j)
        simp only [y₀, Pi.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hyj.1]
        calc y j ≤ 1 := hyj.2
          _ ≤ Real.sqrt d := by
            rcases Nat.eq_zero_or_pos d with hd | hd
            · exact (hd ▸ j).elim0
            · rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt (by exact_mod_cast hd)

  set R : ℝ := ‖f y₀‖ + (K : ℝ) * Real.sqrt d
  have hfy_bound : ∀ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ i : Fin n, |f y i| ≤ R := by
    intro y hy i
    have h1 := hcoord_bound y hy i
    have h2 : |f y₀ i| ≤ ‖f y₀‖ := norm_le_pi_norm (f y₀) i
    calc |f y i| = |(f y i - f y₀ i) + f y₀ i| := by ring_nf
      _ ≤ |f y i - f y₀ i| + |f y₀ i| := abs_add_le _ _
      _ ≤ (K : ℝ) * Real.sqrt d + ‖f y₀‖ := by linarith
      _ = R := by ring

  set B : ℤ := ⌈t * R⌉ + 1
  apply (Set.Finite.pi' (fun _ => Set.finite_Icc (-B) B)).subset
  intro v ⟨y, hy, hvy⟩ i
  have hv_eq : v i = ⌊t * f y i⌋ :=
    (Int.floor_eq_iff.mpr ⟨(hvy i).1, (hvy i).2⟩).symm
  have htf_bound : |t * f y i| ≤ t * R := by
    rw [abs_mul, abs_of_pos ht_pos]
    exact mul_le_mul_of_nonneg_left (hfy_bound y hy i) (le_of_lt ht_pos)
  rw [hv_eq]
  constructor
  ·
    have h := (abs_le.mp htf_bound).1
    have : -(t * R) ≤ t * f y i := h
    have hfl := Int.floor_le_floor this
    rw [Int.floor_neg] at hfl; omega
  ·
    have h := (abs_le.mp htf_bound).2
    calc ⌊t * f y i⌋ ≤ ⌈t * f y i⌉ := Int.floor_le_ceil _
      _ ≤ ⌈t * R⌉ := Int.ceil_le_ceil h
      _ ≤ B := by omega

theorem single_lipschitz_image_cube_count {n d : ℕ} (f : (Fin d → ℝ) → (Fin n → ℝ))
    (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
        ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1} ≤ C * t ^ d := by
  set M : ℕ := 2 * ⌈(↑K : ℝ) * Real.sqrt d⌉₊ + 3
  refine ⟨(2 : ℝ) ^ d * (M : ℝ) ^ n, ?_, ?_⟩
  ·
    apply mul_pos
    · positivity
    · exact pow_pos (by positivity) n
  · intro t ht
    have hbound := lipschitz_floor_image_card_bound f K hf t ht
    have ht0 : (0 : ℝ) ≤ t := by linarith

    have hceil_le : (⌈t⌉₊ : ℝ) ≤ 2 * t := by
      have h1 : ⌈t⌉₊ ≤ ⌊t⌋₊ + 1 := Nat.ceil_le_floor_add_one t
      have h2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      calc (⌈t⌉₊ : ℝ) ≤ (⌊t⌋₊ + 1 : ℕ) := by exact_mod_cast h1
        _ = (⌊t⌋₊ : ℝ) + 1 := by push_cast; ring
        _ ≤ t + 1 := by linarith
        _ ≤ 2 * t := by linarith
    calc (Nat.card _ : ℝ) ≤ ↑(⌈t⌉₊ ^ d * M ^ n) := by exact_mod_cast hbound
      _ = (⌈t⌉₊ : ℝ) ^ d * (M : ℝ) ^ n := by push_cast; ring
      _ ≤ (2 * t) ^ d * (M : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_left₀ (by positivity) hceil_le d
          · positivity
      _ = (2 : ℝ) ^ d * (M : ℝ) ^ n * t ^ d := by ring

def outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∃ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) ∧
    (fun i => x i / t) ∈ S}

def innerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∀ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) →
    (fun i => x i / t) ∈ S}

lemma lattice_count_subset_outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} ⊆ outerCubeSet S t := by
  intro x hx
  simp only [outerCubeSet, mem_setOf_eq]
  refine ⟨fun i => (x i : ℝ), fun i => ⟨le_refl _, by linarith⟩, hx⟩

lemma innerCubeSet_subset_lattice_count {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    innerCubeSet S t ⊆ {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} := by
  intro v hv
  simp only [innerCubeSet, mem_setOf_eq] at *
  apply hv; intro i; exact ⟨le_refl _, by linarith⟩

theorem outerCubeSet_finite {n : ℕ} (_hn : 0 < n) (S : Set (Fin n → ℝ))
    (_hS : MeasurableSet S) (hBdd : Bornology.IsBounded S) (t : ℝ) (ht : 1 ≤ t) :
    (outerCubeSet S t).Finite := by
  rw [isBounded_iff_forall_norm_le] at hBdd
  obtain ⟨R, hR⟩ := hBdd
  have ht_pos : (0 : ℝ) < t := by linarith
  set B := ⌈R * t + 1⌉ with hB_def
  apply Set.Finite.subset (Set.Finite.pi (fun _ => Set.finite_Icc (-B) B))
  intro v hv
  simp only [outerCubeSet, mem_setOf_eq] at hv
  obtain ⟨x, hx_range, hx_mem⟩ := hv
  simp only [mem_univ_pi, mem_Icc]
  intro i
  have hxt : ‖(fun j => x j / t)‖ ≤ R := hR _ hx_mem
  have hxi_t : |x i / t| ≤ R := (norm_le_pi_norm (fun j => x j / t) i).trans hxt
  have hxi : |x i| ≤ R * t := by
    rwa [abs_div, div_le_iff₀ (abs_pos.mpr ht_pos.ne'), abs_of_pos ht_pos] at hxi_t
  obtain ⟨hlo, hhi⟩ := hx_range i
  have hxi_hi : x i ≤ R * t := (abs_le.mp hxi).2
  constructor
  · suffices h : -B < v i + 1 by omega
    suffices h : ((-B : ℤ) : ℝ) < ((v i + 1 : ℤ) : ℝ) by exact_mod_cast h
    push_cast
    calc (-(⌈R * t + 1⌉ : ℤ) : ℝ) ≤ -(R * t + 1) := by
            linarith [Int.le_ceil (R * t + 1)]
      _ < (v i : ℝ) + 1 := by linarith [neg_le_of_abs_le hxi]
  · suffices h : (v i : ℤ) < B + 1 by omega
    suffices h : ((v i : ℤ) : ℝ) < ((B + 1 : ℤ) : ℝ) by exact_mod_cast h
    push_cast
    calc (v i : ℝ) ≤ x i := hlo
      _ ≤ R * t := hxi_hi
      _ < R * t + 1 := by linarith
      _ ≤ (⌈R * t + 1⌉ : ℤ) := Int.le_ceil _
      _ < (⌈R * t + 1⌉ : ℤ) + 1 := by linarith

noncomputable def unitCube {n : ℕ} (v : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1))

theorem cube_measure_sandwich {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S) (hS_vol : volume S ≠ ⊤) (t : ℝ) (ht : 1 ≤ t)
    (hfin_outer : (outerCubeSet S t).Finite) :
    (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n ∧
    (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
  open Pointwise ENNReal in
  have ht0 : (0 : ℝ) < t := by linarith
  have ht_ne : t ≠ 0 := ne_of_gt ht0

  have inner_sub_outer : innerCubeSet S t ⊆ outerCubeSet S t := by
    intro v hv
    exact ⟨fun i => (v i : ℝ), fun i => ⟨le_refl _, by linarith⟩,
      hv (fun i => (v i : ℝ)) (fun i => ⟨le_refl _, by linarith⟩)⟩
  have hfin_inner := hfin_outer.subset inner_sub_outer
  haveI := hfin_inner.to_subtype
  haveI := hfin_outer.to_subtype

  have vol_cube : ∀ v : Fin n → ℤ, volume (unitCube v) = 1 := by
    intro v; simp only [unitCube, Real.volume_pi_Ico, add_sub_cancel_left]
    simp [ENNReal.ofReal_one]

  have meas_cube : ∀ v : Fin n → ℤ, MeasurableSet (unitCube v) :=
    fun v => MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

  have pd_all : Set.PairwiseDisjoint (Set.univ : Set (Fin n → ℤ)) unitCube := by
    intro v _ w _ hvw
    simp only [Function.onFun, Set.disjoint_left, unitCube, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ico]
    intro x hxv hxw; apply hvw; funext i
    have hvi := (hxv i).1; have hvi2 := (hxv i).2
    have hwi := (hxw i).1; have hwi2 := (hxw i).2
    have : (v i : ℤ) = w i := by
      by_contra h; rcases lt_or_gt_of_ne h with h' | h'
      · have : (v i : ℝ) + 1 ≤ (w i : ℝ) := by exact_mod_cast h'
        linarith
      · have : (w i : ℝ) + 1 ≤ (v i : ℝ) := by exact_mod_cast h'
        linarith
    exact_mod_cast this


  have vol_scaled : volume {x : Fin n → ℝ | (fun i => x i / t) ∈ S} =
      ENNReal.ofReal (t ^ n) * volume S := by
    have : {x : Fin n → ℝ | (fun i => x i / t) ∈ S} = t • S := by
      ext x; simp only [mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem₀ ht_ne]
      suffices (fun i => x i / t) = t⁻¹ • x by rw [this]
      ext i; simp [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    rw [this, Measure.addHaar_smul volume t S]
    congr 1; rw [Module.finrank_pi_fintype]
    simp [Module.finrank_self, abs_of_pos (pow_pos ht0 n)]

  have measure_cubes : ∀ (T : Set (Fin n → ℤ)), T.Finite →
      volume (⋃ v ∈ T, unitCube v) = (Nat.card T : ENNReal) := by
    intro T hT; haveI := hT.to_subtype
    rw [measure_biUnion hT.countable
      (fun i hi j hj hij => pd_all (mem_univ i) (mem_univ j) hij)
      (fun v _ => meas_cube v)]
    conv_lhs => arg 1; ext v; rw [vol_cube v.val]
    cases nonempty_fintype T
    simp [mul_one, Nat.card_eq_fintype_card]


  have h_left_ennreal : (Nat.card (innerCubeSet S t) : ENNReal) ≤
      ENNReal.ofReal (t ^ n) * volume S := by
    rw [← measure_cubes _ hfin_inner, ← vol_scaled]
    apply measure_mono
    intro x hx; simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hxv
    exact hv x (fun i => hxv i)
  have left_ineq : (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)).mpr h_left_ennreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith


  have h_right_ennreal : ENNReal.ofReal (t ^ n) * volume S ≤
      (Nat.card (outerCubeSet S t) : ENNReal) := by
    rw [← vol_scaled, ← measure_cubes _ hfin_outer]
    apply measure_mono
    intro x hx; simp only [mem_iUnion, exists_prop]
    exact ⟨fun i => ⌊x i⌋,
      ⟨x, fun i => ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩, hx⟩,
      by simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]; intro i
         exact ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩⟩
  have right_ineq : (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)
      (ENNReal.natCast_ne_top _)).mpr h_right_ennreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith
  exact ⟨left_ineq, right_ineq⟩

theorem preconnected_frontier_inter {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsPreconnected s) {A : Set α}
    (hA : (s ∩ A).Nonempty) (hAc : (s ∩ Aᶜ).Nonempty) :
    (s ∩ frontier A).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : s ⊆ interior A ∪ interior Aᶜ := by
    intro x hx
    by_contra hx_not
    rw [Set.mem_union] at hx_not; push_neg at hx_not
    have hfr : x ∈ frontier A := by
      simp only [frontier, Set.mem_diff]
      refine ⟨?_, hx_not.1⟩
      rw [mem_closure_iff]
      intro U hU hxU
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hx_not.2; apply interior_maximal _ hU hxU
      intro y hy
      simp only [Set.mem_compl_iff]
      intro hyA
      exact absurd (show y ∈ U ∩ A from ⟨hy, hyA⟩) (by rw [hemp]; exact Set.notMem_empty y)
    have : x ∈ s ∩ frontier A := ⟨hx, hfr⟩
    rw [hempty] at this; exact Set.notMem_empty x this
  have h1 : (s ∩ interior A).Nonempty := by
    obtain ⟨x, hxs, hxA⟩ := hA
    rcases hsub hxs with h | h
    · exact ⟨x, hxs, h⟩
    · exact absurd hxA (interior_subset h)
  have h2 : (s ∩ interior Aᶜ).Nonempty := by
    obtain ⟨x, hxs, hxAc⟩ := hAc
    rcases hsub hxs with h | h
    · exact absurd (interior_subset h) hxAc
    · exact ⟨x, hxs, h⟩
  obtain ⟨x, _, hx1, hx2⟩ := hs _ _ isOpen_interior isOpen_interior hsub h1 h2
  exact interior_subset hx2 (interior_subset hx1)

lemma innerCubeSet_subset_outerCubeSet (S : Set (Fin n → ℝ)) (t : ℝ) :
    innerCubeSet S t ⊆ outerCubeSet S t := by
  intro v hv
  simp only [outerCubeSet, Set.mem_setOf_eq]
  have key : ∀ i : Fin n, (v i : ℝ) < (v i : ℝ) + 1 := fun i => lt_add_one _
  exact ⟨fun i => (v i : ℝ), fun i => ⟨le_refl _, key i⟩, hv _ (fun i => ⟨le_refl _, key i⟩)⟩

theorem boundary_cubes_bound {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S)
    (numMaps : ℕ) (maps : Fin numMaps → ((Fin (n-1) → ℝ) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, (maps i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1)))
    (t : ℝ) (ht : 1 ≤ t)
    (hFinOuter : (outerCubeSet S t).Finite)
    (hFinBdry : ∀ i : Fin numMaps, Set.Finite {v : Fin n → ℤ |
      ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1}) :
    (Nat.card (outerCubeSet S t) : ℝ) ≤
    (Nat.card (innerCubeSet S t) : ℝ) +
    ∑ i : Fin numMaps, (Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} : ℝ) := by

  set bdry : Fin numMaps → Set (Fin n → ℤ) :=
    fun i => {v | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} with bdry_def

  suffices h : (outerCubeSet S t).ncard ≤
      (innerCubeSet S t).ncard + ∑ i : Fin numMaps, (bdry i).ncard by
    have := @Nat.cast_le ℝ _ _ _ |>.mpr h
    simp only [Nat.card_coe_set_eq, Nat.cast_add, Nat.cast_sum] at this ⊢
    exact this

  have hInner : innerCubeSet S t ⊆ outerCubeSet S t := innerCubeSet_subset_outerCubeSet S t
  have hFinInner : (innerCubeSet S t).Finite := hFinOuter.subset hInner
  have hFinUnion : (⋃ i, bdry i).Finite := Set.finite_iUnion hFinBdry

  have hDiff : outerCubeSet S t \ innerCubeSet S t ⊆ ⋃ i, bdry i := by
    intro v ⟨hv_outer, hv_not_inner⟩
    simp only [outerCubeSet, Set.mem_setOf_eq] at hv_outer
    simp only [innerCubeSet, Set.mem_setOf_eq] at hv_not_inner
    push_neg at hv_not_inner

    obtain ⟨x, hx_cube, hx_in_S⟩ := hv_outer

    obtain ⟨x', hx'_cube, hx'_not_S⟩ := hv_not_inner

    set cube := {y : Fin n → ℝ | ∀ i, (v i : ℝ) ≤ y i ∧ y i < (v i : ℝ) + 1}
    have hcube_eq : cube = Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1)) := by
      ext y; simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies]
    have hcube_preconn : IsPreconnected cube := by
      rw [hcube_eq]; exact (convex_pi (fun i _ => convex_Ico _ _)).isPreconnected

    set T := {y : Fin n → ℝ | (fun i => y i / t) ∈ S}
    have hx_T : x ∈ cube ∩ T := ⟨hx_cube, hx_in_S⟩
    have hx'_Tc : x' ∈ cube ∩ Tᶜ := ⟨hx'_cube, hx'_not_S⟩

    have hfr := preconnected_frontier_inter hcube_preconn ⟨x, hx_T⟩ ⟨x', hx'_Tc⟩
    obtain ⟨z, hz_cube, hz_frontier⟩ := hfr

    have ht_pos : (0 : ℝ) < t := by linarith
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have hz_on_frontier : (fun i => z i / t) ∈ frontier S := by

      have ht_inv_ne : t⁻¹ ≠ 0 := inv_ne_zero ht_ne
      set φ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := Homeomorph.smulOfNeZero t⁻¹ ht_inv_ne with φ_def
      have hT_eq : T = φ ⁻¹' S := by
        ext y; simp only [T, Set.mem_setOf_eq, Set.mem_preimage, φ_def,
          Homeomorph.smulOfNeZero_apply]
        constructor
        · intro h; convert h using 1; ext i; simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
        · intro h; convert h using 1; ext i; simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
      rw [hT_eq] at hz_frontier
      rw [← φ.preimage_frontier] at hz_frontier
      simp only [Set.mem_preimage, φ_def, Homeomorph.smulOfNeZero_apply] at hz_frontier
      convert hz_frontier using 1
      ext i; simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

    have := hCover hz_on_frontier
    rw [Set.mem_iUnion] at this
    obtain ⟨i, hi⟩ := this
    rw [Set.mem_image] at hi
    obtain ⟨y, hy_mem, hy_eq⟩ := hi

    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    simp only [bdry_def, Set.mem_setOf_eq]
    refine ⟨y, hy_mem, fun j => ?_⟩
    have hjz : (maps i y) j = z j / t := congr_fun hy_eq j
    constructor
    · have := (hz_cube j).1
      rw [hjz, div_eq_inv_mul]
      rw [show t * (t⁻¹ * z j) = z j from by field_simp]
      exact this
    · have := (hz_cube j).2
      rw [hjz, div_eq_inv_mul]
      rw [show t * (t⁻¹ * z j) = z j from by field_simp]
      exact this

  calc (outerCubeSet S t).ncard
      = (innerCubeSet S t ∪ (outerCubeSet S t \ innerCubeSet S t)).ncard := by
        rw [Set.union_diff_cancel hInner]
    _ ≤ (innerCubeSet S t).ncard + (outerCubeSet S t \ innerCubeSet S t).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (innerCubeSet S t).ncard + (⋃ i, bdry i).ncard :=
        Nat.add_le_add_left (Set.ncard_le_ncard hDiff hFinUnion) _
    _ ≤ (innerCubeSet S t).ncard + ∑ i, (bdry i).ncard :=
        Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype bdry) _

theorem lattice_count_upper_sandwich {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S) (hS_vol : volume S ≠ ⊤) (hBdd : Bornology.IsBounded S)
    (numMaps : ℕ) (maps : Fin numMaps → ((Fin (n-1) → ℝ) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, (maps i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1)))
    (t : ℝ) (ht : 1 ≤ t)
    (hFinBdry : ∀ i : Fin numMaps, Set.Finite {v : Fin n → ℤ |
      ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1}) :
    (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) ≤
    (volume S).toReal * t ^ n +
    ∑ i : Fin numMaps, (Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} : ℝ) := by

  have hfin := outerCubeSet_finite hn S hS_meas hBdd t ht
  have h_count_le_outer : (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) ≤
      (Nat.card (outerCubeSet S t) : ℝ) :=
    Nat.cast_le.mpr (Nat.card_mono hfin (lattice_count_subset_outerCubeSet S t))

  have h_bdy := boundary_cubes_bound hn S hS_meas numMaps maps hCover t ht hfin hFinBdry

  have ⟨h_inner_le_vol, _⟩ := cube_measure_sandwich hn S hS_meas hS_vol t ht hfin

  linarith

theorem lattice_count_lower_sandwich {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S) (hS_vol : volume S ≠ ⊤) (hBdd : Bornology.IsBounded S)
    (numMaps : ℕ) (maps : Fin numMaps → ((Fin (n-1) → ℝ) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, (maps i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1)))
    (t : ℝ) (ht : 1 ≤ t)
    (hFinBdry : ∀ i : Fin numMaps, Set.Finite {v : Fin n → ℤ |
      ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1}) :
    (volume S).toReal * t ^ n ≤
    (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) +
    ∑ i : Fin numMaps, (Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} : ℝ) := by

  have hfin := outerCubeSet_finite hn S hS_meas hBdd t ht
  have ⟨_, h_vol_le_outer⟩ := cube_measure_sandwich hn S hS_meas hS_vol t ht hfin

  have h_bdy := boundary_cubes_bound hn S hS_meas numMaps maps hCover t ht hfin hFinBdry

  have h_inner_le_count : (Nat.card (innerCubeSet S t) : ℝ) ≤
      (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) := by
    have hfin_count := hfin.subset (lattice_count_subset_outerCubeSet S t)
    exact Nat.cast_le.mpr (Nat.card_mono hfin_count (innerCubeSet_subset_lattice_count S t))

  linarith

theorem lattice_count_error_bound {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S) (hS_vol : volume S ≠ ⊤) (hBdd : Bornology.IsBounded S)
    (numMaps : ℕ) (maps : Fin numMaps → ((Fin (n-1) → ℝ) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, (maps i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1)))
    (t : ℝ) (ht : 1 ≤ t)
    (hFinBdry : ∀ i : Fin numMaps, Set.Finite {v : Fin n → ℤ |
      ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1}) :
    ‖(Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) -
      (volume S).toReal * t ^ n‖ ≤
    ∑ i : Fin numMaps, (Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} : ℝ) := by
  have h_upper := lattice_count_upper_sandwich hn S hS_meas hS_vol hBdd numMaps maps hCover t ht hFinBdry
  have h_lower := lattice_count_lower_sandwich hn S hS_meas hS_vol hBdd numMaps maps hCover t ht hFinBdry
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem lattice_point_count_asymptotics {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S) (hS_vol : volume S ≠ ⊤)
    (hBdd : Bornology.IsBounded S)
    (hS_bdry : IsLipschitzParametrizable (frontier S) (n - 1)) :
    ∃ C : ℝ, ∀ᶠ t in atTop,
      ‖(Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) -
        (volume S).toReal * t ^ n‖ ≤ C * t ^ (n - 1 : ℕ) := by

  obtain ⟨numMaps, maps, hLip, hCover⟩ := hS_bdry

  have cube_bounds : ∀ i : Fin numMaps, ∃ Ci : ℝ, 0 < Ci ∧ ∀ t : ℝ, 1 ≤ t →
      Nat.card {v : Fin n → ℤ | ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
        ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} ≤
      Ci * t ^ (n - 1) := by
    intro i
    obtain ⟨Ki, hKi⟩ := hLip i
    exact single_lipschitz_image_cube_count (maps i) Ki hKi
  choose Cs _ hCs_bound using cube_bounds
  set C := ∑ i : Fin numMaps, Cs i
  refine ⟨C, ?_⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun t ht => ?_⟩

  have hFinBdry : ∀ i : Fin numMaps, Set.Finite {v : Fin n → ℤ |
      ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
      ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} := by
    intro i
    obtain ⟨Ki, hKi⟩ := hLip i
    exact lipschitz_floor_image_finite (maps i) Ki hKi t ht

  calc ‖(Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) -
        (volume S).toReal * t ^ n‖
      ≤ ∑ i : Fin numMaps, (Nat.card {v : Fin n → ℤ |
          ∃ y ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
          ∀ j, (v j : ℝ) ≤ t * (maps i y) j ∧ t * (maps i y) j < (v j : ℝ) + 1} : ℝ) :=
        lattice_count_error_bound hn S hS_meas hS_vol hBdd numMaps maps hCover t ht hFinBdry
    _ ≤ ∑ i : Fin numMaps, Cs i * t ^ (n - 1) :=
        Finset.sum_le_sum (fun i _ => by exact_mod_cast hCs_bound i t ht)
    _ = C * t ^ (n - 1 : ℕ) := by rw [← Finset.sum_mul]

theorem lattice_count_change_of_basis {n : ℕ} (_hn : 0 < n)
    (S : Set (Fin n → ℝ)) (hS_meas : MeasurableSet S)
    (hS_bdry : IsLipschitzParametrizable (frontier S) (n - 1))
    (Λ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hS_vol : volume S ≠ ⊤ := by exact ENNReal.ofReal_ne_top)
    (hBdd : Bornology.IsBounded S := by exact Bornology.IsBounded.empty) :
    ∃ (S' : Set (Fin n → ℝ)),
      MeasurableSet S' ∧
      IsLipschitzParametrizable (frontier S') (n - 1) ∧
      (∀ t : ℝ, t ≠ 0 →
        (Nat.card {x : Λ | (x : Fin n → ℝ) ∈ (fun v => t • v) '' S} : ℝ) =
        (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S'} : ℝ)) ∧
      ZLattice.covolume Λ * (volume S').toReal = (volume S).toReal ∧
      volume S' ≠ ⊤ ∧
      Bornology.IsBounded S' := by
  set b := IsZLattice.basis Λ
  set e := (b.ofZLatticeBasis ℝ Λ).equivFun
  have equiv_repr : ∀ (x : Λ) (i : Fin n), (b.equivFun x i : ℝ) = ((b.repr x) i : ℝ) := by
    intro x i; simp [Module.Basis.equivFun_apply]
  refine ⟨e '' S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS_meas
  ·

    set h := e.toContinuousLinearEquiv.toHomeomorph with hh_def
    have himg : e '' S = h '' S := rfl
    rw [himg, ← h.image_frontier]
    exact hS_bdry.image_linearEquiv e.toContinuousLinearEquiv

  ·
    intro t ht
    congr 1
    apply Nat.card_congr
    have ekey : ∀ (x : Λ) (i : Fin n), e (↑x) i = ((b.repr x) i : ℝ) := by
      intro x i
      simp only [e, Module.Basis.equivFun_apply, Module.Basis.ofZLatticeBasis_repr_apply]
    refine Equiv.subtypeEquiv b.equivFun.toEquiv ?_
    intro x
    simp only [LinearEquiv.coe_toEquiv, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hxs⟩
      refine ⟨s, hs, ?_⟩
      ext i
      have h3 := congr_fun (show e (↑x) = t • e s by rw [← hxs]; exact map_smul e t s) i
      simp only [Pi.smul_apply, smul_eq_mul] at h3
      rw [equiv_repr]
      rw [show ((b.repr x) i : ℝ) = t * e s i from by rw [← ekey]; exact h3]
      field_simp
    · rintro ⟨s, hs, hes⟩
      refine ⟨s, hs, ?_⟩
      apply e.injective
      rw [map_smul]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      have h1 := ekey x i
      have h2 := congr_fun hes i
      simp only at h2
      rw [h1, ← equiv_repr x i, h2]; field_simp
  ·
    have hvol := ZLattice.volume_image_eq_volume_div_covolume Λ b (s := S)
    have hcov_pos : (0 : ℝ) < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
    rw [hvol, ENNReal.toReal_div, ENNReal.toReal_ofReal (le_of_lt hcov_pos)]
    field_simp
  ·
    have hvol := ZLattice.volume_image_eq_volume_div_covolume Λ b (s := S)
    rw [hvol]
    have hcov_pos : (0 : ℝ) < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
    exact ENNReal.div_ne_top hS_vol (ne_of_gt (ENNReal.ofReal_pos.mpr hcov_pos))
  ·
    exact hBdd.image e.toContinuousLinearEquiv.toContinuousLinearMap

theorem lattice_point_count_general {n : ℕ} (hn : 0 < n)
    (S : Set (Fin n → ℝ)) (hS_meas : MeasurableSet S) (hS_vol : volume S ≠ ⊤)
    (hS_bdry : IsLipschitzParametrizable (frontier S) (n - 1))
    (hBdd : Bornology.IsBounded S)
    (Λ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ C : ℝ, ∀ᶠ t in atTop,
      ‖(Nat.card {x : Λ | (x : Fin n → ℝ) ∈ (fun v => t • v) '' S} : ℝ) -
        (volume S).toReal / (ZLattice.covolume Λ) * t ^ n‖ ≤ C * t ^ (n - 1 : ℕ) := by

  obtain ⟨S', hS'_meas, hS'_bdry, hcount_eq, hvol_eq, hS'_vol, hS'_bdd⟩ :=
    lattice_count_change_of_basis hn S hS_meas hS_bdry Λ hS_vol hBdd

  obtain ⟨C, hC⟩ := lattice_point_count_asymptotics hn S' hS'_meas hS'_vol hS'_bdd hS'_bdry

  refine ⟨C, ?_⟩

  have hC' : ∀ᶠ t in atTop, (1 : ℝ) ≤ t ∧
      ‖(Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S'} : ℝ) -
        (volume S').toReal * t ^ n‖ ≤ C * t ^ (n - 1 : ℕ) := by
    apply Filter.Eventually.and
    · exact Filter.eventually_atTop.mpr ⟨1, fun t ht => ht⟩
    · exact hC
  apply Filter.Eventually.mono hC'
  intro t ⟨ht1, ht⟩
  have ht_ne : t ≠ 0 := by linarith

  rw [hcount_eq t ht_ne]

  have hvol : (volume S').toReal = (volume S).toReal / ZLattice.covolume Λ := by
    have hcov_pos : (0 : ℝ) < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
    field_simp
    linarith [hvol_eq]
  rw [hvol] at ht
  exact ht

section AnalyticClassNumber

variable (K : Type*) [Field K] [NumberField K]



noncomputable def idealToClass (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

noncomputable def toFinME : (NumberField.mixedEmbedding.euclidean.mixedSpace K) ≃ᵐ
    (Fin (Module.finrank ℚ K) → ℝ) := by
  classical
  have hcard : Fintype.card (NumberField.mixedEmbedding.index K) = Module.finrank ℚ K := by
    linarith [NumberField.mixedEmbedding.euclidean.finrank K,
      Module.finrank_eq_card_basis
        (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).toBasis]
  let onb := (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex
    (Fintype.equivFinOfCardEq hcard)
  exact onb.measurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Fin (Module.finrank ℚ K) → ℝ)).symm

end AnalyticClassNumber

section DirichletSeries

theorem LSeriesSummable_of_partial_sum_bound
    (a : ℕ → ℂ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hpartial : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1)‖ ≤ C * (t : ℝ) ^ σ)
    (s : ℂ) (hs : σ + 1 < s.re) : LSeriesSummable a s := by
  obtain ⟨C, hC⟩ := hpartial
  apply LSeriesSummable_of_le_const_mul_rpow hs
  refine ⟨2 * |C|, fun n hn => ?_⟩
  rw [show σ + 1 - 1 = σ from by ring]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn

  have hSn := hC n
  have hSn1 := hC (n - 1)
  have hdecomp : ∑ i ∈ Finset.range n, a (i + 1) =
      ∑ i ∈ Finset.range (n - 1), a (i + 1) + a n := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega, Finset.sum_range_succ]
    simp [Nat.sub_one_add_one_eq_of_pos hn_pos]
  have hbound : ‖a n‖ ≤ ‖∑ i ∈ Finset.range n, a (i + 1)‖ +
      ‖∑ i ∈ Finset.range (n - 1), a (i + 1)‖ := by
    have heq : a n = ∑ i ∈ Finset.range n, a (i + 1) -
        ∑ i ∈ Finset.range (n - 1), a (i + 1) := by
      rw [hdecomp]; ring
    rw [heq]; exact norm_sub_le _ _
  have hn1_le : ((n - 1 : ℕ) : ℝ) ^ σ ≤ (n : ℝ) ^ σ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) hσ
  calc ‖a n‖ ≤ ‖∑ i ∈ Finset.range n, a (i + 1)‖ +
        ‖∑ i ∈ Finset.range (n - 1), a (i + 1)‖ := hbound
    _ ≤ C * (n : ℝ) ^ σ + C * ((n - 1 : ℕ) : ℝ) ^ σ := by linarith [hSn, hSn1]
    _ ≤ |C| * (n : ℝ) ^ σ + |C| * ((n - 1 : ℕ) : ℝ) ^ σ := by
        have h1 : C ≤ |C| := le_abs_self C
        have h2 : (0 : ℝ) ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
        have h3 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg _) σ
        linarith [mul_le_mul_of_nonneg_right h1 h2, mul_le_mul_of_nonneg_right h1 h3]
    _ ≤ |C| * (n : ℝ) ^ σ + |C| * (n : ℝ) ^ σ := by
        linarith [mul_le_mul_of_nonneg_left hn1_le (abs_nonneg C)]
    _ = 2 * |C| * (n : ℝ) ^ σ := by ring

noncomputable def dirichletSeriesAbel (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) *
    (x : ℂ) ^ (-(s + 1))

theorem dirichletSeriesAbel_eq_LSeries (f : ℕ → ℂ) (s : ℂ) (hf : LSeriesSummable f s)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r < s.re)
    (hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[Filter.atTop] fun n => (n : ℝ) ^ r) :
    dirichletSeriesAbel f s = LSeries f s := by

  have h_sum_eq : ∀ N : ℕ, ∑ n ∈ Finset.range N, f (n + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
    intro N
    have h : Finset.Icc 1 N = (Finset.range N).image (· + 1) := by
      ext k; simp [Finset.mem_Icc, Finset.mem_range]; constructor
      · intro ⟨hk1, hk2⟩; exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [h, Finset.sum_image]
    intro a _ b _ hab
    have : a + 1 = b + 1 := hab; omega
  have h_eq : dirichletSeriesAbel f s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) *
        (↑t : ℂ) ^ (-(s + 1)) := by
    unfold dirichletSeriesAbel
    congr 1
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only
    rw [h_sum_eq]

  rw [h_eq, LSeries_eq_mul_integral f hr hrs hf hO]

noncomputable def dirichletSeriesContinuation (a : ℕ → ℂ) (ρ : ℂ) : ℂ → ℂ :=
  fun s => ρ * riemannZeta s + dirichletSeriesAbel (fun n => a n - ρ) s

open Finset in

set_option maxHeartbeats 400000 in

def stepFnAbel (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  if x > 1 then ∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1) else 0

lemma stepFnAbel_eq_zero_of_le_one (f : ℕ → ℂ) {x : ℝ} (hx : x ≤ 1) :
    stepFnAbel f x = 0 := by
  simp [stepFnAbel, not_lt.mpr hx]

lemma stepFnAbel_measurable (f : ℕ → ℂ) : Measurable (stepFnAbel f) := by
  unfold stepFnAbel
  apply Measurable.ite
  · exact measurableSet_Ioi
  · have h1 : Measurable (fun x : ℝ => ⌊x⌋₊) := by measurability
    have h2 : Measurable (fun N : ℕ => ∑ n ∈ Finset.range N, f (n + 1)) :=
      measurable_of_countable _
    show Measurable ((fun N : ℕ => ∑ n ∈ Finset.range N, f (n + 1)) ∘ (fun x : ℝ => ⌊x⌋₊))
    exact h2.comp h1
  · exact measurable_const

theorem stepFnAbel_locallyIntegrableOn (f : ℕ → ℂ) :
    MeasureTheory.LocallyIntegrableOn (stepFnAbel f) (Set.Ioi 0) MeasureTheory.volume := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  refine ⟨Set.Ioo (x / 2) (x + 1), ?_, ?_⟩
  · apply nhdsWithin_le_nhds
    exact Ioo_mem_nhds (by linarith) (by linarith)
  · set M := ∑ n ∈ Finset.range (⌊x⌋₊ + 2), ‖f (n + 1)‖
    apply MeasureTheory.Measure.integrableOn_of_bounded (M := M)
    · exact ne_top_of_le_ne_top (ne_of_lt isCompact_Icc.measure_lt_top)
        (MeasureTheory.measure_mono Set.Ioo_subset_Icc_self)
    · exact (stepFnAbel_measurable f).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      apply Filter.Eventually.of_forall
      intro y hy
      simp only [stepFnAbel]
      split_ifs with h
      · apply le_trans (norm_sum_le _ _)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_range] at hn ⊢
          have h1 : ⌊y⌋₊ ≤ ⌊x + 1⌋₊ := Nat.floor_le_floor (le_of_lt hy.2)
          rw [Nat.floor_add_one (by linarith : (0 : ℝ) ≤ x)] at h1
          omega
        · intro n _ _; exact norm_nonneg _
      · simp
        exact Finset.sum_nonneg (fun n _ => norm_nonneg _)

lemma rpow_anti_base {x y σ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hσ : σ ≤ 0) :
    y ^ σ ≤ x ^ σ := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [show σ = -(-σ) from by ring, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy (by linarith))

lemma floor_rpow_le (x σ : ℝ) (hx : 2 ≤ x) :
    (⌊x⌋₊ : ℝ) ^ σ ≤ 2 ^ |σ| * x ^ σ := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hfloor_pos : (0 : ℝ) < ⌊x⌋₊ := by
    exact_mod_cast Nat.pos_of_ne_zero
      (by have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (show (1:ℝ) ≤ x by linarith)); omega)
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfloor_ge_half : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x; linarith
  by_cases hσ : 0 ≤ σ
  · calc (⌊x⌋₊ : ℝ) ^ σ
        ≤ x ^ σ := Real.rpow_le_rpow hfloor_pos.le hfloor_le hσ
      _ ≤ 2 ^ |σ| * x ^ σ := le_mul_of_one_le_left (Real.rpow_nonneg hx_pos.le _)
          (by calc (1:ℝ) = 1 ^ |σ| := (Real.one_rpow |σ|).symm
                _ ≤ 2 ^ |σ| := Real.rpow_le_rpow (by norm_num) (by norm_num) (abs_nonneg σ))
  · push_neg at hσ
    have h1 : (⌊x⌋₊ : ℝ) ^ σ ≤ (x / 2) ^ σ :=
      rpow_anti_base (by linarith : 0 < x / 2) hfloor_ge_half hσ.le
    rw [Real.div_rpow hx_pos.le (by norm_num : (0:ℝ) ≤ 2)] at h1
    rw [abs_of_neg hσ]
    calc (⌊x⌋₊ : ℝ) ^ σ ≤ x ^ σ / (2 : ℝ) ^ σ := h1
      _ = x ^ σ * ((2 : ℝ) ^ σ)⁻¹ := div_eq_mul_inv _ _
      _ = x ^ σ * (2 : ℝ) ^ (-σ) := by rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (-σ) * x ^ σ := mul_comm _ _

theorem stepFnAbel_isBigO_atTop (f : ℕ → ℂ) (σ : ℝ)
    (hf : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, f (i + 1)‖ ≤ C * (t : ℝ) ^ σ) :
    stepFnAbel f =O[Filter.atTop] fun x => x ^ σ := by
  obtain ⟨C, hC⟩ := hf
  rw [Asymptotics.isBigO_iff]
  refine ⟨|C| * 2 ^ |σ|, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hx_pos : (0 : ℝ) < x := by linarith
  rw [Real.norm_rpow_of_nonneg hx_pos.le, Real.norm_of_nonneg hx_pos.le]
  have hx1 : (1 : ℝ) < x := by linarith
  simp only [stepFnAbel, if_pos hx1]
  calc ‖∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)‖
      ≤ C * (⌊x⌋₊ : ℝ) ^ σ := hC ⌊x⌋₊
    _ ≤ |C| * (⌊x⌋₊ : ℝ) ^ σ := by
        apply mul_le_mul_of_nonneg_right (le_abs_self C)
          (Real.rpow_nonneg (by positivity) _)
    _ ≤ |C| * (2 ^ |σ| * x ^ σ) := by
        apply mul_le_mul_of_nonneg_left (floor_rpow_le x σ hx) (abs_nonneg C)
    _ = |C| * 2 ^ |σ| * x ^ σ := by ring

theorem stepFnAbel_isBigO_nhds_zero (f : ℕ → ℂ) (b : ℝ) :
    stepFnAbel f =O[nhdsWithin 0 (Set.Ioi 0)] fun x => x ^ (-b) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioi 0 ∩ Set.Iio 1, ?_, ?_⟩
  · apply inter_mem_nhdsWithin
    exact Iio_mem_nhds one_pos
  · intro x ⟨_, hx_lt⟩
    rw [stepFnAbel_eq_zero_of_le_one f (le_of_lt hx_lt)]
    simp

lemma mellin_integrand_eq_indicator (f : ℕ → ℂ) (s : ℂ) (x : ℝ) :
    (x : ℂ) ^ (-s - 1) • stepFnAbel f x =
    Set.indicator (Set.Ioi (1:ℝ))
      (fun x => (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) * (x : ℂ) ^ (-(s + 1))) x := by
  by_cases hx : 1 < x
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hx), stepFnAbel, if_pos hx, smul_eq_mul,
      mul_comm]
    congr 1; ring
  · push_neg at hx
    have : x ∉ Set.Ioi (1 : ℝ) := by rwa [Set.mem_Ioi, not_lt]
    rw [Set.indicator_apply_eq_zero.mpr (fun h => absurd h this)]
    simp [stepFnAbel_eq_zero_of_le_one f hx]

theorem mellin_stepFnAbel_eq (f : ℕ → ℂ) (s : ℂ) :
    mellin (stepFnAbel f) (-s) =
      ∫ x in Set.Ioi (1 : ℝ),
        (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) * (x : ℂ) ^ (-(s + 1)) := by
  simp only [mellin]
  simp_rw [mellin_integrand_eq_indicator f s]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  congr 1
  ext x
  simp [Set.Ioi_inter_Ioi]

theorem dirichletSeriesAbel_integral_differentiableOn
    (f : ℕ → ℂ) (σ : ℝ)
    (hf : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, f (i + 1)‖ ≤ C * (t : ℝ) ^ σ) :
    DifferentiableOn ℂ
      (fun s => ∫ x in Set.Ioi (1 : ℝ),
        (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) * (x : ℂ) ^ (-(s + 1)))
      {s : ℂ | σ < s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_setOf_eq] at hs₀
  suffices h : DifferentiableWithinAt ℂ (fun s => mellin (stepFnAbel f) (-s))
      {s : ℂ | σ < s.re} s₀ by
    apply h.congr
    · intro s hs
      simp only [Set.mem_setOf_eq] at hs
      exact (mellin_stepFnAbel_eq f s).symm
    · exact (mellin_stepFnAbel_eq f s₀).symm
  apply DifferentiableAt.differentiableWithinAt
  have hD : DifferentiableAt ℂ (mellin (stepFnAbel f)) (-s₀) := by
    apply @mellin_differentiableAt_of_isBigO_rpow ℂ _ _ (-σ) (-s₀.re - 1)
      (stepFnAbel f) (-s₀)
    · exact stepFnAbel_locallyIntegrableOn f
    · simp only [neg_neg]; exact stepFnAbel_isBigO_atTop f σ hf
    · simp [Complex.neg_re]; linarith
    · exact stepFnAbel_isBigO_nhds_zero f (-s₀.re - 1)
    · simp [Complex.neg_re]
  exact hD.comp s₀ differentiableAt_id.neg

theorem LSeries_analyticOnNhd_of_partialSum_le
    (f : ℕ → ℂ) (σ : ℝ)
    (hf : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, f (i + 1)‖ ≤ C * (t : ℝ) ^ σ) :
    AnalyticOnNhd ℂ (dirichletSeriesAbel f) {s : ℂ | σ < s.re} := by

  have hopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re

  apply DifferentiableOn.analyticOnNhd _ hopen

  intro s₀ hs₀
  simp only [Set.mem_setOf_eq] at hs₀
  apply DifferentiableAt.differentiableWithinAt

  unfold dirichletSeriesAbel
  apply DifferentiableAt.mul differentiableAt_id

  have hD := dirichletSeriesAbel_integral_differentiableOn f σ hf
  exact (hD s₀ hs₀).differentiableAt (hopen.mem_nhds hs₀)

theorem dirichlet_series_remainder_holomorphic
    (a : ℕ → ℂ) (σ : ℝ) (ρ : ℂ)
    (hasympt : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * t‖ ≤
      C * (t : ℝ) ^ σ) :
    AnalyticOnNhd ℂ (dirichletSeriesAbel (fun n => a n - ρ)) {s : ℂ | σ < s.re} := by


  apply LSeries_analyticOnNhd_of_partialSum_le
  obtain ⟨C, hC⟩ := hasympt
  refine ⟨C, fun t => ?_⟩

  have : ∑ i ∈ Finset.range t, (fun n => a n - ρ) (i + 1) =
      ∑ i ∈ Finset.range t, a (i + 1) - ρ * t := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  rw [this]; exact hC t

theorem dirichlet_series_meromorphic_continuation
    (a : ℕ → ℂ) (σ : ℝ) (_hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (ρ : ℂ) (_hρ : ρ ≠ 0)
    (hasympt : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * t‖ ≤
      C * (t : ℝ) ^ σ) :

    Tendsto (fun s : ℝ ↦ (↑s - 1) * dirichletSeriesContinuation a ρ (↑s))
      (𝓝[>] 1) (𝓝 ρ) := by

  suffices hmain : Tendsto
      (fun s : ℝ => ρ * (((↑s : ℂ) - 1) * riemannZeta ↑s) +
        ((↑s : ℂ) - 1) * dirichletSeriesAbel (fun n => a n - ρ) ↑s)
      (𝓝[>] 1) (nhds ρ) by
    exact hmain.congr (fun s => by simp only [dirichletSeriesContinuation]; ring)

  have hzeta : Tendsto (fun s : ℝ => ((↑s : ℂ) - 1) * riemannZeta ↑s)
      (𝓝[>] (1 : ℝ)) (nhds 1) := by
    have hmap : Tendsto (fun s : ℝ => (↑s : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with s hs; exact Complex.ofReal_ne_one.mpr hs)
    exact (riemannZeta_residue_one.comp hmap).mono_left
      (nhdsWithin_mono _ (fun s hs => hs.ne'))

  have hrem : Tendsto (fun s : ℝ => ((↑s : ℂ) - 1) * dirichletSeriesAbel (fun n => a n - ρ) ↑s)
      (𝓝[>] (1 : ℝ)) (nhds 0) := by
    have hrem_anal : AnalyticOnNhd ℂ (dirichletSeriesAbel (fun n => a n - ρ)) {s : ℂ | σ < s.re} :=
      dirichlet_series_remainder_holomorphic a σ ρ hasympt

    have h1mem : (1 : ℂ) ∈ {s : ℂ | σ < s.re} := by simp [hσ1]
    have hgcont : Tendsto (fun s : ℝ => dirichletSeriesAbel (fun n => a n - ρ) (↑s : ℂ))
        (𝓝[>] (1 : ℝ)) (nhds (dirichletSeriesAbel (fun n => a n - ρ) (1 : ℂ))) :=
      ((hrem_anal 1 h1mem).continuousAt.tendsto.comp
        (continuous_ofReal.tendsto (1 : ℝ))).mono_left nhdsWithin_le_nhds
    have hzero : Tendsto (fun s : ℝ => ((↑s : ℂ) - 1)) (𝓝[>] (1 : ℝ)) (nhds 0) := by
      rw [show (0 : ℂ) = ((1 : ℝ) : ℂ) - 1 from by push_cast; ring]
      exact ((continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).sub
        tendsto_const_nhds
    rw [show (0 : ℂ) = 0 * dirichletSeriesAbel (fun n => a n - ρ) (1 : ℂ) from by ring]
    exact hzero.mul hgcont

  have := (hzeta.const_mul ρ).add hrem
  simp only [mul_one, add_zero] at this; exact this

lemma riemannZeta_analyticAt {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt
    (fun z (hz : z ∈ {w : ℂ | w ≠ 1}) =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_ne.mem_nhds hs)

lemma riemannZeta_meromorphicAt_one : MeromorphicAt riemannZeta 1 := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  set f : ℂ → ℂ := fun z ↦ (z - 1) * riemannZeta z
  have hf_tendsto : Tendsto f (𝓝[≠] 1) (𝓝 1) := riemannZeta_residue_one
  have hf_diff : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ f z :=
    fun z hz ↦ (differentiableAt_id.sub (differentiableAt_const _)).mul
      (differentiableAt_riemannZeta hz)
  obtain ⟨s, hs_mem, hs_bdd⟩ : ∃ s ∈ 𝓝 (1 : ℂ), BddAbove (norm ∘ f '' (s \ {1})) := by
    rw [Metric.tendsto_nhdsWithin_nhds] at hf_tendsto
    obtain ⟨δ, hδ_pos, hδ⟩ := hf_tendsto 1 one_pos
    refine ⟨Metric.ball 1 δ, Metric.ball_mem_nhds 1 hδ_pos, ?_⟩
    rw [bddAbove_def]
    refine ⟨‖(1 : ℂ)‖ + 1, ?_⟩
    intro x hx
    simp only [mem_image, mem_diff, mem_singleton_iff, Function.comp_apply] at hx
    obtain ⟨z, ⟨hz_ball, hz_ne⟩, rfl⟩ := hx
    have hne : z ∈ ({1} : Set ℂ)ᶜ := mem_compl_singleton_iff.mpr hz_ne
    have hdist := hδ hne (Metric.mem_ball.mp hz_ball)
    have : ‖f z - 1‖ < 1 := by rwa [← dist_eq_norm]
    calc ‖f z‖ = ‖1 + (f z - 1)‖ := by ring_nf
    _ ≤ ‖(1 : ℂ)‖ + ‖f z - 1‖ := norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + 1 := by linarith
  have hf_diffOn : DifferentiableOn ℂ f (s \ {1}) :=
    fun z ⟨_, hz_ne⟩ ↦ (hf_diff z (mem_compl_singleton_iff.mp hz_ne)).differentiableWithinAt
  have hg := differentiableOn_update_limUnder_of_bddAbove hs_mem hf_diffOn hs_bdd
  have hlim : limUnder (𝓝[≠] (1 : ℂ)) f = 1 := hf_tendsto.limUnder_eq
  rw [hlim] at hg
  have hg_analytic : AnalyticAt ℂ (Function.update f 1 1) 1 :=
    (hg.analyticAt hs_mem)
  refine ⟨-1, Function.update f 1 1, hg_analytic, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [mem_compl_iff, mem_singleton_iff] at hz
  simp only [Function.update_of_ne hz, zpow_neg_one, smul_eq_mul]
  rw [inv_mul_cancel_left₀ (sub_ne_zero.mpr hz)]

theorem dirichlet_series_meromorphicOn
    (a : ℕ → ℂ) (σ : ℝ) (_hσ : 0 ≤ σ) (_hσ1 : σ < 1)
    (ρ : ℂ) (_hρ : ρ ≠ 0)
    (hasympt : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * t‖ ≤
      C * (t : ℝ) ^ σ) :
    MeromorphicOn (dirichletSeriesContinuation a ρ) {s : ℂ | ↑σ < s.re} := by
  have hrem : AnalyticOnNhd ℂ (dirichletSeriesAbel (fun n => a n - ρ)) {s : ℂ | ↑σ < s.re} :=
    dirichlet_series_remainder_holomorphic a σ ρ hasympt
  intro s hs
  by_cases hs_ne : s = 1
  ·
    subst hs_ne; unfold dirichletSeriesContinuation
    exact ((analyticAt_const.meromorphicAt.smul riemannZeta_meromorphicAt_one).congr
      Filter.EventuallyEq.rfl).add (hrem 1 hs).meromorphicAt
  ·
    exact ((analyticAt_const.mul (riemannZeta_analyticAt hs_ne)).add
      (hrem s hs)).meromorphicAt

theorem dirichlet_series_analyticAt_off_pole
    (a : ℕ → ℂ) (σ : ℝ) (ρ : ℂ)
    (hasympt : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * t‖ ≤
      C * (t : ℝ) ^ σ) :
    ∀ s : ℂ, s ∈ {s : ℂ | ↑σ < s.re} → s ≠ 1 →
      AnalyticAt ℂ (dirichletSeriesContinuation a ρ) s := by
  intro s hs hs_ne; unfold dirichletSeriesContinuation
  exact (analyticAt_const.mul (riemannZeta_analyticAt hs_ne)).add
    (dirichlet_series_remainder_holomorphic a σ ρ hasympt s hs)

lemma riemannZeta_order_witness :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (1 : ℂ), riemannZeta z = (z - 1) ^ (-1 : ℤ) • g z := by
  set f : ℂ → ℂ := fun z ↦ (z - 1) * riemannZeta z
  have hf_tendsto : Tendsto f (𝓝[≠] 1) (𝓝 1) := riemannZeta_residue_one
  have hf_diff : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ f z :=
    fun z hz ↦ (differentiableAt_id.sub (differentiableAt_const _)).mul
      (differentiableAt_riemannZeta hz)
  obtain ⟨s, hs_mem, hs_bdd⟩ : ∃ s ∈ 𝓝 (1 : ℂ), BddAbove (norm ∘ f '' (s \ {1})) := by
    rw [Metric.tendsto_nhdsWithin_nhds] at hf_tendsto
    obtain ⟨δ, hδ_pos, hδ⟩ := hf_tendsto 1 one_pos
    refine ⟨Metric.ball 1 δ, Metric.ball_mem_nhds 1 hδ_pos, ?_⟩
    rw [bddAbove_def]
    refine ⟨‖(1 : ℂ)‖ + 1, ?_⟩
    intro x hx
    simp only [mem_image, mem_diff, mem_singleton_iff, Function.comp_apply] at hx
    obtain ⟨z, ⟨hz_ball, hz_ne⟩, rfl⟩ := hx
    have hne : z ∈ ({1} : Set ℂ)ᶜ := mem_compl_singleton_iff.mpr hz_ne
    have hdist := hδ hne (Metric.mem_ball.mp hz_ball)
    have : ‖f z - 1‖ < 1 := by rwa [← dist_eq_norm]
    calc ‖f z‖ = ‖1 + (f z - 1)‖ := by ring_nf
    _ ≤ ‖(1 : ℂ)‖ + ‖f z - 1‖ := norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + 1 := by linarith
  have hf_diffOn : DifferentiableOn ℂ f (s \ {1}) :=
    fun z ⟨_, hz_ne⟩ ↦ (hf_diff z (mem_compl_singleton_iff.mp hz_ne)).differentiableWithinAt
  have hg := differentiableOn_update_limUnder_of_bddAbove hs_mem hf_diffOn hs_bdd
  have hlim : limUnder (𝓝[≠] (1 : ℂ)) f = 1 := hf_tendsto.limUnder_eq
  rw [hlim] at hg
  refine ⟨Function.update f 1 1, hg.analyticAt hs_mem, ?_, ?_⟩
  · rw [Function.update_self]; exact one_ne_zero
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz
    simp only [Function.update_of_ne hz, zpow_neg_one, smul_eq_mul, f]
    rw [inv_mul_cancel_left₀ (sub_ne_zero.mpr hz)]

theorem dirichlet_series_residue_complex
    (a : ℕ → ℂ) (σ : ℝ) (_hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (ρ : ℂ) (_hρ : ρ ≠ 0)
    (hasympt : ∃ C : ℝ, ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * t‖ ≤
      C * (t : ℝ) ^ σ) :
    Tendsto (fun s : ℂ => (s - 1) * dirichletSeriesContinuation a ρ s)
      (𝓝[≠] 1) (𝓝 ρ) := by
  suffices hmain : Tendsto
      (fun s : ℂ => ρ * ((s - 1) * riemannZeta s) +
        (s - 1) * dirichletSeriesAbel (fun n => a n - ρ) s)
      (𝓝[≠] 1) (nhds ρ) by
    exact hmain.congr (fun s => by simp only [dirichletSeriesContinuation]; ring)

  have hzeta : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] (1 : ℂ)) (nhds 1) := riemannZeta_residue_one

  have hrem : AnalyticOnNhd ℂ (dirichletSeriesAbel (fun n => a n - ρ)) {s : ℂ | ↑σ < s.re} :=
    dirichlet_series_remainder_holomorphic a σ ρ hasympt
  have h1mem : (1 : ℂ) ∈ {s : ℂ | ↑σ < s.re} := by simp [hσ1]
  have hgcont : Tendsto (dirichletSeriesAbel (fun n => a n - ρ))
      (𝓝[≠] (1 : ℂ)) (nhds (dirichletSeriesAbel (fun n => a n - ρ) 1)) :=
    ((hrem 1 h1mem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun s : ℂ => (s - 1)) (𝓝[≠] (1 : ℂ)) (nhds 0) := by
    rw [show (0 : ℂ) = (1 : ℂ) - 1 from by ring]
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds
  have hrem_lim : Tendsto (fun s : ℂ => (s - 1) * dirichletSeriesAbel (fun n => a n - ρ) s)
      (𝓝[≠] (1 : ℂ)) (nhds 0) := by
    rw [show (0 : ℂ) = 0 * dirichletSeriesAbel (fun n => a n - ρ) 1 from by ring]
    exact hzero.mul hgcont

  have := (hzeta.const_mul ρ).add hrem_lim
  simp only [mul_one, add_zero] at this; exact this

end DirichletSeries

section ACNF

variable (K : Type*) [Field K] [NumberField K]




end ACNF

section Cyclotomic

def IsUnramifiedAtPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 K)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1

def pFreePart (m p : ℕ) : ℕ := m / p ^ padicValNat p m

lemma pFreePart_pos {m : ℕ} (hm : 0 < m) (p : ℕ) : 0 < pFreePart m p := by
  unfold pFreePart
  apply Nat.div_pos (Nat.le_of_dvd hm pow_padicValNat_dvd)
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [padicValNat]
  · exact Nat.pos_of_ne_zero (by positivity)

instance pFreePart_neZero {m : ℕ} [NeZero m] (p : ℕ) : NeZero (pFreePart m p) :=
  ⟨(pFreePart_pos (NeZero.pos m) p).ne'⟩

lemma pFreePart_dvd (m p : ℕ) : pFreePart m p ∣ m := by
  unfold pFreePart
  exact Nat.div_dvd_of_dvd pow_padicValNat_dvd

lemma not_dvd_pFreePart {m : ℕ} (hm : 0 < m) (p : ℕ) (hp : Nat.Prime p) :
    ¬(p ∣ pFreePart m p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hm' : m / p ^ padicValNat p m ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hm pow_padicValNat_dvd) (pow_pos hp.pos _)).ne'
  have h1 : padicValNat p (m / p ^ padicValNat p m) = 0 := by
    rw [padicValNat.div_pow pow_padicValNat_dvd]; omega
  rw [padicValNat.eq_zero_iff] at h1
  rcases h1 with h1 | h1 | h1
  · exact absurd h1 hp.ne_one
  · exact absurd h1 hm'
  · exact h1

theorem isUnramifiedAtPrime_of_le
    (m : ℕ) [NeZero m] (p : ℕ)
    (E E' : IntermediateField ℚ (CyclotomicField m ℚ))
    (hle : E ≤ E')
    (hE' : IsUnramifiedAtPrime E' p) :
    IsUnramifiedAtPrime E p := by

  intro P hPprime hPover

  letI : Algebra ↥E ↥E' := (IntermediateField.inclusion hle).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 ↥E) (𝓞 ↥E') :=
    RingOfIntegers.extension_algebra_isIntegral ↥E ↥E'

  obtain ⟨Q, _, hQprime, hQover⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 ↥E') P ⊥
      (Ideal.comap_bot_le_of_injective _ (RingOfIntegers.algebraMap.injective ↥E ↥E'))
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver P := Ideal.LiesOver.mk hQover.symm

  haveI hQp : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans Q P (Ideal.span {(p : ℤ)})

  have hQ1 : Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q = 1 := @hE' Q hQprime hQp

  have htower := Ideal.ramificationIdx_algebra_tower' (Ideal.span {(p : ℤ)}) P Q

  rw [hQ1] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

lemma cyclotomic_ppow_unramified_at_other_primes
    (m : ℕ) [NeZero m] (p : ℕ) (hp : Nat.Prime p)
    (E₁ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁]
    (q : ℕ) (hq : Nat.Prime q) (hqp : q ≠ p) :
    IsUnramifiedAtPrime E₁ q := by
  intro P hPprime hPover
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPover
  haveI : NeZero (p ^ padicValNat p m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hqdvd : ¬ q ∣ p ^ padicValNat p m := by
    intro h
    have : q ∣ p := hq.dvd_of_dvd_pow h
    rcases hp.eq_one_or_self_of_dvd q this with h1 | h1
    · exact hq.one_lt.ne' h1
    · exact hqp h1
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
    (m := p ^ padicValNat p m) q E₁ P hqdvd

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
lemma minkowski_no_unramified_extension
    (m : ℕ) [NeZero m]
    (F : IntermediateField ℚ (CyclotomicField m ℚ))
    (hF : ∀ (q : ℕ), Nat.Prime q → IsUnramifiedAtPrime F q) :
    F = ⊥ := by
  by_contra hFne

  have hrank : 1 < Module.finrank ℚ F := by
    refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', ?_⟩
    rwa [ne_eq, IntermediateField.finrank_eq_one_iff]

  have hdisc : 2 < |discr F| := abs_discr_gt_two hrank

  have hdiff_norm : (differentIdeal ℤ (𝓞 F)).absNorm = (discr F).natAbs :=
    absNorm_differentIdeal F (𝓞 F)

  have hdiff_ne_top : differentIdeal ℤ (𝓞 F) ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hdiff_norm
    have h1 : (discr F).natAbs = 1 := hdiff_norm.symm
    have h2 : |discr F| = ↑(discr F).natAbs := Int.abs_eq_natAbs _
    linarith

  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hdiff_ne_top
  haveI : M.IsPrime := hMmax.isPrime

  have hMdvd : M ∣ differentIdeal ℤ (𝓞 F) := Ideal.dvd_iff_le.mpr hle

  have hMne : M ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hMmax (RingOfIntegers.not_isField F)

  have hram : ¬ Algebra.IsUnramifiedAt ℤ M := dvd_differentIdeal_iff.mp hMdvd

  have hram2 : ¬ ((M.under ℤ).ramificationIdx M = 1) := by
    rwa [← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hMne]

  have hunder_ne_bot : M.under ℤ ≠ ⊥ :=
    fun h => hMne (Ideal.eq_bot_of_comap_eq_bot h)
  have hunder_prime : (M.under ℤ).IsPrime := Ideal.IsPrime.under ℤ M

  rw [Ideal.isPrime_int_iff] at hunder_prime
  obtain (hbot | ⟨q, hq, heq⟩) := hunder_prime
  · exact hunder_ne_bot hbot

  have hMover : M.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.mk heq.symm
  have := hF q hq M hMover

  rw [heq] at hram2
  exact hram2 this

theorem cyclotomic_ppow_unramified_le_bot
    (m : ℕ) [NeZero m] (p : ℕ) (hp : Nat.Prime p)
    (E₁ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁]
    (F : IntermediateField ℚ (CyclotomicField m ℚ))
    (hFE₁ : F ≤ E₁)
    (hF : IsUnramifiedAtPrime F p) :
    F = ⊥ := by


  apply minkowski_no_unramified_extension
  intro q hq
  by_cases hqp : q = p
  · rwa [hqp]
  · exact isUnramifiedAtPrime_of_le m q F E₁ hFE₁
      (cyclotomic_ppow_unramified_at_other_primes m p hp E₁ q hq hqp)




noncomputable instance cyclotomicSubgroupModular (m : ℕ) [NeZero m] :
    IsModularLattice (Subgroup (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  have hm : 0 < m := NeZero.pos m
  have hirr := Polynomial.cyclotomic.irreducible_rat hm
  have oi := (IsCyclotomicExtension.autEquivPow (CyclotomicField m ℚ) hirr).mapSubgroup
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (oi y) (oi.le_iff_le.mpr hxz)
  rw [← oi.map_sup, ← oi.map_inf, ← oi.map_inf, ← oi.map_sup] at h
  exact oi.le_iff_le.mp h

noncomputable instance cyclotomicIntermediateFieldModular (m : ℕ) [NeZero m] :
    IsModularLattice (IntermediateField ℚ (CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  haveI : IsGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  have e := IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := CyclotomicField m ℚ)
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (e y) (e.le_iff_le.mpr hxz)
  rw [← e.map_sup, ← e.map_inf, ← e.map_inf, ← e.map_sup] at h
  exact e.le_iff_le.mp h

theorem cyclotomic_coprime_sup_eq_top
    (m : ℕ) [NeZero m] (p : ℕ) (hp : Nat.Prime p)
    (E₀ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {pFreePart m p} ℚ E₀]
    (E₁ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁] :
    E₀ ⊔ E₁ = ⊤ := by

  haveI hne0 : NeZero (pFreePart m p) := pFreePart_neZero p
  haveI hne1 : NeZero (p ^ padicValNat p m) :=
    ⟨(pow_pos hp.pos _).ne'⟩

  have hcop : Nat.Coprime (pFreePart m p) (p ^ padicValNat p m) :=
    hp.coprime_pow_of_not_dvd (not_dvd_pFreePart (NeZero.pos m) p hp)

  have hlcm : Nat.lcm (pFreePart m p) (p ^ padicValNat p m) = m := by
    rw [hcop.lcm_eq_mul]
    exact Nat.div_mul_cancel pow_padicValNat_dvd

  have h_sup_cyc : IsCyclotomicExtension
      ({Nat.lcm (pFreePart m p) (p ^ padicValNat p m)} : Set ℕ) ℚ
      ↥(E₀ ⊔ E₁) :=
    @IntermediateField.isCyclotomicExtension_lcm_sup ℚ (CyclotomicField m ℚ) _ _ _
      (pFreePart m p) (p ^ padicValNat p m) E₀ E₁
      ‹IsCyclotomicExtension {pFreePart m p} ℚ E₀›
      ‹IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁›
      hne0 hne1

  rw [hlcm] at h_sup_cyc

  have h_top_cyc : IsCyclotomicExtension ({m} : Set ℕ) ℚ
      (⊤ : IntermediateField ℚ (CyclotomicField m ℚ)) := by
    haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
      CyclotomicField.isCyclotomicExtension m ℚ
    exact IsCyclotomicExtension.equiv _ ℚ _ IntermediateField.topEquiv.symm

  exact @IntermediateField.isCyclotomicExtension_eq ({m} : Set ℕ) ℚ (CyclotomicField m ℚ) _ _ _
    (E₀ ⊔ E₁) ⊤ h_sup_cyc h_top_cyc

theorem cyclotomic_coprime_nontrivial_ext
    (m : ℕ) [NeZero m] (p : ℕ) (hp : Nat.Prime p)
    (E₀ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {pFreePart m p} ℚ E₀]
    (E₁ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁]
    (F : IntermediateField ℚ (CyclotomicField m ℚ))
    (hE₀F : E₀ < F) :
    F ⊓ E₁ ≠ ⊥ := by
  have hsup := cyclotomic_coprime_sup_eq_top m p hp E₀ E₁
  intro h
  have hle : E₀ ≤ F := le_of_lt hE₀F
  have key := sup_inf_assoc_of_le E₁ hle
  rw [hsup, top_inf_eq] at key
  rw [inf_comm] at h
  rw [h, sup_bot_eq] at key
  exact lt_irrefl F (key ▸ hE₀F)






instance instNeZeroCastRat (m : ℕ) [NeZero m] : NeZero (m : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩

instance instIsCyclotomicExtensionCyclotomicField (m : ℕ) [NeZero m] :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

noncomputable def subgroupDualOrderIso (G : Type*) [CommGroup G] [Finite G] :
    Subgroup G ≃o (Subgroup (G →* ℂˣ))ᵒᵈ :=
  CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ

noncomputable abbrev prop_18_40 := @subgroupDualOrderIso

set_option backward.isDefEq.respectTransparency false in
theorem subgroup_dual_annihilator_mem (G : Type*) [CommGroup G] [Finite G]
    (K : Subgroup (G →* ℂˣ)) (g : G) :
    g ∈ (subgroupDualOrderIso G).symm (OrderDual.toDual K) ↔ ∀ χ ∈ K, χ g = 1 :=
  CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff ℂ K g

set_option backward.isDefEq.respectTransparency false in

theorem subgroup_dual_card_annihilator (G : Type*) [CommGroup G] [Fintype G] (H : Subgroup G) :
    Nat.card H * Nat.card (MonoidHom.restrictHom H ℂˣ).ker = Nat.card G := by
  have hsurj := MonoidHom.restrict_surjective (G := G) ℂ H
  have hcard_G : Nat.card (G →* ℂˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have hcard_H : Nat.card (↥H →* ℂˣ) = Nat.card ↥H :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥H ℂ
  have hlagrange := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MonoidHom.restrictHom H ℂˣ).ker
  have hquot : Nat.card ((G →* ℂˣ) ⧸ (MonoidHom.restrictHom H ℂˣ).ker) = Nat.card (↥H →* ℂˣ) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [← hcard_G, hlagrange, hquot, hcard_H]

abbrev prop_18_40_card := @subgroup_dual_card_annihilator

set_option backward.isDefEq.respectTransparency false in
theorem subgroup_dual_card_dual_annihilator (G : Type*) [CommGroup G] [Fintype G]
    (K : Subgroup (G →* ℂˣ)) :
    Nat.card K * Nat.card ((subgroupDualOrderIso G).symm (OrderDual.toDual K)) = Nat.card G := by
  haveI heru : HasEnoughRootsOfUnity ℂ (Monoid.exponent (G →* ℂˣ)) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ
    rw [Monoid.exponent_eq_of_mulEquiv e]; infer_instance
  let ddi := CommGroup.monoidHomMonoidHomEquiv G ℂ
  have hcard_psi : Nat.card ((subgroupDualOrderIso G).symm (OrderDual.toDual K)) =
      Nat.card (MonoidHom.restrictHom K ℂˣ).ker :=
    Nat.card_congr (MulEquiv.subgroupMap ddi _).toEquiv.symm
  rw [hcard_psi]
  have hsurj := MonoidHom.restrict_surjective (G := G →* ℂˣ) ℂ K
  have hcard_dd : Nat.card ((G →* ℂˣ) →* ℂˣ) = Nat.card G := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G →* ℂˣ) ℂ,
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ]
  haveI : NeZero (Monoid.exponent (G →* ℂˣ)) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ
    rw [Monoid.exponent_eq_of_mulEquiv e]
    exact ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent ↥K) :=
    heru.of_dvd ℂ (Monoid.exponent_submonoid_dvd K.toSubmonoid)
  have hcard_K_dual : Nat.card (↥K →* ℂˣ) = Nat.card ↥K :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥K ℂ
  have hlagrange := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MonoidHom.restrictHom K ℂˣ).ker
  have hquot : Nat.card (((G →* ℂˣ) →* ℂˣ) ⧸ (MonoidHom.restrictHom K ℂˣ).ker) =
      Nat.card (↥K →* ℂˣ) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [← hcard_dd, hlagrange, hquot, hcard_K_dual]

set_option backward.isDefEq.respectTransparency false in
theorem subgroup_dual_correspondence (G : Type*) [CommGroup G] [Fintype G] :

    Nonempty (Subgroup G ≃o (Subgroup (G →* ℂˣ))ᵒᵈ) ∧

    (∀ (K : Subgroup (G →* ℂˣ)) (g : G),
      g ∈ (subgroupDualOrderIso G).symm (OrderDual.toDual K) ↔ ∀ χ ∈ K, χ g = 1) ∧

    (∀ (H : Subgroup G),
      Nat.card H * Nat.card (MonoidHom.restrictHom H ℂˣ).ker = Nat.card G) ∧

    (∀ (K : Subgroup (G →* ℂˣ)),
      Nat.card K * Nat.card ((subgroupDualOrderIso G).symm (OrderDual.toDual K)) =
        Nat.card G) :=
  ⟨⟨subgroupDualOrderIso G⟩,
   subgroup_dual_annihilator_mem G,
   subgroup_dual_card_annihilator G,
   subgroup_dual_card_dual_annihilator G⟩

def characterAnnihilator (m : ℕ) (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup (ZMod m)ˣ where
  carrier := {u | ∀ χ ∈ H, χ u.val = 1}
  mul_mem' {a b} ha hb χ hχ := by rw [Units.val_mul, map_mul, ha χ hχ, hb χ hχ, one_mul]
  one_mem' χ _ := by rw [Units.val_one, map_one]
  inv_mem' {a} ha χ hχ := by
    have h1 := ha χ hχ
    have h2 : χ a.val * χ a⁻¹.val = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [h1, one_mul] at h2; exact h2

def galoisAnnihilator (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup ((CyclotomicField m ℚ) ≃ₐ[ℚ] (CyclotomicField m ℚ)) :=
  (characterAnnihilator m H).comap
    (IsCyclotomicExtension.Rat.galEquivZMod m (CyclotomicField m ℚ)).toMonoidHom

def fixedFieldOfCharacterSubgroup (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    IntermediateField ℚ (CyclotomicField m ℚ) :=
  IntermediateField.fixedField (galoisAnnihilator m H)

instance instNumberFieldFixedField (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    NumberField (fixedFieldOfCharacterSubgroup m H) :=
  NumberField.of_intermediateField _

def dedekindZetaLocalFactor (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (s : ℂ) : ℂ :=
  ∏ᶠ (𝔭 : {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 K) ∈ I}),
    (1 - (Ideal.absNorm (𝔭 : Ideal (𝓞 K)) : ℂ) ^ (-s))⁻¹

def characterLocalFactor (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) (p : ℕ) (s : ℂ) : ℂ :=
  ∏ χ : H, (1 - (χ : DirichletCharacter ℂ m) p * (p : ℂ) ^ (-s))⁻¹

lemma roots_of_unity_prod_eq (f : ℕ) (hf : 0 < f) (T : ℂ) :
    ∏ μ ∈ Polynomial.nthRootsFinset f (1 : ℂ), (1 - μ * T) = 1 - T ^ f := by
  have hf' : f ≠ 0 := Nat.pos_iff_ne_zero.mp hf
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ f := ⟨_, Complex.isPrimitiveRoot_exp f hf'⟩
  have h := hζ.pow_sub_pow_eq_prod_sub_mul (1 : ℂ) T hf
  simp only [one_pow] at h
  exact h.symm

noncomputable def frobenius_f_p (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (_hp : Nat.Prime p) : ℕ :=
  if hcop : p.Coprime m then
    orderOf (QuotientGroup.mk' (characterAnnihilator m H) (ZMod.unitOfCoprime p hcop))
  else 1

noncomputable def frobenius_g_p (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  haveI : Fintype H := Fintype.ofFinite H
  Fintype.card H / frobenius_f_p m H p hp

theorem frobenius_f_p_pos (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) : 0 < frobenius_f_p m H p hp := by
  unfold frobenius_f_p
  split
  · exact @orderOf_pos ((ZMod m)ˣ ⧸ characterAnnihilator m H) _ (Quotient.finite _) _
  · exact Nat.one_pos

lemma prod_fiber_const_card {α β M : Type*} [CommMonoid M] [DecidableEq β] [Fintype α]
    {f : α → β} {S : Finset β} {k : ℕ}
    (himg : ∀ a, f a ∈ S)
    (hfib : ∀ b ∈ S, (Finset.univ.filter (fun a => f a = b)).card = k)
    (h : β → M) :
    ∏ a : α, h (f a) = (∏ b ∈ S, h b) ^ k := by
  rw [← Finset.prod_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => himg i)]
  have : ∀ b ∈ S, ∏ a ∈ Finset.univ.filter (fun a => f a = b), h (f a) = h b ^ k := by
    intro b hb
    rw [Finset.prod_congr rfl (fun a ha => by simp only [Finset.mem_filter] at ha; rw [ha.2]),
        Finset.prod_const, hfib b hb]
  rw [Finset.prod_congr rfl this, Finset.prod_pow]

def evalAtUnit (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) (u : (ZMod m)ˣ) : H →* ℂ where
  toFun χ := (χ : DirichletCharacter ℂ m) u
  map_one' := by simp [MulChar.one_apply]
  map_mul' χ₁ χ₂ := by simp [Subgroup.coe_mul, MulChar.mul_apply]

lemma fiber_card_of_surj_onto {G : Type*} [Group G] [Fintype G]
    (f : G →* ℂ) (S : Finset ℂ) (hS : 0 < S.card)
    (himg : ∀ g : G, f g ∈ S)
    (hsurj : ∀ s ∈ S, ∃ g : G, f g = s) :
    ∀ μ ∈ S,
      (Finset.univ.filter (fun g : G => f g = μ)).card = Fintype.card G / S.card := by
  have hfib_eq : ∀ x ∈ S, ∀ y ∈ S,
      (Finset.univ.filter (fun g => f g = x)).card =
      (Finset.univ.filter (fun g => f g = y)).card := by
    intro x hx y hy
    obtain ⟨gx, hgx⟩ := hsurj x hx
    obtain ⟨gy, hgy⟩ := hsurj y hy
    exact MonoidHom.card_fiber_eq_of_mem_range f ⟨gx, hgx⟩ ⟨gy, hgy⟩
  obtain ⟨μ₀, hμ₀⟩ : S.Nonempty := Finset.card_pos.mp hS
  set k := (Finset.univ.filter (fun g : G => f g = μ₀)).card
  have hk : ∀ b ∈ S, (Finset.univ.filter (fun g : G => f g = b)).card = k :=
    fun b hb => hfib_eq b hb μ₀ hμ₀
  have hsum : Fintype.card G = ∑ b ∈ S, (Finset.univ.filter (fun g : G => f g = b)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun g _ => himg g)
  rw [Finset.sum_congr rfl hk, Finset.sum_const, smul_eq_mul] at hsum
  have hk_eq : k = Fintype.card G / S.card := by
    rw [hsum, Nat.mul_div_cancel_left _ hS]
  intro μ hμ; rw [hk μ hμ, hk_eq]

theorem artin_eval_surjective_aux
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) (hcop : p.Coprime m) :
    ∀ μ ∈ Polynomial.nthRootsFinset (frobenius_f_p m H p hp) (1 : ℂ),
      ∃ χ : H, evalAtUnit m H (ZMod.unitOfCoprime p hcop) χ = μ := by
  set u := ZMod.unitOfCoprime p hcop
  set q := QuotientGroup.mk' (characterAnnihilator m H) u
  set f_p := frobenius_f_p m H p hp
  have hfp_eq : f_p = orderOf q := by
    show frobenius_f_p m H p hp = orderOf q
    unfold frobenius_f_p; rw [dif_pos hcop]
  have hfp_pos : 0 < f_p := frobenius_f_p_pos m H p hp
  have hfp_ne : (f_p : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp hfp_pos

  set ev' : H →* ℂˣ := {
    toFun := fun χ => MulChar.equivToUnitHom (χ : DirichletCharacter ℂ m) u
    map_one' := by
      show MulChar.equivToUnitHom (1 : DirichletCharacter ℂ m) u = 1
      have : MulChar.equivToUnitHom (1 : DirichletCharacter ℂ m) = 1 := by
        ext a; simp [MulChar.equivToUnitHom, MulChar.toUnitHom]
      rw [this]; simp
    map_mul' := fun χ₁ χ₂ => by
      simp only [Subgroup.coe_mul]
      rw [MulChar.equivToUnitHom_mul_apply]
  } with hev'_def

  have hev'_coe : ∀ χ : H, (ev' χ : ℂ) = evalAtUnit m H u χ := by
    intro χ
    show (MulChar.equivToUnitHom (χ : DirichletCharacter ℂ m) u : ℂ) =
         (χ : DirichletCharacter ℂ m) ↑u
    exact MulChar.coe_equivToUnitHom _ _

  have hroots : ∀ χ : H, (ev' χ) ^ f_p = 1 := by
    intro χ
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hev'_coe, show evalAtUnit m H u χ = (χ : DirichletCharacter ℂ m) ↑u from rfl]
    rw [← map_pow]
    have hmem : u ^ f_p ∈ characterAnnihilator m H := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk' (characterAnnihilator m H) (u ^ f_p)) = 1
      rw [map_pow, hfp_eq]
      exact pow_orderOf_eq_one q
    have h_ann := hmem (↑χ : DirichletCharacter ℂ m) χ.prop
    rw [show (u ^ f_p : (ZMod m)ˣ).val = (u : ZMod m) ^ f_p from
      Units.val_pow_eq_pow_val u f_p] at h_ann
    exact h_ann

  haveI : NeZero f_p := ⟨Nat.pos_iff_ne_zero.mp hfp_pos⟩
  have hrange_le : ev'.range ≤ rootsOfUnity f_p ℂ := by
    intro x hx
    obtain ⟨χ, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [_root_.mem_rootsOfUnity]
    exact hroots χ


  haveI : Finite H := inferInstance
  haveI : Finite (ev'.range) := by
    apply Finite.of_surjective (f := fun g => ⟨ev' g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩)
    intro ⟨x, hx⟩; obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx; exact ⟨g, rfl⟩
  haveI : IsCyclic (ev'.range) := isCyclic_subgroup_units ev'.range
  have hexp_eq_card : Monoid.exponent (ev'.range) = Nat.card (ev'.range) :=
    IsCyclic.exponent_eq_card
  have hcard_dvd_fp : Nat.card (ev'.range) ∣ f_p := by
    rw [← hexp_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro ⟨x, hx⟩
    ext
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_one]
    obtain ⟨χ, rfl⟩ := MonoidHom.mem_range.mp hx
    have := hroots χ
    have hval := congr_arg (fun u : ℂˣ => (u : ℂ)) this
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hval
    exact hval

  have hfp_dvd_card : f_p ∣ Nat.card (ev'.range) := by


    set d := Nat.card (ev'.range)
    have hpow_eq_one : ∀ χ : H, (ev' χ) ^ d = 1 := by
      intro χ
      have hmem : ev' χ ∈ ev'.range := MonoidHom.mem_range.mpr ⟨χ, rfl⟩
      haveI : Fintype (ev'.range) := Fintype.ofFinite _
      have h := @pow_card_eq_one (ev'.range) _ _ ⟨ev' χ, hmem⟩
      have hcd : Fintype.card (ev'.range) = d := Fintype.card_eq_nat_card
      rw [hcd] at h
      ext
      have hval := congr_arg (fun x : ev'.range => (x : ℂˣ).val) h
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
                  Units.val_one] at hval
      exact hval
    have h_ann : u ^ d ∈ characterAnnihilator m H := by
      intro χ hχ
      have hchi : (⟨χ, hχ⟩ : H) ∈ (⊤ : Set H) := Set.mem_univ _
      have := hpow_eq_one ⟨χ, hχ⟩
      have hval := congr_arg (fun u : ℂˣ => (u : ℂ)) this
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at hval
      rw [hev'_coe] at hval
      show χ ↑(u ^ d) = 1
      rw [Units.val_pow_eq_pow_val]
      show (χ : DirichletCharacter ℂ m) ((↑u : ZMod m) ^ d) = 1
      rw [show (χ : DirichletCharacter ℂ m) ((↑u : ZMod m) ^ d) =
           ((χ : DirichletCharacter ℂ m) (↑u : ZMod m)) ^ d from map_pow _ _ _]
      exact hval
    rw [hfp_eq]
    have hq_pow : q ^ d = 1 := by
      have : (QuotientGroup.mk' (characterAnnihilator m H)) (u ^ d) = 1 :=
        (QuotientGroup.eq_one_iff (u ^ d)).mpr h_ann
      rw [map_pow] at this
      exact this
    exact orderOf_dvd_of_pow_eq_one hq_pow

  have hcard_eq : Nat.card (ev'.range) = f_p :=
    Nat.dvd_antisymm hcard_dvd_fp hfp_dvd_card

  haveI : NeZero f_p := ⟨hfp_ne⟩
  have hcard_roots : Nat.card (rootsOfUnity f_p ℂ) = f_p := by
    rw [Nat.card_eq_fintype_card]
    exact (Complex.isPrimitiveRoot_exp f_p hfp_ne).card_rootsOfUnity
  have hrange_eq : ev'.range = rootsOfUnity f_p ℂ := by
    apply Subgroup.eq_of_le_of_card_ge hrange_le
    rw [hcard_roots, hcard_eq]

  intro μ hμ
  rw [Polynomial.mem_nthRootsFinset hfp_pos 1] at hμ

  have hμ_ne : μ ≠ 0 := by
    intro h; simp [h, zero_pow hfp_ne] at hμ
  set μ_unit : ℂˣ := Units.mk0 μ hμ_ne
  have hμ_unit_mem : μ_unit ∈ rootsOfUnity f_p ℂ := by
    rw [_root_.mem_rootsOfUnity]
    ext; simp only [μ_unit, Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]; exact hμ

  rw [← hrange_eq] at hμ_unit_mem
  obtain ⟨χ, hχ⟩ := MonoidHom.mem_range.mp hμ_unit_mem
  exact ⟨χ, by rw [← hev'_coe, hχ]; rfl⟩

theorem artin_eval_fiber_uniform_aux
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) (hcop : p.Coprime m) :
    let f_p := frobenius_f_p m H p hp
    let g_p := frobenius_g_p m H p hp
    (∀ μ ∈ Polynomial.nthRootsFinset f_p (1 : ℂ),
      (Finset.univ.filter (fun χ : H => (χ : DirichletCharacter ℂ m) p = μ)).card = g_p) := by
  intro f_p g_p
  set u := ZMod.unitOfCoprime p hcop
  set ev := evalAtUnit m H u
  set S := Polynomial.nthRootsFinset f_p (1 : ℂ)
  set q := QuotientGroup.mk' (characterAnnihilator m H) u
  have hfp_eq : f_p = orderOf q := by
    show frobenius_f_p m H p hp = orderOf q
    unfold frobenius_f_p; rw [dif_pos hcop]
  have hfp_pos : 0 < f_p :=
    hfp_eq ▸ @orderOf_pos ((ZMod m)ˣ ⧸ characterAnnihilator m H) _ (Quotient.finite _) _
  have hS_card : S.card = f_p :=
    (Complex.isPrimitiveRoot_exp f_p (Nat.pos_iff_ne_zero.mp hfp_pos)).card_nthRootsFinset
  have himg : ∀ χ : H, ev χ ∈ S := by
    intro χ
    show (↑χ : DirichletCharacter ℂ m) ↑u ∈ Polynomial.nthRootsFinset f_p 1
    rw [hfp_eq, Polynomial.mem_nthRootsFinset
          (@orderOf_pos ((ZMod m)ˣ ⧸ characterAnnihilator m H) _ (Quotient.finite _) _)]


    rw [← map_pow]
    have hmem : u ^ orderOf q ∈ characterAnnihilator m H := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk' (characterAnnihilator m H) (u ^ orderOf q)) = 1
      rw [map_pow]
      exact pow_orderOf_eq_one q
    have h_ann := hmem (↑χ : DirichletCharacter ℂ m) χ.prop
    rw [show (u ^ orderOf q : (ZMod m)ˣ).val = (u : ZMod m) ^ orderOf q from
      Units.val_pow_eq_pow_val u (orderOf q)] at h_ann
    exact h_ann
  have hsurj : ∀ s ∈ S, ∃ g : H, ev g = s :=
    artin_eval_surjective_aux m H p hp hcop
  have hfiber := fiber_card_of_surj_onto ev S (hS_card ▸ hfp_pos) himg hsurj
  intro μ hμ
  calc (Finset.univ.filter (fun χ : H => (χ : DirichletCharacter ℂ m) p = μ)).card
      = (Finset.univ.filter (fun g : H => ev g = μ)).card := by congr 1
    _ = Fintype.card H / S.card := hfiber μ hμ
    _ = Fintype.card H / f_p := by rw [hS_card]
    _ = g_p := by
        show Fintype.card H / frobenius_f_p m H p hp = frobenius_g_p m H p hp
        unfold frobenius_g_p
        simp only [Fintype.card_eq_nat_card]

lemma artin_eval_fiber_uniform
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) (hcop : p.Coprime m) :
    let f_p := frobenius_f_p m H p hp
    let g_p := frobenius_g_p m H p hp
    (∀ χ : H, (χ : DirichletCharacter ℂ m) p ∈ Polynomial.nthRootsFinset f_p (1 : ℂ)) ∧
    (∀ μ ∈ Polynomial.nthRootsFinset f_p (1 : ℂ),
      (Finset.univ.filter (fun χ : H => (χ : DirichletCharacter ℂ m) p = μ)).card = g_p) := by
  set u := ZMod.unitOfCoprime p hcop
  have hu_val : (u : ZMod m) = (p : ZMod m) := ZMod.coe_unitOfCoprime p hcop
  set q := QuotientGroup.mk' (characterAnnihilator m H) u
  have hfp_simp : frobenius_f_p m H p hp = orderOf q := by
    unfold frobenius_f_p; rw [dif_pos hcop]
  constructor
  ·
    intro χ
    rw [hfp_simp]
    rw [Polynomial.mem_nthRootsFinset
      (@orderOf_pos ((ZMod m)ˣ ⧸ characterAnnihilator m H) _ (Quotient.finite _) _)]
    have : (↑↑χ : DirichletCharacter ℂ m) (↑p : ZMod m) =
        (↑↑χ : DirichletCharacter ℂ m) (u : ZMod m) := by rw [hu_val]
    rw [this, ← map_pow]
    have hmem : u ^ orderOf q ∈ characterAnnihilator m H := by
      rw [← QuotientGroup.eq_one_iff]
      rw [show (QuotientGroup.mk (u ^ orderOf q) : (ZMod m)ˣ ⧸ characterAnnihilator m H) =
            q ^ orderOf q from by
        rfl]
      exact pow_orderOf_eq_one q
    have h_ann := hmem (↑χ : DirichletCharacter ℂ m) χ.prop
    rw [show (u ^ orderOf q : (ZMod m)ˣ).val = (u : ZMod m) ^ orderOf q from
      Units.val_pow_eq_pow_val u (orderOf q)] at h_ann
    exact h_ann
  ·


    exact artin_eval_fiber_uniform_aux m H p hp hcop

theorem frobenius_character_distribution_identity
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (hp : Nat.Prime p) (hcop : p.Coprime m) (T : ℂ) :
    ∏ χ : H, (1 - (χ : DirichletCharacter ℂ m) p * T) =
      (∏ μ ∈ Polynomial.nthRootsFinset (frobenius_f_p m H p hp) (1 : ℂ), (1 - μ * T)) ^
        frobenius_g_p m H p hp := by
  obtain ⟨himg, hfib⟩ := artin_eval_fiber_uniform m H p hp hcop
  exact prod_fiber_const_card himg hfib (fun μ => 1 - μ * T)

@[reducible]
noncomputable def primes_above_fintype
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (p : ℕ) (_hp : Nat.Prime p) :
    Fintype {I : Ideal (𝓞 (fixedFieldOfCharacterSubgroup m H)) //
      I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 (fixedFieldOfCharacterSubgroup m H)) ∈ I} := by
  letI K := fixedFieldOfCharacterSubgroup m H
  have ha : (p : 𝓞 K) ≠ 0 := by exact_mod_cast _hp.ne_zero
  have hfin : (Ideal.span {(p : 𝓞 K)}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsub : {I : Ideal (𝓞 K) | I.IsPrime ∧ I ≠ ⊥ ∧ (p : 𝓞 K) ∈ I} ⊆
      (Ideal.span {(p : 𝓞 K)}).minimalPrimes := by
    intro I ⟨hIp, _, haI⟩
    refine ⟨⟨hIp, (Ideal.span_singleton_le_iff_mem I).mpr haI⟩, fun q ⟨hqp, haq⟩ hqI => ?_⟩
    by_cases hq0 : q = ⊥
    · exact absurd (Ideal.mem_bot.mp (hq0 ▸ (Ideal.span_singleton_le_iff_mem q).mp haq)) ha
    · exact ((hqp.isMaximal hq0).eq_of_le hIp.ne_top hqI).ge
  exact (hfin.subset hsub).fintype









def dedekindZetaTerm (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℕ → ℂ :=
  LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s

lemma dedekindZetaTerm_zero (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    dedekindZetaTerm K s 0 = 0 :=
  LSeries.term_zero _ _

lemma dedekindZetaTerm_one (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    dedekindZetaTerm K s 1 = 1 := by
  unfold dedekindZetaTerm
  rw [LSeries.term_of_ne_zero (by omega : (1 : ℕ) ≠ 0)]
  simp only [Nat.cast_one]
  suffices Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 by norm_cast; simp
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun ⟨I, hI⟩ => by
    simp only [Subtype.mk.injEq]; exact Ideal.absNorm_eq_one_iff.mp hI⟩

set_option maxHeartbeats 400000 in
lemma idealNormCount_mul_coprime (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} =
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} *
    Nat.card {J : Ideal (𝓞 K) // Ideal.absNorm J = n} := by
  open UniqueFactorizationMonoid in
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n}
        → {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} :=
    fun ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ => ⟨I * J, by rw [map_mul Ideal.absNorm, hI, hJ]⟩
  suffices hbij : Function.Bijective f by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm
  constructor
  ·
    rintro ⟨⟨I₁, hI₁⟩, ⟨J₁, hJ₁⟩⟩ ⟨⟨I₂, hI₂⟩, ⟨J₂, hJ₂⟩⟩ heq
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq ⊢
    have hI₁ne : I₁ ≠ 0 := by intro h; exact hm (by rw [← hI₁, h, map_zero])
    have hrel12 : IsRelPrime I₁ J₂ := by
      intro d hd1 hd2
      rw [Ideal.isUnit_iff, ← Ideal.absNorm_eq_one_iff]
      have := Nat.dvd_gcd (map_dvd Ideal.absNorm hd1) (map_dvd Ideal.absNorm hd2)
      rwa [hI₁, hJ₂, hmn, Nat.dvd_one] at this
    have hrel21 : IsRelPrime I₂ J₁ := by
      intro d hd1 hd2
      rw [Ideal.isUnit_iff, ← Ideal.absNorm_eq_one_iff]
      have := Nat.dvd_gcd (map_dvd Ideal.absNorm hd1) (map_dvd Ideal.absNorm hd2)
      rwa [hI₂, hJ₁, hmn, Nat.dvd_one] at this
    have hIeq : I₁ = I₂ := dvd_antisymm
      (hrel12.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right I₁ J₁))
      (hrel21.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right I₂ J₂))
    exact ⟨hIeq, mul_left_cancel₀ (hIeq ▸ hI₁ne) (hIeq ▸ heq)⟩
  ·
    rintro ⟨L, hL⟩
    open UniqueFactorizationMonoid in
    have hLne : L ≠ 0 := by
      intro h; exact Nat.mul_ne_zero hm hn (by rw [← hL, h, map_zero])
    let nf := normalizedFactors L
    let p : Ideal (𝓞 K) → Prop := fun 𝔭 => Ideal.absNorm 𝔭 ∣ m
    let I := (nf.filter p).prod
    let J := (nf.filter (fun 𝔭 => ¬ p 𝔭)).prod
    have hIJ : I * J = L := by
      show (nf.filter p).prod * (nf.filter (fun 𝔭 => ¬ p 𝔭)).prod = L
      rw [← Multiset.prod_add, Multiset.filter_add_not,
        prod_normalizedFactors_eq_self hLne]
    have hIJ_norm : Ideal.absNorm I * Ideal.absNorm J = m * n := by
      rw [← map_mul Ideal.absNorm, hIJ, hL]

    have hdvdm : Ideal.absNorm I ∣ m := by
      have hcop : Nat.Coprime (Ideal.absNorm I) n := by
        rw [show Ideal.absNorm I = ((nf.filter p).map Ideal.absNorm).prod from
          map_multiset_prod Ideal.absNorm _, Nat.coprime_multiset_prod_left_iff]
        intro a ha
        obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp ha
        exact Nat.Coprime.coprime_dvd_left (Multiset.mem_filter.mp h𝔭).2 hmn
      exact hcop.dvd_of_dvd_mul_right (hIJ_norm ▸ dvd_mul_right _ _)

    have hdvdn : Ideal.absNorm J ∣ n := by
      have hcop : Nat.Coprime (Ideal.absNorm J) m := by
        rw [show Ideal.absNorm J = ((nf.filter (fun 𝔭 => ¬ p 𝔭)).map Ideal.absNorm).prod from
          map_multiset_prod Ideal.absNorm _, Nat.coprime_multiset_prod_left_iff]
        intro a ha
        obtain ⟨𝔭, h𝔭mem, rfl⟩ := Multiset.mem_map.mp ha
        have h𝔭filt := Multiset.mem_filter.mp h𝔭mem
        have h𝔭_prime := prime_of_normalized_factor _ h𝔭filt.1

        have h𝔭_pp : IsPrimePow (Ideal.absNorm 𝔭) := by
          have hne := h𝔭_prime.ne_zero
          have hisPrime := (Ideal.prime_iff_isPrime hne).mp h𝔭_prime
          haveI : 𝔭.IsMaximal := hisPrime.isMaximal hne
          haveI : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
          haveI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
          obtain ⟨q, _, e, hprime, hcard⟩ := FiniteField.card' (𝓞 K ⧸ 𝔭)
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
          exact IsPrimePow.pow hprime.isPrimePow e.pos.ne'

        have h𝔭_dvd_n : Ideal.absNorm 𝔭 ∣ n :=
          ((hmn.isPrimePow_dvd_mul h𝔭_pp).mp
            (hL ▸ map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors h𝔭filt.1))).resolve_left
              h𝔭filt.2
        exact Nat.Coprime.coprime_dvd_left h𝔭_dvd_n hmn.symm
      exact hcop.dvd_of_dvd_mul_left (hIJ_norm ▸ dvd_mul_left _ _)

    have hInorm : Ideal.absNorm I = m := by
      apply Nat.le_antisymm
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvdm
      · by_contra h
        push Not at h
        have : Ideal.absNorm I * Ideal.absNorm J < m * n :=
          calc _ ≤ Ideal.absNorm I * n :=
                Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvdn)
          _ < m * n := Nat.mul_lt_mul_of_pos_right h (Nat.pos_of_ne_zero hn)
        omega
    have hJnorm : Ideal.absNorm J = n :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) (hInorm ▸ hIJ_norm)
    exact ⟨(⟨I, hInorm⟩, ⟨J, hJnorm⟩), Subtype.ext hIJ⟩

lemma dedekindZetaTerm_mul_coprime (K : Type*) [Field K] [NumberField K] (s : ℂ)
    {m n : ℕ} (hmn : m.Coprime n) :
    dedekindZetaTerm K s (m * n) = dedekindZetaTerm K s m * dedekindZetaTerm K s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [dedekindZetaTerm, LSeries.term_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dedekindZetaTerm, LSeries.term_zero]
  have hmn_ne : (m * n : ℕ) ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [dedekindZetaTerm, LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    LSeries.term_of_ne_zero hmn_ne]
  rw [idealNormCount_mul_coprime K hmn hm hn]
  push_cast
  rw [Complex.natCast_mul_natCast_cpow m n s]
  ring

set_option maxHeartbeats 800000 in

lemma dedekindZetaTerm_normSummable (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    Summable (fun n => ‖dedekindZetaTerm K s n‖) := by
  unfold dedekindZetaTerm

  suffices hLS : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s from hLS.norm

  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one hs

  apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
    (a := NumberField.dedekindZeta_residue K)
  simp only [Real.rpow_one]

  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  norm_cast

  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma absNorm_prime_above_is_prime_pow (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ 𝔭) :
    ∃ f : ℕ, 0 < f ∧ Ideal.absNorm 𝔭 = (↑p : ℕ) ^ f := by
  obtain ⟨h𝔭_prime, _, hp_mem⟩ := h𝔭
  haveI : 𝔭.IsPrime := h𝔭_prime
  have hp_ne_zero : (↑↑p : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp_span_prime : (Ideal.span {(↑↑p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp_ne_zero).mpr
      (Int.prime_iff_natAbs_prime.mpr (by simpa using p.2))
  have hp_span_ne_bot : (Ideal.span {(↑↑p : ℤ)}) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  haveI : (Ideal.span {(↑↑p : ℤ)}).IsMaximal :=
    hp_span_prime.isMaximal hp_span_ne_bot
  haveI : 𝔭.LiesOver (Ideal.span {(↑↑p : ℤ)}) := by
    constructor
    have h_prime_under : (Ideal.under ℤ 𝔭).IsPrime := Ideal.IsPrime.under ℤ 𝔭
    have hp_in_under : (↑↑p : ℤ) ∈ Ideal.under ℤ 𝔭 := by
      show (algebraMap ℤ (𝓞 K)) (↑↑p : ℤ) ∈ 𝔭
      simp only [map_natCast]; exact hp_mem
    exact (‹(Ideal.span {(↑↑p : ℤ)}).IsMaximal›).eq_of_le h_prime_under.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hp_in_under)
  rw [Ideal.absNorm_eq_pow_inertiaDeg' 𝔭 p.2]
  exact ⟨_, Ideal.inertiaDeg_pos _ _, rfl⟩

noncomputable instance primesAbove_fintype (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) :
    Fintype {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} := by
  classical
  set J := Ideal.span ({(↑↑p : 𝓞 K)} : Set (𝓞 K)) with hJ_def
  have hJ_ne_bot : J ≠ ⊥ := by
    rw [hJ_def, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  have h_subset : ∀ (𝔭 : Ideal (𝓞 K)),
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ 𝔭 →
      𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors J).toFinset := by
    intro 𝔭 ⟨h_prime, _, h_mem⟩
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hJ_ne_bot]
    exact ⟨h_prime, (Ideal.span_singleton_le_iff_mem 𝔭).mpr h_mem⟩
  exact Fintype.ofInjective
    (fun ⟨𝔭, h⟩ => ⟨𝔭, h_subset 𝔭 h⟩ :
      {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} →
      (UniqueFactorizationMonoid.normalizedFactors J).toFinset)
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)





theorem LSeries_prod_eq_tprod_localFactor
    (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m))
    (s : ℂ) (hs : 1 < s.re) :
    ∏ χ : H, LSeries (fun n => (χ : DirichletCharacter ℂ m) ↑n) s =
      ∏' p : Nat.Primes, characterLocalFactor m H p s := by

  have h_euler : ∀ χ : H,
      LSeries (fun n => (χ : DirichletCharacter ℂ m) ↑n) s =
        ∏' p : Nat.Primes,
          (1 - (χ : DirichletCharacter ℂ m) ↑↑p * (↑↑p : ℂ) ^ (-s))⁻¹ :=
    fun χ => (DirichletCharacter.LSeries_eulerProduct_tprod
      (↑χ : DirichletCharacter ℂ m) hs).symm
  simp_rw [h_euler]


  symm
  exact Multipliable.tprod_finsetProd (fun χ _ =>
    (DirichletCharacter.LSeries_eulerProduct_hasProd
      (↑χ : DirichletCharacter ℂ m) hs).multipliable)







end Cyclotomic

section Nonvanishing

theorem dirichlet_L_ne_zero_at_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

end Nonvanishing

end Section19
