/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Gershgorin

namespace Expanders

abbrev IsDRegular {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop :=
  G.IsRegularOfDegree d

variable {V : Type*} [DecidableEq V]

noncomputable def indicatorVec (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

end Expanders

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def setNeighborFinset (S : Finset V) : Finset V :=
  (S.biUnion (fun v => G.neighborFinset v)) \ S

def IsVertexExpander (α β : ℝ) : Prop :=
  α * β < 1 ∧
  ∀ S : Finset V, (S.card : ℝ) ≤ α * (Fintype.card V : ℝ) →
    ((G.setNeighborFinset S).card : ℝ) ≥ β * (S.card : ℝ)

open Matrix Finset BigOperators

noncomputable def edgeCountBetween (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card

noncomputable def adjEigenvalues : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

noncomputable def secondLargestAdjEigenvalue
    (hcard : Fintype.card V ≥ 2) : ℝ :=
  G.adjEigenvalues ⟨1, by omega⟩






end SimpleGraph

namespace BipartiteMatching

open Finset

noncomputable def partialMatchingsOfSize (n : ℕ) (adj : Fin n → Fin n → Bool) (k : ℕ) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (Finset.univ (α := Finset (Fin n × Fin n))).filter fun m =>
    m.card = k ∧
    (∀ p ∈ m, adj p.1 p.2 = true) ∧
    (m.image Prod.fst).card = m.card ∧
    (m.image Prod.snd).card = m.card

def HasMinDegree (n : ℕ) (adj : Fin n → Fin n → Bool) (d : ℕ) : Prop :=
  (∀ i : Fin n, (Finset.univ.filter (fun j => adj i j = true)).card ≥ d) ∧
  (∀ j : Fin n, (Finset.univ.filter (fun i => adj i j = true)).card ≥ d)



end BipartiteMatching

namespace SpectralExpanders

structure GraphFamily where
  V : ℕ → Type*
  instFintype : ∀ n, Fintype (V n)
  instDecidableEq : ∀ n, DecidableEq (V n)
  G : ∀ n, SimpleGraph (V n)
  instDecidableAdj : ∀ n, DecidableRel (G n).Adj
  d : ℕ
  isRegular : ∀ n, (G n).IsRegularOfDegree d
  card_ge_two : ∀ n, @Fintype.card (V n) (instFintype n) ≥ 2

attribute [instance] GraphFamily.instFintype GraphFamily.instDecidableEq
  GraphFamily.instDecidableAdj

open Finset BigOperators

noncomputable def GraphFamily.setConductanceAt (F : GraphFamily) (n : ℕ)
    (S : Finset (F.V n)) : ℝ :=
  let volS := ∑ v ∈ S, ((F.G n).degree v : ℝ)
  let volSc := ∑ v ∈ Sᶜ, ((F.G n).degree v : ℝ)
  let edgesCut := ∑ v ∈ S, (((F.G n).neighborFinset v) \ S).card
  (edgesCut : ℝ) / min volS volSc

noncomputable def GraphFamily.familyConductance (F : GraphFamily) (n : ℕ) : ℝ :=
  let candidates := (@Finset.univ (Finset (F.V n)) _).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (F.setConductanceAt n)
  else
    0

def IsExpanderFamilyConductance (F : GraphFamily) : Prop :=
  ∃ c' : ℝ, c' > 0 ∧ ∀ n : ℕ, F.familyConductance n ≥ c'

end SpectralExpanders

namespace SimpleGraph

section BipartiteExpander

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable (G : SimpleGraph (L ⊕ R)) [DecidableRel G.Adj]

def bipartiteNeighborFinset (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => ∃ l ∈ S, G.Adj (Sum.inl l) (Sum.inr r)

def IsBipartiteExpander (α β : ℝ) : Prop :=
  ∀ S : Finset L, (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    ((G.bipartiteNeighborFinset S).card : ℝ) ≥ β * (S.card : ℝ)

end BipartiteExpander

end SimpleGraph

namespace ExpanderDiameter

open Polynomial Matrix Finset BigOperators SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma smul_matrix_pow (c : ℝ) (A : Matrix V V ℝ) (n : ℕ) :
    (c • A) ^ n = c ^ n • A ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul_comm, ← pow_succ, ← pow_succ]

theorem polynomial_diameter_bound
    {d : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : G.IsRegularOfDegree d) (_hd : 0 < d)
    (p : Polynomial ℝ) {k : ℕ} (hp : p.natDegree ≤ k)
    (M : Matrix V V ℝ) (hM : M = (1 / (d : ℝ)) • (G.adjMatrix ℝ))
    (h_pos : ∀ u v : V, 0 < (Polynomial.aeval M p) u v) :
    G.diam ≤ k := by

  suffices hediam : G.ediam ≤ ↑k from ENat.toNat_le_of_le_coe hediam

  apply SimpleGraph.ediam_le_of_edist_le
  intro u v

  have h_exists : ∃ i ∈ range (p.natDegree + 1), (G.adjMatrix ℝ ^ i) u v ≠ 0 := by
    by_contra h_all_zero
    push Not at h_all_zero

    have h_zero : (Polynomial.aeval M p) u v = 0 := by
      rw [hM, Polynomial.aeval_eq_sum_range]
      simp only [Matrix.sum_apply, Matrix.smul_apply]
      apply Finset.sum_eq_zero
      intro i hi
      rw [smul_matrix_pow, Matrix.smul_apply, h_all_zero i hi, smul_zero, smul_zero]
    linarith [h_pos u v]

  obtain ⟨i, hi_range, hi_ne⟩ := h_exists
  rw [G.adjMatrix_pow_apply_eq_card_walk] at hi_ne
  simp only [Ne, Nat.cast_eq_zero] at hi_ne
  rw [Fintype.card_eq_zero_iff] at hi_ne
  obtain ⟨⟨w, hw⟩⟩ := not_isEmpty_iff.mp hi_ne

  have hi_le_k : i ≤ k := by
    have := Finset.mem_range.mp hi_range; omega
  calc G.edist u v ≤ ↑w.length := SimpleGraph.edist_le w
    _ = ↑i := by rw [hw]
    _ ≤ ↑k := by exact_mod_cast hi_le_k

lemma aeval_matrix_diagonal {m : Type*} [Fintype m] [DecidableEq m]
    (v : m → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal v) p =
      Matrix.diagonal (fun i => p.eval (v i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, ← Pi.add_def, Matrix.diagonal_add]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Matrix.diagonal_pow, Polynomial.eval_monomial]
    ext i j; simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    · simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, Matrix.diagonal_apply, h]

lemma aeval_conjStarAlgAut_eq {m : Type*} [Fintype m] [DecidableEq m]
    (u : ↥(Matrix.unitaryGroup m ℝ)) (D : Matrix m m ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval ((Unitary.conjStarAlgAut ℝ (Matrix m m ℝ) u) D) p =
      (Unitary.conjStarAlgAut ℝ (Matrix m m ℝ) u) (Polynomial.aeval D p) := by
  have h := Polynomial.aeval_algEquiv
    (Unitary.conjStarAlgAut ℝ (Matrix m m ℝ) u).toAlgEquiv D
  have := congr_fun (congrArg DFunLike.coe h) p
  simp only [AlgHom.comp_apply, AlgHom.coe_coe] at this
  convert this using 1

lemma conjStarAlgAut_diagonal_entry_eq {m : Type*} [Fintype m] [DecidableEq m]
    (u : ↥(Matrix.unitaryGroup m ℝ)) (d : m → ℝ) (a b : m) :
    ((Unitary.conjStarAlgAut ℝ (Matrix m m ℝ) u) (Matrix.diagonal d)) a b =
      ∑ i : m, d i * (u : Matrix m m ℝ) a i * (u : Matrix m m ℝ) b i := by
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.star_apply,
    RCLike.star_def, conj_trivial, Matrix.diagonal_apply]
  congr 1; ext i; simp only [Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]; ring
  · intro j _ hji; simp [hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma aeval_hermitian_entry {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) (p : Polynomial ℝ) (a b : m) :
    (Polynomial.aeval M p) a b =
      ∑ i : m, p.eval (hM.eigenvalues i) *
        (hM.eigenvectorUnitary : Matrix m m ℝ) a i *
        (hM.eigenvectorUnitary : Matrix m m ℝ) b i := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [aeval_conjStarAlgAut_eq]
  simp only [aeval_matrix_diagonal, Function.comp, conjStarAlgAut_diagonal_entry_eq]
  simp

lemma unitary_row_sq_sum_eq_one {m : Type*} [Fintype m] [DecidableEq m]
    (u : ↥(Matrix.unitaryGroup m ℝ)) (a : m) :
    ∑ k : m, (u : Matrix m m ℝ) a k ^ 2 = 1 := by
  have h := congr_fun (congr_fun (Unitary.coe_mul_star_self u) a) a
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  suffices hsuff : ∀ k, (u : Matrix m m ℝ) a k ^ 2 =
    (u : Matrix m m ℝ) a k * (↑(star u) : Matrix m m ℝ) k a from by
    simp_rw [hsuff]; exact h
  intro k; simp [sq, Matrix.star_apply]

lemma walk_matrix_mulVec_ones {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M = (1 / (d : ℝ)) • (G.adjMatrix ℝ)) :
    M *ᵥ (Function.const (Fin n) 1) = Function.const (Fin n) 1 := by
  ext v
  simp only [hM, mulVec, dotProduct, smul_apply, smul_eq_mul, Function.const_apply]
  have key : ∑ x : Fin n, (G.adjMatrix ℝ) v x = (d : ℝ) := by
    have h := G.adjMatrix_mulVec_const_apply (a := (1 : ℝ)) (v := v)
    simp only [mulVec, dotProduct, Function.const_apply, mul_one] at h
    rw [h, hreg v]
  calc ∑ x, 1 / (d : ℝ) * (G.adjMatrix ℝ) v x * 1
      = (d : ℝ)⁻¹ * ∑ x, (G.adjMatrix ℝ) v x := by
        rw [Finset.mul_sum]; congr 1; ext x; ring
    _ = (d : ℝ)⁻¹ * (d : ℝ) := by rw [key]
    _ = 1 := by field_simp

lemma walk_matrix_eigenvalues₀_zero_eq_one {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = (1 / (d : ℝ)) • (G.adjMatrix ℝ))
    (hM_sym : M.IsHermitian) :
    hM_sym.eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; omega⟩ = 1 := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n

  have h_range_eq : Set.range hM_sym.eigenvalues₀ = Set.range hM_sym.eigenvalues := by
    ext x; simp only [Set.mem_range, Matrix.IsHermitian.eigenvalues]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))) k, by simp⟩
    · rintro ⟨k, hk⟩
      exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm k, by simp [hk]⟩

  have hones : M *ᵥ (Function.const (Fin n) 1) = Function.const (Fin n) 1 :=
    walk_matrix_mulVec_ones G hd hreg M hM
  have hones_ne : (Function.const (Fin n) (1 : ℝ)) ≠ 0 := by
    intro h; have := congr_fun h ⟨0, hn⟩; simp at this
  have h_has_ev : Module.End.HasEigenvalue (Matrix.toLin' M) 1 := by
    rw [Module.End.hasEigenvalue_iff]
    intro h_bot
    have hmem : Function.const (Fin n) (1 : ℝ) ∈
        Module.End.eigenspace (Matrix.toLin' M) 1 := by
      rw [Module.End.mem_eigenspace_iff]
      simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply, one_smul]
      exact hones
    rw [h_bot] at hmem
    exact hones_ne hmem
  have h_one_in_spec : (1 : ℝ) ∈ spectrum ℝ M := by
    rw [← Matrix.spectrum_toLin' M]
    exact (Module.End.hasEigenvalue_iff_mem_spectrum).mp h_has_ev

  have h_ev_le_one : ∀ i : Fin (Fintype.card (Fin n)), hM_sym.eigenvalues₀ i ≤ 1 := by
    intro i
    have h_in_spec : (hM_sym.eigenvalues₀ i : ℝ) ∈ spectrum ℝ M := by
      rw [hM_sym.spectrum_real_eq_range_eigenvalues, ← h_range_eq]
      exact ⟨i, rfl⟩
    have h_eigenvalue_i : Module.End.HasEigenvalue (Matrix.toLin' M)
        (hM_sym.eigenvalues₀ i : ℝ) := by
      rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin' M]
      exact h_in_spec
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball h_eigenvalue_i

    have hM_diag : M k k = 0 := by
      rw [hM]
      simp only [Matrix.smul_apply, smul_eq_mul]
      have : (G.adjMatrix ℝ) k k = 0 := by
        simp [SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl]
      rw [this, mul_zero]

    have hM_row_sum : ∑ j ∈ Finset.univ.erase k, ‖M k j‖ = 1 := by
      have hM_entries_nonneg : ∀ j, 0 ≤ M k j := by
        intro j; rw [hM]
        simp only [Matrix.smul_apply, smul_eq_mul]
        apply mul_nonneg
        · positivity
        · simp only [SimpleGraph.adjMatrix_apply]
          split_ifs <;> positivity
      have h_norm_eq : ∀ j ∈ Finset.univ.erase k, ‖M k j‖ = M k j :=
        fun j _ => Real.norm_of_nonneg (hM_entries_nonneg j)
      rw [Finset.sum_congr rfl h_norm_eq]
      have hsub : ∑ j ∈ Finset.univ.erase k, M k j = ∑ j, M k j - M k k := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring
      rw [hsub, hM_diag, sub_zero]
      have := congr_fun hones k
      simp only [mulVec, dotProduct, Function.const_apply, mul_one] at this
      exact this
    rw [hM_diag, hM_row_sum] at hk
    simp only [Metric.mem_closedBall] at hk
    have hab : |hM_sym.eigenvalues₀ i| ≤ 1 := by
      rwa [Real.dist_eq, sub_zero] at hk
    linarith [le_abs_self (hM_sym.eigenvalues₀ i)]

  have h_one_exists : ∃ i : Fin (Fintype.card (Fin n)), hM_sym.eigenvalues₀ i = 1 := by
    rw [hM_sym.spectrum_real_eq_range_eigenvalues, ← h_range_eq] at h_one_in_spec
    exact h_one_in_spec
  obtain ⟨i, hi⟩ := h_one_exists
  haveI : NeZero (Fintype.card (Fin n)) := ⟨by rw [hcard]; omega⟩
  apply le_antisymm
  · exact h_ev_le_one _
  · calc (1 : ℝ) = hM_sym.eigenvalues₀ i := hi.symm
      _ ≤ hM_sym.eigenvalues₀ ⟨0, by rw [hcard]; omega⟩ :=
        hM_sym.eigenvalues₀_antitone (Fin.zero_le i)

theorem poly_degree_bounds_diameter
    {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = (1 / (d : ℝ)) • (G.adjMatrix ℝ))
    (hM_sym : M.IsHermitian)
    (p : Polynomial ℝ) (k : ℕ) (hp_deg : p.natDegree ≤ k)
    (hp_one : p.eval 1 = 1)
    (hp_small : ∀ i : Fin (Fintype.card (Fin n)), i.val ≥ 1 →
      |p.eval (hM_sym.eigenvalues₀ i)| < 1 / (n : ℝ)) :
    G.diam ≤ k := by
  apply polynomial_diameter_bound G hreg hd p hp_deg M hM
  intro a b
  rw [aeval_hermitian_entry M hM_sym p a b]
  set U := (hM_sym.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  set j₀ : Fin (Fintype.card (Fin n)) := ⟨0, by rw [Fintype.card_fin]; omega⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn

  have h_ev_rel : ∀ j, hM_sym.eigenvalues (e j) = hM_sym.eigenvalues₀ j := by
    intro j; simp [Matrix.IsHermitian.eigenvalues, e]

  have h_sum_reindex : ∑ i : Fin n, p.eval (hM_sym.eigenvalues i) * U a i * U b i =
      ∑ j : Fin (Fintype.card (Fin n)),
        p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j) := by
    conv_lhs => rw [← Equiv.sum_comp e]
    congr 1; ext j; simp only [Function.comp, h_ev_rel]
  rw [h_sum_reindex]
  have h_ev0 : hM_sym.eigenvalues₀ j₀ = 1 :=
    walk_matrix_eigenvalues₀_zero_eq_one hn G hd hreg M hM hM_sym

  have hM_symm : ∀ v i : Fin n, M v i = M i v := by
    intro v i
    have h : Mᴴ = M := hM_sym
    have h2 : Mᴴ v i = M v i := congr_fun (congr_fun h v) i
    simp only [Matrix.conjTranspose_apply, star_trivial] at h2
    exact h2.symm

  have h_row_sum : ∀ v : Fin n, ∑ j, M v j = 1 := by
    intro v
    have := congr_fun (walk_matrix_mulVec_ones G hd hreg M hM) v
    simp [mulVec, dotProduct, Function.const_apply, mul_one] at this
    exact this

  have h_col_sum_M : ∀ i : Fin n, ∑ v, M v i = 1 := by
    intro i; simp_rw [hM_symm _ i]; exact h_row_sum i

  have h_col_sum_zero : ∀ j : Fin n, hM_sym.eigenvalues j ≠ 1 →
      ∑ v : Fin n, U v j = 0 := by
    intro j hj


    have h_eigen : ∀ v, ∑ k, M v k * U k j = hM_sym.eigenvalues j * U v j := by
      intro v
      have h_basis := hM_sym.mulVec_eigenvectorBasis j
      have hv := congr_fun h_basis v
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
        Matrix.IsHermitian.eigenvectorUnitary_apply] at hv
      exact hv
    have way1 : ∑ v, ∑ k, M v k * U k j = hM_sym.eigenvalues j * ∑ v, U v j := by
      simp_rw [h_eigen, Finset.mul_sum]
    have way2 : ∑ v, ∑ k, M v k * U k j = ∑ v, U v j := by
      rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul]
      simp_rw [h_col_sum_M, one_mul]
    have : (hM_sym.eigenvalues j - 1) * ∑ v, U v j = 0 := by linarith [way1, way2]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hj)

  have h_ev_ne_one : ∀ j : Fin (Fintype.card (Fin n)), j.val ≥ 1 →
      hM_sym.eigenvalues₀ j ≠ 1 := by
    intro j hj habs
    have h1 := hp_small j hj; rw [habs, hp_one, abs_one] at h1
    have h_one_le_n : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
    have h_inv_le : 1 / (n : ℝ) ≤ 1 := div_le_one_of_le₀ h_one_le_n (by linarith)
    linarith

  have h_parseval : ∑ j : Fin n, (∑ v : Fin n, U v j) ^ 2 = (n : ℝ) := by
    have hUUT : U * Uᵀ = 1 := by
      have := Unitary.coe_mul_star_self hM_sym.eigenvectorUnitary
      simp only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] at this
      exact this
    calc ∑ j : Fin n, (∑ v : Fin n, U v j) ^ 2
        = ∑ v, ∑ w, ∑ j, U v j * U w j := by
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
          congr 1; ext v
          rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      _ = ∑ v, ∑ w, (U * Uᵀ) v w := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply]
      _ = (n : ℝ) := by
          rw [hUUT]; simp [Matrix.one_apply, Finset.sum_ite_eq',
            Finset.card_univ, Fintype.card_fin]

  have h_col_sq_n : (∑ v : Fin n, U v (e j₀)) ^ 2 = (n : ℝ) := by
    have h_reindex : ∑ j' : Fin (Fintype.card (Fin n)),
        (∑ v : Fin n, U v (e j')) ^ 2 = (n : ℝ) := by
      rw [← h_parseval, ← Equiv.sum_comp e]
    have h_tail : ∀ j' ∈ Finset.univ.erase j₀,
        (∑ v : Fin n, U v (e j')) ^ 2 = 0 := by
      intro j' hj'
      have hj'_val : j'.val ≥ 1 := by
        have hj'_ne : j' ≠ j₀ := by
          exact (Finset.mem_erase.mp hj').1
        exact Nat.one_le_iff_ne_zero.mpr (fun h => hj'_ne (Fin.ext h))
      have hne : hM_sym.eigenvalues (e j') ≠ 1 := by
        rw [h_ev_rel]
        exact h_ev_ne_one j' hj'_val
      rw [h_col_sum_zero (e j') hne]; simp
    have := Finset.add_sum_erase Finset.univ
      (fun j' => (∑ v : Fin n, U v (e j')) ^ 2) (Finset.mem_univ j₀)
    rw [Finset.sum_eq_zero h_tail, add_zero] at this
    linarith [h_reindex]

  have h_col_norm : ∑ v : Fin n, U v (e j₀) ^ 2 = 1 := by
    have hU_star := Unitary.coe_star_mul_self hM_sym.eigenvectorUnitary
    have h := congr_fun (congr_fun hU_star (e j₀)) (e j₀)
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply,
      RCLike.star_def, conj_trivial] at h
    convert h using 1; congr 1; ext v; ring

  have h_all_eq : ∀ v w : Fin n, U v (e j₀) = U w (e j₀) := by
    by_contra h_not; push_neg at h_not
    obtain ⟨v₁, v₂, hne⟩ := h_not
    have h_var_zero : ∑ v : Fin n,
        (U v (e j₀) - (∑ w, U w (e j₀)) / n) ^ 2 = 0 := by
      have expand : ∀ v : Fin n, (U v (e j₀) - (∑ w, U w (e j₀)) / (n : ℝ)) ^ 2 =
          U v (e j₀) ^ 2 - 2 * U v (e j₀) * ((∑ w, U w (e j₀)) / n) +
          ((∑ w, U w (e j₀)) / n) ^ 2 := fun v => by ring
      simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum]
      have h1 := h_col_norm; have h2 := h_col_sq_n
      field_simp; nlinarith
    have h_each_zero : ∀ v, U v (e j₀) - (∑ w, U w (e j₀)) / (n : ℝ) = 0 := by
      intro v
      have hnn : ∀ i : Fin n, (0 : ℝ) ≤
          (U i (e j₀) - (∑ w, U w (e j₀)) / n) ^ 2 := fun _ => sq_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp h_var_zero v
        (Finset.mem_univ v)
      exact sq_eq_zero_iff.mp this
    have h1 := sub_eq_zero.mp (h_each_zero v₁)
    have h2 := sub_eq_zero.mp (h_each_zero v₂)
    exact hne (by linarith)

  have h_entry_sq : ∀ v : Fin n, U v (e j₀) ^ 2 = 1 / (n : ℝ) := by
    intro v
    have h_sum_const : ∑ w : Fin n, U w (e j₀) ^ 2 = n * U v (e j₀) ^ 2 := by
      conv_lhs => rw [show ∑ w : Fin n, U w (e j₀) ^ 2 =
        ∑ w : Fin n, U v (e j₀) ^ 2 from
        Finset.sum_congr rfl (fun w _ => by rw [h_all_eq w v])]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h_sum_const] at h_col_norm
    have : U v (e j₀) ^ 2 = 1 / (n : ℝ) := by
      field_simp at h_col_norm ⊢; linarith
    exact this
  have h_prod_eq : U a (e j₀) * U b (e j₀) = 1 / (n : ℝ) := by
    rw [show U a (e j₀) * U b (e j₀) = U a (e j₀) ^ 2 from by
      rw [h_all_eq b a]; ring]
    exact h_entry_sq a

  have h_split : ∑ j : Fin (Fintype.card (Fin n)),
      p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j) =
    p.eval (hM_sym.eigenvalues₀ j₀) * (U a (e j₀) * U b (e j₀)) +
      ∑ j ∈ Finset.univ.erase j₀,
        p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j) := by
    have := Finset.add_sum_erase Finset.univ
      (fun j => p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j))
      (Finset.mem_univ j₀)
    linarith
  rw [h_split, h_ev0, hp_one, one_mul, h_prod_eq]
  suffices h_tail : |∑ j ∈ Finset.univ.erase j₀,
      p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j)| < 1 / (n : ℝ) by
    have h_bound := (abs_lt.mp h_tail).1
    linarith

  have h_cs : ∑ j ∈ Finset.univ.erase j₀, |U a (e j)| * |U b (e j)| ≤
      Real.sqrt (∑ j ∈ Finset.univ.erase j₀, U a (e j) ^ 2) *
      Real.sqrt (∑ j ∈ Finset.univ.erase j₀, U b (e j) ^ 2) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ.erase j₀)
      (fun j => |U a (e j)|) (fun j => |U b (e j)|)
    simp_rw [sq_abs] at this
    convert this using 2 <;> (ext j; rw [abs_mul_abs_self])

  have h_rest : ∀ c : Fin n,
      ∑ j ∈ Finset.univ.erase j₀, U c (e j) ^ 2 = 1 - 1 / (n : ℝ) := by
    intro c
    have h_full : ∑ j' : Fin (Fintype.card (Fin n)), U c (e j') ^ 2 = 1 := by
      have h := unitary_row_sq_sum_eq_one hM_sym.eigenvectorUnitary c
      rw [show ∑ j' : Fin (Fintype.card (Fin n)), U c (e j') ^ 2 =
        ∑ k : Fin n, U c k ^ 2 from Equiv.sum_comp e (fun k => U c k ^ 2)]
      exact h
    have := Finset.add_sum_erase Finset.univ (fun j' => U c (e j') ^ 2) (Finset.mem_univ j₀)
    linarith [h_entry_sq c]

  have h_sqrt_lt : Real.sqrt (1 - 1 / (n : ℝ)) < 1 := by
    have h_nn : (0 : ℝ) ≤ 1 - 1 / n := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have : 1 / (n : ℝ) ≤ 1 := div_le_one_of_le₀ h1n (by linarith)
      linarith
    have h_lt : 1 - 1 / (n : ℝ) < 1 := by linarith [show (0 : ℝ) < 1 / n from div_pos one_pos hn_pos]
    calc Real.sqrt (1 - 1 / (n : ℝ)) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt h_nn h_lt
      _ = 1 := Real.sqrt_one

  have h_abs_le : |∑ j ∈ Finset.univ.erase j₀,
      p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j)| ≤
    (1 / (n : ℝ)) * (Real.sqrt (1 - 1 / (n : ℝ)) * Real.sqrt (1 - 1 / (n : ℝ))) := by
    calc |∑ j ∈ Finset.univ.erase j₀, p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j)|
      ≤ ∑ j ∈ Finset.univ.erase j₀, |p.eval (hM_sym.eigenvalues₀ j) * U a (e j) * U b (e j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase j₀, (1 / (n : ℝ)) * (|U a (e j)| * |U b (e j)|) := by
        apply Finset.sum_le_sum; intro j hj
        rw [abs_mul, abs_mul, mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have hj_val : j.val ≥ 1 := by
          have := (Finset.mem_erase.mp hj).1
          exact Nat.one_le_iff_ne_zero.mpr (fun h => this (Fin.ext h))
        exact le_of_lt (hp_small j hj_val)
      _ = (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.erase j₀, |U a (e j)| * |U b (e j)| := by
        rw [← Finset.mul_sum]
      _ ≤ (1 / (n : ℝ)) * (Real.sqrt (∑ j ∈ Finset.univ.erase j₀, U a (e j) ^ 2) *
          Real.sqrt (∑ j ∈ Finset.univ.erase j₀, U b (e j) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_cs (by positivity)
      _ = _ := by rw [h_rest a, h_rest b]
  have h_sq_lt : Real.sqrt (1 - 1 / (n : ℝ)) * Real.sqrt (1 - 1 / (n : ℝ)) < 1 := by
    have h_nn : (0 : ℝ) ≤ Real.sqrt (1 - 1 / n) := Real.sqrt_nonneg _
    exact mul_lt_one_of_nonneg_of_lt_one_left h_nn h_sqrt_lt (le_of_lt h_sqrt_lt)
  have h_bound : 1 / (n : ℝ) * (Real.sqrt (1 - 1 / (n : ℝ)) * Real.sqrt (1 - 1 / (n : ℝ))) < 1 / (n : ℝ) := by
    calc 1 / (n : ℝ) * (Real.sqrt (1 - 1 / (n : ℝ)) * Real.sqrt (1 - 1 / (n : ℝ)))
      < 1 / (n : ℝ) * 1 := by apply mul_lt_mul_of_pos_left h_sq_lt; positivity
      _ = 1 / (n : ℝ) := mul_one _
  exact lt_of_le_of_lt h_abs_le h_bound

lemma one_sub_lt_exp_neg_of_pos {lam : ℝ} (hlam_pos : 0 < lam) :
    1 - lam < Real.exp (-lam) := by
  linarith [Real.add_one_lt_exp (show (-lam : ℝ) ≠ 0 from by linarith)]

lemma spectral_gap_rpow_bound {lam : ℝ} (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 - lam) ^ (Real.log n / lam) < 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn_one_lt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n from by omega)
  have hdiv_pos : 0 < Real.log (n : ℝ) / lam := div_pos (Real.log_pos hn_one_lt) hlam_pos
  calc (1 - lam) ^ (Real.log (n : ℝ) / lam)
      < (Real.exp (-lam)) ^ (Real.log (n : ℝ) / lam) :=
        Real.rpow_lt_rpow (by linarith) (one_sub_lt_exp_neg_of_pos hlam_pos) hdiv_pos
    _ = 1 / (n : ℝ) := by
        rw [← Real.exp_mul]; ring_nf
        rw [show lam * Real.log ↑n * lam⁻¹ = Real.log ↑n from by field_simp]
        rw [Real.exp_neg, Real.exp_log hn_pos]

lemma spectral_gap_nat_pow_bound {lam : ℝ} (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 - lam) ^ ⌈Real.log n / lam⌉₊ < 1 / (n : ℝ) := by
  have hn_one_lt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n from by omega)
  have hdiv_pos : 0 < Real.log (n : ℝ) / lam :=
    div_pos (Real.log_pos hn_one_lt) hlam_pos
  have hceil_pos : (0 : ℝ) < (⌈Real.log (n : ℝ) / lam⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr hdiv_pos
  rw [← Real.rpow_natCast]
  rcases eq_or_lt_of_le hlam_le with hlam_eq | hlam_lt
  · subst hlam_eq; rw [sub_self, Real.zero_rpow (ne_of_gt hceil_pos)]; positivity
  · calc (1 - lam) ^ (⌈Real.log n / lam⌉₊ : ℝ)
        ≤ (1 - lam) ^ (Real.log n / lam) :=
          Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (Nat.le_ceil _)
      _ < 1 / (n : ℝ) := spectral_gap_rpow_bound hlam_pos hlam_le hn

theorem diameter_spectral_gap_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (_hd : 0 < d) (_hreg : G.IsRegularOfDegree d)
    (hcard : Fintype.card V ≥ 2)
    (μ₂ : ℝ) (_hμ₂_nonneg : 0 ≤ μ₂) (hμ₂_lt : μ₂ < 1)


    (hpointwise : ∀ (u v : V) (t : ℕ),
      |(((2 : ℝ)⁻¹ • (1 + (d : ℝ)⁻¹ • G.adjMatrix ℝ)) ^ t) u v -
        1 / (Fintype.card V : ℝ)| ≤ μ₂ ^ t) :
    G.diam ≤ ⌈Real.log (Fintype.card V) / (1 - μ₂)⌉₊ := by

  set lam := 1 - μ₂ with hlam_def
  have hlam_pos : 0 < lam := by linarith
  have hlam_le : lam ≤ 1 := by linarith

  set t := ⌈Real.log (Fintype.card V : ℝ) / lam⌉₊
  have h_pow_lt : (1 - lam) ^ t < 1 / (Fintype.card V : ℝ) :=
    spectral_gap_nat_pow_bound hlam_pos hlam_le hcard

  have h_mu_eq : 1 - lam = μ₂ := by linarith
  rw [h_mu_eq] at h_pow_lt

  set M := (2 : ℝ)⁻¹ • (1 + (d : ℝ)⁻¹ • G.adjMatrix ℝ) with hM_def
  have h_entry_pos : ∀ u v : V, 0 < (M ^ t) u v := by
    intro u v
    have hbound := hpointwise u v t
    have hlt : |(M ^ t) u v - 1 / (Fintype.card V : ℝ)| < 1 / (Fintype.card V : ℝ) :=
      lt_of_le_of_lt hbound h_pow_lt
    rw [abs_lt] at hlt
    linarith [hlt.1]

  suffices hediam : G.ediam ≤ ↑t from ENat.toNat_le_of_le_coe hediam
  apply SimpleGraph.ediam_le_of_edist_le
  intro u v

  have hMuv := h_entry_pos u v

  set W := (d : ℝ)⁻¹ • G.adjMatrix ℝ with hW_def
  have hM_eq : M = (2 : ℝ)⁻¹ • (1 + W) := rfl
  rw [hM_eq, smul_matrix_pow] at hMuv
  simp only [Matrix.smul_apply, smul_eq_mul] at hMuv

  suffices h_exists : ∃ k : ℕ, k ≤ t ∧ (G.adjMatrix ℝ ^ k) u v ≠ 0 by
    obtain ⟨k, hk_le, hk_ne⟩ := h_exists
    rw [G.adjMatrix_pow_apply_eq_card_walk] at hk_ne
    simp only [Ne, Nat.cast_eq_zero] at hk_ne
    rw [Fintype.card_eq_zero_iff] at hk_ne
    obtain ⟨⟨w, hw⟩⟩ := not_isEmpty_iff.mp hk_ne
    calc G.edist u v ≤ ↑w.length := SimpleGraph.edist_le w
      _ = ↑k := by rw [hw]
      _ ≤ ↑t := by exact_mod_cast hk_le

  by_contra h_all
  push_neg at h_all

  have hW_zero : ∀ k : ℕ, k ≤ t → (W ^ k) u v = 0 := by
    intro k hk
    rw [hW_def, smul_matrix_pow, Matrix.smul_apply, smul_eq_mul, h_all k hk, mul_zero]

  have hcomm : Commute (1 : Matrix V V ℝ) W := Commute.one_left W
  have h_expand : ((1 + W) ^ t) u v =
      ∑ m ∈ Finset.range (t + 1), (t.choose m : ℝ) * (W ^ (t - m)) u v := by
    conv_lhs => rw [hcomm.add_pow t]
    simp only [Matrix.sum_apply, one_pow, one_mul]
    congr 1; ext m
    simp only [Matrix.mul_apply, Matrix.natCast_apply, Nat.cast_ite, Nat.cast_zero,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

  have h_sum_zero : ((1 + W) ^ t) u v = 0 := by
    rw [h_expand]
    apply Finset.sum_eq_zero
    intro m _
    rw [hW_zero (t - m) (Nat.sub_le t m), mul_zero]

  rw [h_sum_zero, mul_zero] at hMuv
  exact lt_irrefl 0 hMuv

end ExpanderDiameter

namespace MagicPolynomial

open Polynomial Real



end MagicPolynomial

namespace SimpleGraph

noncomputable abbrev diameter {V : Type*} (G : SimpleGraph V) : ℕ := G.diam

end SimpleGraph
