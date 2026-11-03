/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Atlas.AlgebraicGeometryI.code.SerreDualityStatement

set_option maxHeartbeats 800000

noncomputable section

namespace Lec24

/-- The dimension `h⁰(ℙ¹, O(d)) = max(d + 1, 0)`. -/
def h0_P1 (d : ℤ) : ℕ := (d + 1).toNat

/-- The dimension `h¹(ℙ¹, O(d)) = max(-d - 1, 0)`, dual to `h⁰(ℙ¹, O(-d - 2))`. -/
def h1_P1 (d : ℤ) : ℕ := (-d - 1).toNat

/-- Euler characteristic of `O(d)` on `ℙ¹`: `χ(O(d)) = h⁰ - h¹ = d + 1`. -/
theorem euler_char_O_d_P1 (d : ℤ) : (h0_P1 d : ℤ) - (h1_P1 d : ℤ) = d + 1 := by
  unfold h0_P1 h1_P1
  by_cases h : 0 ≤ d + 1
  · rw [Int.toNat_of_nonneg h]
    by_cases h2 : 0 ≤ -d - 1
    · rw [Int.toNat_of_nonneg h2]; omega
    · rw [Int.toNat_eq_zero.mpr (by omega : -d - 1 ≤ 0)]; omega
  · rw [Int.toNat_eq_zero.mpr (by omega : d + 1 ≤ 0)]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -d - 1)]; omega

/-- Axiomatic data for a locally free sheaf on `ℙ¹_k`: its rank and degree together with
the cohomology dimensions of its Serre twists, satisfying the expected Euler-characteristic
formula. -/
structure LocallyFreeSheafOnP1 where
  rank : ℕ
  degree : ℤ
  h0_twist : ℤ → ℕ
  h1_twist : ℤ → ℕ
  euler_char_twist : ∀ d : ℤ,
    (h0_twist d : ℤ) - (h1_twist d : ℤ) = degree + rank * d + rank

/-- The split bundle `⨁ᵢ O_{ℙ¹}(dᵢ)` on `ℙ¹`, packaged as a `LocallyFreeSheafOnP1`. -/
def splitBundle (n : ℕ) (degrees : Fin n → ℤ) : LocallyFreeSheafOnP1 where
  rank := n
  degree := ∑ i, degrees i
  h0_twist := fun d => ∑ i : Fin n, h0_P1 (degrees i + d)
  h1_twist := fun d => ∑ i : Fin n, h1_P1 (degrees i + d)
  euler_char_twist := by
    intro d
    push_cast
    have key : ∀ i : Fin n,
        (h0_P1 (degrees i + d) : ℤ) - (h1_P1 (degrees i + d) : ℤ) = degrees i + d + 1 :=
      fun i => euler_char_O_d_P1 (degrees i + d)
    rw [← Finset.sum_sub_distrib]
    simp_rw [key]
    simp [Finset.sum_add_distrib]


/-- Numerical data attached to a locally free sheaf on a curve: rank, degree, and the
zeroth/first cohomology dimensions. -/
structure LocallyFreeSheafData where
  rk : ℕ
  deg : ℤ
  h0 : ℕ
  h1 : ℕ

/-- Axiomatic data of a smooth complete curve together with a category of coherent sheaves,
their Serre duals, the structure sheaf, the canonical sheaf and the numerical Riemann-Roch
and Serre duality relations they satisfy. -/
structure SmoothCompleteCurveWithSheaves where
  genus : ℕ
  degK : ℤ
  Sheaf : Type
  data : Sheaf → LocallyFreeSheafData
  serreDual : Sheaf → Sheaf
  structureSheaf : Sheaf
  canonicalSheaf : Sheaf

  structureSheaf_rk : (data structureSheaf).rk = 1
  structureSheaf_deg : (data structureSheaf).deg = 0
  structureSheaf_h0 : (data structureSheaf).h0 = 1
  structureSheaf_h1 : (data structureSheaf).h1 = genus

  canonicalSheaf_rk : (data canonicalSheaf).rk = 1
  canonicalSheaf_deg : (data canonicalSheaf).deg = degK

  serreDual_rk : ∀ E, (data (serreDual E)).rk = (data E).rk
  serreDual_deg : ∀ E,
    (data (serreDual E)).deg = (data E).rk * degK - (data E).deg
  serreDual_structure : data (serreDual structureSheaf) = data canonicalSheaf
  serreDual_canonical : data (serreDual canonicalSheaf) = data structureSheaf
  serreDual_involutive : ∀ E, data (serreDual (serreDual E)) = data E
  chi_determined_by_rk_deg : ∀ E : Sheaf,
    ((data E).h0 : ℤ) - ((data E).h1 : ℤ) =
    ↑(data E).rk * (↑(data structureSheaf).h0 - ↑(data structureSheaf).h1) +
    (data E).deg

  serre_duality : ∀ E : Sheaf,
    (data E).h0 = (data (serreDual E)).h1

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The Euler characteristic `χ(E) = h⁰(E) - h¹(E)` of a coherent sheaf on the curve. -/
def chi (E : X.Sheaf) : ℤ := ((X.data E).h0 : ℤ) - ((X.data E).h1 : ℤ)

/-- Riemann-Roch (Theorem 24.2): For a coherent sheaf `E` on a smooth complete curve of
genus `g`, `χ(E) = deg(E) + rank(E) · (1 - g)`. -/
theorem riemann_roch (E : X.Sheaf) :
    ((X.data E).h0 : ℤ) - ((X.data E).h1 : ℤ) =
    (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) := by
  have hchi := X.chi_determined_by_rk_deg E
  rw [X.structureSheaf_h0, X.structureSheaf_h1] at hchi
  push_cast at hchi ⊢
  linarith

/-- Restatement of Riemann-Roch in terms of `chi`: `χ(E) = deg E + rk E · (1 - g)`. -/
theorem chi_eq (E : X.Sheaf) :
    X.chi E = (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) :=
  X.riemann_roch E

/-- `χ(O_X) = 1 - g` for the structure sheaf of a smooth complete curve of genus `g`. -/
theorem chi_structure : X.chi X.structureSheaf = 1 - (X.genus : ℤ) := by
  rw [chi_eq, X.structureSheaf_deg, X.structureSheaf_rk]; push_cast; ring

end SmoothCompleteCurveWithSheaves

/-- Serre duality (Theorem 24.3): `h⁰(E) = h¹(E^∨ ⊗ ω_X)`, here packaged via the Serre dual. -/
theorem serre_duality_dimension (X : SmoothCompleteCurveWithSheaves)
    (E : X.Sheaf) :
    (X.data E).h0 = (X.data (X.serreDual E)).h1 :=
  X.serre_duality E

/-- Serre duality in reverse: `h¹(E) = h⁰(E^∨ ⊗ ω_X)`. -/
theorem serre_duality_reverse (X : SmoothCompleteCurveWithSheaves)
    (E : X.Sheaf) :
    (X.data E).h1 = (X.data (X.serreDual E)).h0 := by
  have hsd := serre_duality_dimension X (X.serreDual E)
  rw [X.serreDual_involutive] at hsd
  exact hsd.symm

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- Arithmetic genus equals geometric genus: `h⁰(ω_X) = g`. -/
theorem arithmetic_eq_geometric_genus :
    (X.data X.canonicalSheaf).h0 = X.genus := by
  have hsd := serre_duality_dimension X X.canonicalSheaf
  rw [X.serreDual_canonical] at hsd
  rw [hsd, X.structureSheaf_h1]

/-- `h¹(ω_X) = 1`, the Serre dual of `h⁰(O_X) = 1`. -/
theorem h1_canonical_eq_one : (X.data X.canonicalSheaf).h1 = 1 := by
  have hsd := serre_duality_dimension X X.structureSheaf
  rw [X.serreDual_structure] at hsd
  rw [X.structureSheaf_h0] at hsd
  exact hsd.symm

/-- The degree of the canonical sheaf: `deg(ω_X) = 2g - 2`. -/
theorem deg_canonical_eq : X.degK = 2 * (X.genus : ℤ) - 2 := by
  have hRR := X.riemann_roch X.canonicalSheaf
  rw [X.canonicalSheaf_deg, X.canonicalSheaf_rk,
      X.arithmetic_eq_geometric_genus, X.h1_canonical_eq_one] at hRR
  push_cast at hRR ⊢; omega

/-- Riemann form of Riemann-Roch: `h⁰(E) - h⁰(E^∨ ⊗ ω_X) = deg E + rk E · (1 - g)`,
combining Riemann-Roch with Serre duality. -/
theorem riemann_form (E : X.Sheaf) :
    ((X.data E).h0 : ℤ) - ((X.data (X.serreDual E)).h0 : ℤ) =
    (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) := by
  have hsd_rev := serre_duality_reverse X E
  have hRR := X.riemann_roch E
  have : ((X.data (X.serreDual E)).h0 : ℤ) = ((X.data E).h1 : ℤ) := by
    exact_mod_cast hsd_rev.symm
  linarith

/-- High-degree case: for a line bundle `L` with `h⁰(L^∨ ⊗ ω_X) = 0`, Riemann-Roch reduces to
`h⁰(L) = deg L + 1 - g`. -/
theorem h0_high_degree (E : X.Sheaf)
    (hrk : (X.data E).rk = 1)
    (hvanish : (X.data (X.serreDual E)).h0 = 0) :
    ((X.data E).h0 : ℤ) = (X.data E).deg + 1 - (X.genus : ℤ) := by
  have hsd_rev := serre_duality_reverse X E
  have hRR := X.riemann_roch E
  rw [hsd_rev, hvanish] at hRR
  rw [hrk] at hRR
  push_cast at hRR ⊢
  linarith

end SmoothCompleteCurveWithSheaves

/-- Axiomatic data for computing `K_0(Coh X)` on a smooth curve: a class of sheaves with
rank and degree functions, short exact sequences, plus designated structure sheaf and
skyscraper-at-a-point with the expected rank/degree values. -/
structure SmoothCurveK0Data where
  CohSheaf : Type
  rank : CohSheaf → ℕ
  deg : CohSheaf → ℤ
  SES : CohSheaf → CohSheaf → CohSheaf → Prop
  O_X : CohSheaf
  O_x : CohSheaf
  O_X_rank : rank O_X = 1
  O_X_deg : deg O_X = 0
  O_x_rank : rank O_x = 0
  O_x_deg : deg O_x = 1
  rank_additive : ∀ A B C, SES A B C → rank B = rank A + rank C
  deg_additive : ∀ A B C, SES A B C → deg B = deg A + deg C

/-- The subgroup of `ℤ[CohSheaf]` generated by the relations `[A] + [C] - [B]` coming from
short exact sequences `0 → A → B → C → 0`. Quotienting yields `K_0(Coh X)`. -/
def sesRelations (X : SmoothCurveK0Data) : AddSubgroup (FreeAbelianGroup X.CohSheaf) :=
  AddSubgroup.closure
    { r | ∃ A B C, X.SES A B C ∧
        r = FreeAbelianGroup.of A + FreeAbelianGroup.of C - FreeAbelianGroup.of B }

/-- The Grothendieck group `K_0(Coh X)`: the free abelian group on coherent sheaves modulo
the short-exact-sequence relations. -/
abbrev K0Coh (X : SmoothCurveK0Data) : Type :=
  FreeAbelianGroup X.CohSheaf ⧸ sesRelations X

/-- The class `[F]` of a coherent sheaf `F` in `K_0(Coh X)`. -/
def K0Coh.classOf (X : SmoothCurveK0Data) (F : X.CohSheaf) : K0Coh X :=
  QuotientAddGroup.mk' (sesRelations X) (FreeAbelianGroup.of F)

/-- The group homomorphism `ℤ ⊕ ℤ → K_0(Coh X)` sending `(r, d) ↦ r·[O_X] + d·[O_x]`,
which is shown by Lemma 35 to be surjective. -/
def rankDegToK0 (X : SmoothCurveK0Data) : ℤ × ℤ →+ K0Coh X where
  toFun := fun ⟨r, d⟩ => r • K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp [add_smul]; abel

/-- Strong-induction helper: assuming torsion sheaves decompose as multiples of `[O_x]`
and rank can always be reduced via an `O_X`-direct-summand, every class `[F]` lies in the
image of `(r, d) ↦ r[O_X] + d[O_x]`. -/
lemma classOf_in_range (X : SmoothCurveK0Data)
    (torsion_decomp : ∀ F : X.CohSheaf, X.rank F = 0 →
      ∃ (n : ℤ), K0Coh.classOf X F = n • K0Coh.classOf X X.O_x)
    (rank_reduction : ∀ F : X.CohSheaf, 0 < X.rank F →
      ∃ (d : ℤ) (Q : X.CohSheaf),
        X.rank Q < X.rank F ∧
        K0Coh.classOf X F = K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x +
          K0Coh.classOf X Q)
    (F : X.CohSheaf) : K0Coh.classOf X F ∈ (rankDegToK0 X).range := by
  have : ∀ n : ℕ, ∀ G : X.CohSheaf, X.rank G = n →
      K0Coh.classOf X G ∈ (rankDegToK0 X).range := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro G hG
      by_cases hn : n = 0
      ·
        obtain ⟨m, hm⟩ := torsion_decomp G (by omega)
        rw [hm]; exact ⟨⟨0, m⟩, by simp [rankDegToK0]⟩
      ·
        obtain ⟨d, Q, hQ_rank, hQ_eq⟩ := rank_reduction G (by omega)
        rw [hQ_eq]
        have hQ_mem := ih (X.rank Q) (by omega) Q rfl
        obtain ⟨⟨r₃, d₃⟩, h₃⟩ := hQ_mem
        refine ⟨⟨1 + r₃, d + d₃⟩, ?_⟩
        simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₃ ⊢
        rw [← h₃]; module
  exact this (X.rank F) F rfl

/-- Lemma 35 (generators of `K_0`): On a smooth curve, the classes `[O_X]` and `[O_x]`
generate `K_0(Coh X)`, i.e. the rank-degree map is surjective. -/
theorem K0_generators_lemma35 (X : SmoothCurveK0Data)
    (torsion_decomp : ∀ F : X.CohSheaf, X.rank F = 0 →
      ∃ (n : ℤ), K0Coh.classOf X F = n • K0Coh.classOf X X.O_x)
    (rank_reduction : ∀ F : X.CohSheaf, 0 < X.rank F →
      ∃ (d : ℤ) (Q : X.CohSheaf),
        X.rank Q < X.rank F ∧
        K0Coh.classOf X F = K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x +
          K0Coh.classOf X Q) :
    Function.Surjective (rankDegToK0 X) := by
  intro y

  induction y using QuotientAddGroup.induction_on with
  | H z =>

    induction z using FreeAbelianGroup.induction_on with
    | zero => exact ⟨⟨0, 0⟩, by simp [rankDegToK0]⟩
    | of F => exact classOf_in_range X torsion_decomp rank_reduction F
    | neg F hF =>
      obtain ⟨⟨r, d⟩, hr⟩ := hF
      refine ⟨⟨-r, -d⟩, ?_⟩
      simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hr ⊢
      rw [QuotientAddGroup.mk_neg, neg_smul, neg_smul, ← neg_add, hr]
    | add x y hx hy =>
      obtain ⟨⟨r₁, d₁⟩, h₁⟩ := hx
      obtain ⟨⟨r₂, d₂⟩, h₂⟩ := hy
      refine ⟨⟨r₁ + r₂, d₁ + d₂⟩, ?_⟩
      simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁ h₂ ⊢
      rw [QuotientAddGroup.mk_add, ← h₁, ← h₂, add_smul, add_smul]; abel


/-- Goal 185 (degree of canonical sheaf): `deg(ω_X) = 2g - 2`, a corollary of Riemann-Roch
applied to `ω_X` and Serre duality. -/
theorem goal_185 (X : SmoothCompleteCurveWithSheaves) :
    X.degK = 2 * (X.genus : ℤ) - 2 :=
  X.deg_canonical_eq

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The arithmetic genus `p_a := 1 - χ(O_X)`. -/
def arithmeticGenus_pa : ℤ :=
  1 - X.chi X.structureSheaf

/-- The geometric genus `p_g := h⁰(ω_X)`. -/
def geometricGenus_pg : ℕ :=
  (X.data X.canonicalSheaf).h0

/-- The arithmetic genus agrees with `g`: `p_a = g`. -/
theorem pa_eq_genus : X.arithmeticGenus_pa = (X.genus : ℤ) := by
  unfold arithmeticGenus_pa
  rw [X.chi_structure]
  ring

/-- The geometric genus agrees with `g`: `p_g = g`. -/
theorem pg_eq_genus : X.geometricGenus_pg = X.genus :=
  X.arithmetic_eq_geometric_genus

end SmoothCompleteCurveWithSheaves

end Lec24
