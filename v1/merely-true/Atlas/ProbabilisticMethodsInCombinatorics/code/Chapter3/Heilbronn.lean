/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 800000

open Set Finset

namespace Heilbronn

/-- The closed unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)

/-- The area of the triangle with vertices $p, q, r \in \mathbb{R}^2$, computed via the
absolute value of half the cross product of $(q-p)$ and $(r-p)$. -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1))| / 2

/-- The minimum triangle area among all triples of distinct points in a finite set
$S \subseteq \mathbb{R}^2$. -/
noncomputable def minTriangleArea (S : Finset (ℝ × ℝ)) : ℝ :=
  sInf {a : ℝ | ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ a = triangleArea p q r}

/-- The Heilbronn number $H(n)$: the supremum, over all $n$-point configurations in the
unit square, of the minimum triangle area among triples of points in the configuration. -/
noncomputable def heilbronnNumber (n : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ S : Finset (ℝ × ℝ), S.card = n ∧
    (↑S : Set (ℝ × ℝ)) ⊆ unitSquare ∧ a = minTriangleArea S}

/-- For prime $p$ and $i \in \{0, 1, \dots, p-1\}$, the point $(i/p, (i^2 \bmod p)/p)$
on the discretized parabola in the unit square. -/
noncomputable def parabolaPoint (p : ℕ) (i : Fin p) : ℝ × ℝ :=
  ((i.val : ℝ) / (p : ℝ), ((i.val ^ 2 % p : ℕ) : ℝ) / (p : ℝ))

/-- The integer cross-product determinant associated with three points on the parabola at
indices $a, b, c \in \mathbb{F}_p$. -/
def intDetFin {p : ℕ} (a b c : Fin p) : ℤ :=
  ((b.val : ℤ) - a.val) * (((c.val ^ 2 % p : ℕ) : ℤ) - ((a.val ^ 2 % p : ℕ) : ℤ)) -
  (((b.val ^ 2 % p : ℕ) : ℤ) - ((a.val ^ 2 % p : ℕ) : ℤ)) * ((c.val : ℤ) - a.val)

/-- Modulo $p$, the determinant `intDetFin a b c` equals the Vandermonde-type product
$(b-a)(c-a)(c-b)$ in $\mathbb{F}_p$. -/
lemma intDetFin_cast_eq_vandermonde {p : ℕ} (a b c : Fin p) :
    ((intDetFin a b c : ℤ) : ZMod p) =
    ((b.val : ZMod p) - a.val) * ((c.val : ZMod p) - a.val) *
    ((c.val : ZMod p) - b.val) := by
  simp only [intDetFin]; push_cast; ring

/-- Two elements of `Fin p` are equal whenever their values agree in $\mathbb{Z}/p\mathbb{Z}$. -/
lemma fin_eq_of_zmod_eq {p : ℕ} (a b : Fin p)
    (h : (a.val : ZMod p) = (b.val : ZMod p)) : a = b :=
  Fin.ext (ZMod.val_natCast_of_lt a.isLt ▸ ZMod.val_natCast_of_lt b.isLt ▸
    congr_arg ZMod.val h)

/-- For prime $p$ and pairwise distinct $a, b, c \in \mathbb{F}_p$, the determinant
`intDetFin a b c` is nonzero, since the Vandermonde product modulo $p$ is nonzero. -/
lemma intDetFin_ne_zero {p : ℕ} (hp : Nat.Prime p) (a b c : Fin p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : intDetFin a b c ≠ 0 := by
  intro h
  have h1 : ((intDetFin a b c : ℤ) : ZMod p) = 0 := by simp [h]
  rw [intDetFin_cast_eq_vandermonde] at h1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr (fun heq => hab (fin_eq_of_zmod_eq b a heq).symm))
    (sub_ne_zero.mpr (fun heq => hac (fin_eq_of_zmod_eq c a heq).symm)))
    (sub_ne_zero.mpr (fun heq => hbc (fin_eq_of_zmod_eq c b heq).symm))) h1

/-- The signed area cross-product of three parabola points equals the integer determinant
`intDetFin a b c` divided by $p^2$. -/
lemma cross_product_formula (p : ℕ) (hp : 0 < p) (a b c : Fin p) :
    ((parabolaPoint p b).1 - (parabolaPoint p a).1) *
    ((parabolaPoint p c).2 - (parabolaPoint p a).2) -
    ((parabolaPoint p b).2 - (parabolaPoint p a).2) *
    ((parabolaPoint p c).1 - (parabolaPoint p a).1) =
    (intDetFin a b c : ℝ) / (p : ℝ) ^ 2 := by
  simp only [parabolaPoint, intDetFin]
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  field_simp; norm_cast

/-- For prime $p$ and pairwise distinct indices, any triangle formed by three parabola
points has area at least $\frac{1}{2p^2}$. -/
lemma triangleArea_parabolaPoint_bound {p : ℕ} (hp : Nat.Prime p)
    (a b c : Fin p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triangleArea (parabolaPoint p a) (parabolaPoint p b) (parabolaPoint p c) ≥
    1 / (2 * (p : ℝ) ^ 2) := by
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  simp only [triangleArea]
  rw [cross_product_formula p hp.pos a b c, abs_div,
      abs_of_pos (show (0:ℝ) < (p:ℝ)^2 from by positivity), div_div]
  have hdet_abs : (1 : ℝ) ≤ |(intDetFin a b c : ℝ)| := by
    exact_mod_cast Int.one_le_abs (intDetFin_ne_zero hp a b c hab hac hbc)
  rw [ge_iff_le, show 2 * (p : ℝ) ^ 2 = (p : ℝ) ^ 2 * 2 from by ring]
  exact div_le_div_of_nonneg_right hdet_abs (by positivity)

/-- The map `parabolaPoint p` from `Fin p` to $\mathbb{R}^2$ is injective. -/
lemma parabolaPoint_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (parabolaPoint p) := by
  intro i j hij
  simp only [parabolaPoint, Prod.mk.injEq] at hij
  have hpp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  have h1 := hij.1
  rw [div_eq_div_iff hpp hpp] at h1
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hpp h1))

/-- Each parabola point $(i/p, (i^2 \bmod p)/p)$ lies in the closed unit square $[0,1]^2$. -/
lemma parabolaPoint_mem_unitSquare {p : ℕ} (hp : Nat.Prime p) (i : Fin p) :
    parabolaPoint p i ∈ unitSquare := by
  simp only [parabolaPoint, unitSquare, Set.mem_Icc, Prod.le_def]
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  exact ⟨⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hpp),
          div_nonneg (Nat.cast_nonneg _) (le_of_lt hpp)⟩,
         ⟨(div_le_one hpp).mpr (by exact_mod_cast (Fin.is_lt i).le),
          (div_le_one hpp).mpr (by exact_mod_cast (Nat.mod_lt _ hp.pos).le)⟩⟩

/-- **Theorem 3.2.3 (Heilbronn lower bound).** There exists a constant $c > 0$ such that
for every $n \geq 3$ there are $n$ points in the unit square $[0,1]^2$ with every triangle
they form having area at least $c/n^2$. -/
theorem heilbronn_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    ∃ S : Finset (ℝ × ℝ), S.card = n ∧ (↑S : Set (ℝ × ℝ)) ⊆ unitSquare ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → x ≠ z → y ≠ z →
    triangleArea x y z ≥ c / (n : ℝ) ^ 2 := by
  refine ⟨1 / 8, by norm_num, fun n hn => ?_⟩

  have hn_ne : n ≠ 0 := by omega
  have hn_pos : (0 : ℕ) < n := by omega
  obtain ⟨p, hp_prime, hnp, hp2n⟩ := Nat.bertrand n hn_ne
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hnn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos

  set S_full := (Finset.univ : Finset (Fin p)).image (parabolaPoint p)
  have hcard_full : S_full.card = p := by
    rw [Finset.card_image_of_injective _ (parabolaPoint_injective hp_prime.pos),
        Finset.card_fin]
  obtain ⟨S, hS_sub, hS_card⟩ :=
    Finset.exists_subset_card_eq (hcard_full ▸ Nat.le_of_lt hnp)
  refine ⟨S, hS_card, ?_, ?_⟩

  · intro x hx
    have hxf : x ∈ S_full := hS_sub hx
    simp only [S_full, Finset.mem_image, Finset.mem_univ, true_and] at hxf
    obtain ⟨i, rfl⟩ := hxf
    exact parabolaPoint_mem_unitSquare hp_prime i

  · intro x hx y hy z hz hxy hxz hyz
    have hxf : x ∈ S_full := hS_sub hx
    have hyf : y ∈ S_full := hS_sub hy
    have hzf : z ∈ S_full := hS_sub hz
    simp only [S_full, Finset.mem_image, Finset.mem_univ, true_and] at hxf hyf hzf
    obtain ⟨i, rfl⟩ := hxf
    obtain ⟨j, rfl⟩ := hyf
    obtain ⟨k, rfl⟩ := hzf
    have hij : i ≠ j := fun h => hxy (congrArg _ h)
    have hik : i ≠ k := fun h => hxz (congrArg _ h)
    have hjk : j ≠ k := fun h => hyz (congrArg _ h)

    have h_area := triangleArea_parabolaPoint_bound hp_prime i j k hij hik hjk

    have h_bound : (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≥ 1 / 8 / (n : ℝ) ^ 2 := by
      rw [ge_iff_le, div_div,
          div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * (n:ℝ)^2)
            (by positivity : (0:ℝ) < 2 * (p:ℝ)^2)]
      have h : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
      nlinarith [sq_nonneg ((p : ℝ)), sq_nonneg ((n : ℝ))]
    linarith

end Heilbronn
