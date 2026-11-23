/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.LatticesValuations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open DVRContext

variable (p : ℕ) [Fact (Nat.Prime p)]

noncomputable section

set_option maxHeartbeats 32000000

/-- *A non-identity permutation moves some index upward*: for any permutation $σ \ne 1$ on
$\text{Fin}\,m$, there is some $i$ with $i < σ(i)$. Used to detect off-diagonal terms in the
Iwahori-determinant computation. Proof: if $σ(i) \le i$ for all $i$, then strict inequality
somewhere combined with $\sum σ(j) = \sum j$ gives a contradiction. -/
lemma perm_exists_gt_of_ne_one {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : σ ≠ 1) :
    ∃ i : Fin m, i < σ i := by
  by_contra hall
  push Not at hall
  have hfix : ∀ i, σ i = i := by
    intro i
    apply le_antisymm (hall i)
    by_contra hlt; push Not at hlt
    have hsum_eq : ∑ j : Fin m, (σ j).val = ∑ j : Fin m, j.val :=
      Equiv.sum_comp σ (fun j : Fin m => j.val)
    have hsum_lt : ∑ j : Fin m, (σ j).val < ∑ j : Fin m, j.val :=
      Finset.sum_lt_sum (fun j _ => (hall j : (σ j).val ≤ j.val))
        ⟨i, Finset.mem_univ _, (hlt : (σ i).val < i.val)⟩
    linarith
  exact hσ (Equiv.ext hfix)

/-- *Product strictly less than $1$ when one factor is strictly less than $1$ and others are
$\le 1$*: pulled out as a separate fact to bound off-diagonal Iwahori products. -/
lemma prod_lt_one_of_le_one {m : ℕ} (f : Fin m → ℝ)
    (hnn : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ 1)
    {i₀ : Fin m} (hlt : f i₀ < 1) :
    ∏ i : Fin m, f i < 1 :=
  calc ∏ i : Fin m, f i
      = (∏ i ∈ Finset.univ.erase i₀, f i) * f i₀ := by
        rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)]; ring
    _ ≤ 1 * f i₀ := mul_le_mul_of_nonneg_right
        (Finset.prod_le_one (fun i _ => hnn i) (fun i _ => hle i)) (hnn i₀)
    _ = f i₀ := one_mul _
    _ < 1 := hlt

/-- *Ultrametric strict triangle inequality for a finite sum*: in $\mathbb{Q}_p$ (or any
ultrametric field), if every term $f(i)$ has norm $< C$, then so does the sum $\sum_i f(i)$.
Proof by induction on the finset using $\|x + y\| \le \max(\|x\|, \|y\|)$. -/
lemma ultrametric_norm_sum_lt {ι : Type*} {s : Finset ι} {f : ι → ℚ_[p]} {C : ℝ}
    (hC : 0 < C) (hbound : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, norm_zero]; exact hC
  | cons a s has ih =>
    rw [Finset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (hbound a (Finset.mem_cons_self a s))
        (ih (fun i hi => hbound i (Finset.mem_cons_of_mem hi))))

/-- *Iwahori determinant has $p$-adic norm $1$*: a matrix $g$ over $\mathbb{Q}_p$ that is in
Iwahori form (diagonal entries unit norm, above-diagonal $\le 1$, strictly below-diagonal
$< 1$) has $\|\det g\| = 1$. The proof expands the determinant as a sum over permutations:
the identity contributes a product of unit-norm entries giving norm $1$, while every
non-identity permutation forces at least one strictly-below-diagonal factor, making its
contribution have norm $< 1$. Ultrametricity then yields $\|\det g\| = 1$. -/
lemma iwahori_det_norm_eq_one {m : ℕ} (g : Matrix (Fin m) (Fin m) ℚ_[p])
    (hdiag : ∀ i, ‖g i i‖ = 1)
    (habove : ∀ i j, i < j → ‖g i j‖ ≤ 1)
    (hbelow : ∀ i j, j < i → ‖g i j‖ < 1) :
    ‖g.det‖ = 1 := by
  have hall_le : ∀ i j, ‖g i j‖ ≤ 1 := fun i j => by
    rcases lt_trichotomy i j with h | h | h
    · exact habove i j h
    · rw [h]; exact le_of_eq (hdiag j)
    · exact le_of_lt (hbelow i j h)
  rw [Matrix.det_apply]
  set f := fun σ : Equiv.Perm (Fin m) => Equiv.Perm.sign σ • ∏ i : Fin m, g (σ i) i
  have hid_norm : ‖f 1‖ = 1 := by
    simp only [f, Equiv.Perm.sign_one, Equiv.Perm.one_apply]
    have : (1 : ℤˣ) • (∏ x : Fin m, g x x) = ∏ x : Fin m, g x x := one_smul ℤˣ _
    rw [this, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hdiag i)
  have hother : ∀ σ : Equiv.Perm (Fin m), σ ≠ 1 → ‖f σ‖ < 1 := by
    intro σ hσ
    simp only [f]
    have hsmul : ‖Equiv.Perm.sign σ • ∏ i, g (σ i) i‖ = ‖∏ i, g (σ i) i‖ := by
      rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
    rw [hsmul, norm_prod]
    obtain ⟨i₀, hi₀⟩ := perm_exists_gt_of_ne_one σ hσ
    exact prod_lt_one_of_le_one _ (fun i => norm_nonneg _) (fun i => hall_le _ _) (hbelow _ _ hi₀)
  rw [show ∑ σ : Equiv.Perm (Fin m), f σ = f 1 + ∑ σ ∈ Finset.univ.erase 1, f σ from
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 1)).symm]
  have hrest : ‖∑ σ ∈ Finset.univ.erase 1, f σ‖ < 1 :=
    ultrametric_norm_sum_lt p one_pos (fun σ hσ => hother σ (Finset.ne_of_mem_erase hσ))
  have hne : ‖f 1‖ ≠ ‖∑ σ ∈ Finset.univ.erase 1, f σ‖ := by
    rw [hid_norm]; exact ne_of_gt hrest
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hid_norm, max_eq_left (le_of_lt hrest)] at heq
  exact heq

/-- *The $p$-adic DVR context*: instantiates the `DVRContext` framework with $k = \mathbb{Q}_p$,
$\mathfrak{o} = \mathbb{Z}_p$, the natural inclusion as embed, and the uniformizer $p$. The
parameter $n$ records the relevant dimension (e.g. of an Iwahori subgroup of $GL_n$). -/
def padicDVRContext (n : ℕ) (hn : 0 < n) : DVRContext where
  k := ℚ_[p]
  𝔬 := ℤ_[p]
  embed := (PadicInt.subring p).subtype
  embed_injective := Subtype.coe_injective
  uniformizer := (p : ℤ_[p])
  n := n
  n_pos := hn

variable {p} (n : ℕ) (hn : 0 < n)

/-- *Membership in the $p$-adic valuation subring via norm*: $x \in \mathbb{Z}_p$ (as image
of `embed`) iff $\|x\|_p \le 1$. -/
lemma padic_isInO_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isInO x ↔ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨r, hr⟩; rw [← hr]; exact PadicInt.norm_le_one r
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

/-- *Membership in the $p$-adic maximal ideal via norm*: $x \in p\mathbb{Z}_p$ iff
$\|x\|_p < 1$. Uses `PadicInt.norm_lt_one_iff_dvd` to translate between divisibility by $p$
and norm being strictly less than $1$. -/
lemma padic_isInMaxIdeal_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isInMaxIdeal x ↔ ‖x‖ < 1 := by
  constructor
  · rintro ⟨r, hr_mem, hr_eq⟩
    rw [← hr_eq]
    have hdvd : (p : ℤ_[p]) ∣ r := by
      rw [DVRContext.maxIdeal, Ideal.mem_span_singleton] at hr_mem; exact hr_mem
    exact (PadicInt.norm_lt_one_iff_dvd r).mpr hdvd
  · intro h
    have hle : ‖x‖ ≤ 1 := le_of_lt h
    let r : ℤ_[p] := ⟨x, hle⟩
    have hr_dvd : (p : ℤ_[p]) ∣ r := (PadicInt.norm_lt_one_iff_dvd r).mp h
    refine ⟨r, ?_, rfl⟩
    rw [DVRContext.maxIdeal, Ideal.mem_span_singleton]; exact hr_dvd

/-- *Units of $\mathbb{Z}_p$ via norm*: $x \in \mathbb{Z}_p^\times$ iff $\|x\|_p = 1$. -/
lemma padic_isUnitInO_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isUnitInO x ↔ ‖x‖ = 1 := by
  constructor
  · rintro ⟨r, hr_unit, hr_eq⟩; rw [← hr_eq]; exact PadicInt.isUnit_iff.mp hr_unit
  · intro h; exact ⟨⟨x, le_of_eq h⟩, PadicInt.isUnit_iff.mpr h, rfl⟩

/-- *Iwahori matrices over $\mathbb{Q}_p$ have unit determinant*: phrased in the abstract
`DVRContext` language as a wrapper around `iwahori_det_norm_eq_one`. -/
lemma padic_iwahori_det_unit (g : Matrix (Fin n) (Fin n) ℚ_[p])
    (hdiag : ∀ i, (padicDVRContext p n hn).isUnitInO (g i i))
    (habove : ∀ i j, i < j → (padicDVRContext p n hn).isInO (g i j))
    (hbelow : ∀ i j, j < i → (padicDVRContext p n hn).isInMaxIdeal (g i j)) :
    (padicDVRContext p n hn).isUnitInO g.det := by
  rw [padic_isUnitInO_iff]
  have hdiag' : ∀ i, ‖g i i‖ = 1 := fun i => (padic_isUnitInO_iff n hn _).mp (hdiag i)
  have habove' : ∀ i j, i < j → ‖g i j‖ ≤ 1 :=
    fun i j h => (padic_isInO_iff n hn _).mp (habove i j h)
  have hbelow' : ∀ i j, j < i → ‖g i j‖ < 1 :=
    fun i j h => (padic_isInMaxIdeal_iff n hn _).mp (hbelow i j h)
  exact iwahori_det_norm_eq_one p g hdiag' habove' hbelow'

/-- *`DVRClosure` instance for the $p$-adic context*: assembles all closure properties of
$\mathbb{Z}_p$ inside $\mathbb{Q}_p$ — closed under $0$, $1$, negation, addition,
multiplication, integer casts, and inverses of units; plus Iwahori-determinant unit. -/
instance padicDVRClosure : DVRClosure (padicDVRContext p n hn) where
  isInO_zero := ⟨0, rfl⟩
  isInO_one := ⟨1, rfl⟩
  isInO_neg := fun {x} ⟨r, hr⟩ => ⟨-r, by subst hr; rfl⟩
  isInO_add := fun {x y} ⟨r, hr⟩ ⟨s, hs⟩ => ⟨r + s, by subst hr; subst hs; rfl⟩
  isInO_mul := fun {x y} ⟨r, hr⟩ ⟨s, hs⟩ => ⟨r * s, by subst hr; subst hs; rfl⟩
  isInO_intCast := fun m => ⟨(m : ℤ_[p]), by norm_cast⟩
  isUnitInO_inv := fun {x} hx => by
    have hx' := (padic_isUnitInO_iff n hn x).mp hx
    exact (padic_isInO_iff n hn x⁻¹).mpr (by simp [norm_inv, hx'])
  iwahori_det_unit := padic_iwahori_det_unit n hn

/-- *`DVRTopology` instance for the $p$-adic context*: equips the $p$-adic DVR context with
its norm topology (a `NormedField`) and the ultrametric inequality, registering the
norm-characterisations of `isInO`, `isInMaxIdeal`, and `isUnitInO`. -/
instance padicDVRTopology : DVRContext.DVRTopology (padicDVRContext p n hn) where
  instNormedField := inferInstanceAs (NormedField ℚ_[p])
  instUltrametric := Padic.instIsUltrametricDist p
  isInO_iff_norm_le_one := padic_isInO_iff n hn
  isInMaxIdeal_iff_norm_lt_one := padic_isInMaxIdeal_iff n hn
  isUnitInO_iff_norm_eq_one := padic_isUnitInO_iff n hn

end
