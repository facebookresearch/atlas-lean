/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Eval.Coeff

universe u

/-- The inverse limit of a sequence of types $S_0, S_1, \ldots$ connected by transition maps
$f_n : S_{n+1} \to S_n$: a coherent sequence $(s_n)_{n \in \mathbb{N}}$ with $s_n \in S_n$ and
$f_n(s_{n+1}) = s_n$ for every $n$. -/
def InverseLimit (S : ℕ → Type u) (f : (n : ℕ) → S (n + 1) → S n) : Type u :=
  { s : (n : ℕ) → S n // ∀ n, f n (s (n + 1)) = s n }

namespace InverseLimit

variable {S : ℕ → Type u} (fn : (n : ℕ) → S (n + 1) → S n)

/-- The $k$-fold image chain `imgCh fn n k`: the subset of $S_n$ obtained by iterating the
transition maps $k$ times starting from $S_{n+k}$. Forms an antitone family in $k$ that captures
which elements of $S_n$ lift back through the inverse system. -/
def imgCh : (n k : ℕ) → Set (S n)
  | _, 0 => Set.univ
  | n, k + 1 => fn n '' (imgCh (n + 1) k)

/-- The image chains are nested: `imgCh fn n (k+1) ⊆ imgCh fn n k`. -/
lemma imgCh_succ_subset (n k : ℕ) : imgCh fn n (k + 1) ⊆ imgCh fn n k := by
  induction k generalizing n with
  | zero => intro x _; exact Set.mem_univ x
  | succ k ih => exact Set.image_mono (ih (n + 1))

/-- The image chains `imgCh fn n k` form an antitone family in $k$. -/
lemma imgCh_antitone (n : ℕ) : Antitone (imgCh fn n) :=
  antitone_nat_of_succ_le (imgCh_succ_subset fn n)

/-- If every $S_n$ is nonempty, every image chain `imgCh fn n k` is nonempty. -/
lemma imgCh_nonempty [∀ n, Nonempty (S n)] (n k : ℕ) : (imgCh fn n k).Nonempty := by
  induction k generalizing n with
  | zero => exact Set.univ_nonempty
  | succ k ih => exact Set.Nonempty.image _ (ih (n + 1))

/-- Any antitone function $g : \mathbb{N} \to \mathbb{N}$ eventually stabilizes: there exists $N$
such that $g(k) = g(N)$ for all $k \ge N$. -/
lemma nat_antitone_stabilizes {g : ℕ → ℕ} (hg : Antitone g) :
    ∃ N, ∀ k, N ≤ k → g k = g N := by
  by_contra h
  push Not at h
  have hstep : ∀ N, ∃ k, N ≤ k ∧ g k < g N := by
    intro N; obtain ⟨k, hk1, hk2⟩ := h N
    exact ⟨k, hk1, lt_of_le_of_ne (hg hk1) hk2⟩
  suffices ∀ n, ∃ k, g k + n ≤ g 0 from by
    obtain ⟨k, hk⟩ := this (g 0 + 1); omega
  intro n; induction n with
  | zero => exact ⟨0, le_refl _⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih; obtain ⟨k', _, hlt⟩ := hstep k; exact ⟨k', by omega⟩

/-- Finite König-style lemma: an antitone family of nonempty subsets of a finite type has nonempty
intersection. -/
lemma iInter_nonempty_of_antitone {α : Type u} [Fintype α]
    {T : ℕ → Set α} (hanti : Antitone T) (hne : ∀ k, (T k).Nonempty) :
    (⋂ k, T k).Nonempty := by
  classical
  have hcard_anti : Antitone (fun k => Fintype.card ↥(T k)) := fun a b hab =>
    Fintype.card_le_of_injective (Set.inclusion (hanti hab)) (Set.inclusion_injective _)
  obtain ⟨N, hN⟩ := nat_antitone_stabilizes hcard_anti
  have hT_stab : ∀ k, N ≤ k → T k = T N :=
    fun k hk => Set.eq_of_subset_of_card_le (hanti hk) (le_of_eq (hN k hk).symm)
  suffices ⋂ k, T k = T N by rw [this]; exact hne N
  apply le_antisymm (Set.iInter_subset T N)
  intro x hx; rw [Set.mem_iInter]
  exact fun k => if hk : N ≤ k then (hT_stab k hk) ▸ hx else hanti (by omega) hx

/-- Lifting step in the König argument: any element of $S_n$ in every image chain at level $n$ has
a preimage in $S_{n+1}$ that itself lies in every image chain at level $n+1$. -/
lemma surjective_on_eventual_image
    [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    (n : ℕ) (x : S n) (hx : x ∈ ⋂ k, imgCh fn n k) :
    ∃ y ∈ ⋂ k, imgCh fn (n + 1) k, fn n y = x := by
  classical


  let P : ℕ → Set (S (n + 1)) := fun k => fn n ⁻¹' {x} ∩ imgCh fn (n + 1) k
  have hP_ne : ∀ k, (P k).Nonempty := by
    intro k
    have hxk : x ∈ imgCh fn n (k + 1) := Set.mem_iInter.mp hx (k + 1)
    obtain ⟨y, hy_mem, hy_eq⟩ := hxk
    exact ⟨y, Set.mem_inter (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hy_eq)) hy_mem⟩
  have hP_anti : Antitone P := fun _ _ hab =>
    Set.inter_subset_inter_right _ (imgCh_antitone fn (n + 1) hab)

  obtain ⟨y, hy⟩ := iInter_nonempty_of_antitone hP_anti hP_ne
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, P] at hy
  exact ⟨y, Set.mem_iInter.mpr (fun k => (hy k).2), (hy 0).1⟩

/-- Lemma 8.3 (König's lemma): an inverse system $(S_n, f_n)$ of nonempty finite types has nonempty
inverse limit. The compatible sequence is built recursively by choosing preimages that remain in
the stable image chain at each level. -/
theorem nonempty
    (S : ℕ → Type u) (fn : (n : ℕ) → S (n + 1) → S n)
    [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)] :
    Nonempty (InverseLimit S fn) := by
  classical


  have hE_ne : ∀ n, (⋂ k, imgCh fn n k).Nonempty :=
    fun n => iInter_nonempty_of_antitone (imgCh_antitone fn n) (imgCh_nonempty fn n)

  have hsurj : ∀ n (x : S n), x ∈ ⋂ k, imgCh fn n k →
      ∃ y ∈ ⋂ k, imgCh fn (n + 1) k, fn n y = x :=
    fun n x hx => surjective_on_eventual_image fn n x hx


  let build : (n : ℕ) → { x : S n // x ∈ ⋂ k, imgCh fn n k } := fun n =>
    Nat.rec
      ⟨(hE_ne 0).some, (hE_ne 0).some_mem⟩
      (fun n prev =>
        ⟨(hsurj n prev.val prev.property).choose,
         (hsurj n prev.val prev.property).choose_spec.1⟩)
      n

  have hcompat : ∀ n, fn n (build (n + 1)).val = (build n).val :=
    fun n => (hsurj n (build n).val (build n).property).choose_spec.2
  exact ⟨⟨fun n => (build n).val, hcompat⟩⟩

end InverseLimit

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

open Polynomial PadicInt

/-- The finite set of roots of $f \in \mathbb{Z}_p[X]$ in the quotient ring
$\mathbb{Z}/p^n\mathbb{Z}$, i.e. roots of the reduction of $f$ modulo $p^n$. -/
def PolyRootSet (f : Polynomial ℤ_[p]) (n : ℕ) : Type :=
  {r : ZMod (p ^ n) // Polynomial.eval r (Polynomial.map (toZModPow n) f) = 0}

/-- `PolyRootSet f n` is a finite type, being a subtype of the finite ring
$\mathbb{Z}/p^n\mathbb{Z}$. -/
instance polyRootSetFintype (f : Polynomial ℤ_[p]) (n : ℕ) :
    Fintype (PolyRootSet f n) :=
  Subtype.fintype _

/-- Transition map from roots of $f \bmod p^{n+1}$ to roots of $f \bmod p^n$, given by reducing the
representative modulo $p^n$. Makes `(PolyRootSet f, polyRootReduction f)` into an inverse system. -/
def polyRootReduction (f : Polynomial ℤ_[p]) (n : ℕ) :
    PolyRootSet f (n + 1) → PolyRootSet f n := fun ⟨r, hr⟩ =>
  ⟨ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) r, by
    rw [eval_map] at hr ⊢
    rw [show eval₂ (toZModPow n)
          ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r) f =
        eval₂ ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))).comp
          (toZModPow (n + 1)))
          ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r) f
      from by rw [zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)]]
    rw [← hom_eval₂ f (toZModPow (n + 1))
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r, hr, map_zero]⟩

/-- The underlying value of `polyRootReduction f n x` is the cast of `x.val` from
$\mathbb{Z}/p^{n+1}\mathbb{Z}$ to $\mathbb{Z}/p^n\mathbb{Z}$. -/
lemma polyRootReduction_val (f : Polynomial ℤ_[p]) (n : ℕ) (x : PolyRootSet f (n + 1)) :
    (polyRootReduction f n x).val =
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x.val := rfl

/-- Theorem 8.4: a polynomial $f \in \mathbb{Z}_p[X]$ has a root in $\mathbb{Z}_p$ if and only if
it has a root modulo $p^n$ for every $n \in \mathbb{N}$. The forward direction is reduction; the
reverse uses König's lemma on `PolyRootSet f` together with the inverse-limit description of
$\mathbb{Z}_p$. -/
theorem padic_poly_root_iff (f : Polynomial ℤ_[p]) :
    (∃ a : ℤ_[p], Polynomial.eval a f = 0) ↔
    (∀ n : ℕ, ∃ r : ZMod (p ^ n),
      Polynomial.eval r (Polynomial.map (toZModPow n) f) = 0) := by
  constructor
  ·
    rintro ⟨a, ha⟩ n
    exact ⟨toZModPow n a, by rw [eval_map, eval₂_at_apply, ha, map_zero]⟩
  ·
    intro hroots

    haveI hne : ∀ n, Nonempty (PolyRootSet f n) := fun n =>
      let ⟨r, hr⟩ := hroots n; ⟨⟨r, hr⟩⟩

    obtain ⟨s⟩ := InverseLimit.nonempty (PolyRootSet f) (polyRootReduction f)

    let seq : ℕ → ℤ := fun n => (s.val n).val.val

    have hdvd : ∀ i, (p : ℤ) ^ i ∣ seq (i + 1) - seq i := by
      intro i
      haveI : NeZero (p ^ i) := ⟨pow_ne_zero i (Nat.Prime.ne_zero hp.out)⟩
      have hcomp := s.property i

      have hcast : (ZMod.castHom (pow_dvd_pow p (Nat.le_succ i)) (ZMod (p ^ i)))
          (s.val (i + 1)).val = (s.val i).val := by
        rw [← polyRootReduction_val]; exact congr_arg Subtype.val hcomp
      rw [ZMod.castHom_apply] at hcast

      rw [show (p ^ i : ℤ) = ((p ^ i : ℕ) : ℤ) from by push_cast; ring]
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_val]
      exact hcast.symm

    let a : ℤ_[p] := PadicInt.ofIntSeq seq
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub seq p hdvd)

    have hproj : ∀ n, toZModPow n a = (s.val n).val := by
      intro n
      haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero hp.out)⟩
      have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub seq p hdvd n
      simp only [seq] at this
      rw [this, Int.cast_natCast, ZMod.natCast_zmod_val]

    refine ⟨a, ext_of_toZModPow.mp (fun n => ?_)⟩
    have : toZModPow n (Polynomial.eval a f) =
        Polynomial.eval (toZModPow n a) (Polynomial.map (toZModPow n) f) := by
      rw [eval_map, eval₂_at_apply]
    rw [this, hproj n, (s.val n).property, map_zero]

end
