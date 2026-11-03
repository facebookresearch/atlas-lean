/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div

open Polynomial Finset

namespace BerlekampRabin

section Defs

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Two nonzero elements `α`, `β` of a finite field `F` are of *different type* if
their `(q-1)/2`-th powers differ, where `q = |F|`. By Euler's criterion this means
exactly one of `α, β` is a quadratic residue. -/
def DifferentType (α β : F) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ α ^ (Fintype.card F / 2) ≠ β ^ (Fintype.card F / 2)

/-- Decidability of `DifferentType` (since equality in a finite field with decidable
equality is decidable). -/
noncomputable instance differentTypeDecidable (α β : F) :
    Decidable (DifferentType F α β) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set of shifts `δ ∈ F` such that `α + δ` and `β + δ` are of different type
(in the sense of `DifferentType`). Used in Rabin's root-finding algorithm
(Algorithm 3.45 / Theorem 3.44). -/
noncomputable def differentTypeSet (α β : F) : Finset F :=
  Finset.univ.filter fun δ => DifferentType F (α + δ) (β + δ)

end Defs

section Bijection

variable {F : Type*} [Field F]

/-- The map `δ ↦ (α + δ)/(β + δ)`, used to put the different-type set in bijection
with the set of `γ` whose `(q-1)/2`-th power is `-1`. -/
noncomputable def phi (α β δ : F) : F := (α + δ) / (β + δ)

/-- Inverse of `phi`: given `γ`, the unique `δ` with `phi α β δ = γ` (when `α ≠ β`
and `γ ≠ 1`). -/
noncomputable def psi (α β γ : F) : F := (γ * β - α) / (1 - γ)

/-- `phi ∘ psi = id` on the locus where `α ≠ β` and `γ ≠ 1`. -/
lemma phi_psi (α β γ : F) (hαβ : α ≠ β) (hγ : γ ≠ 1) :
    phi α β (psi α β γ) = γ := by
  unfold phi psi
  have h1γ : (1 : F) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  have hden : β + (γ * β - α) / (1 - γ) ≠ 0 := by
    intro h
    apply hβα
    have h1 : (β + (γ * β - α) / (1 - γ)) * (1 - γ) = 0 := by rw [h, zero_mul]
    rw [add_mul, div_mul_cancel₀ _ h1γ] at h1
    linear_combination h1
  rw [div_eq_iff hden]
  field_simp
  ring

/-- `psi ∘ phi = id` on the locus where `α ≠ β` and `β + δ ≠ 0`. -/
lemma psi_phi (α β δ : F) (hαβ : α ≠ β) (hβδ : β + δ ≠ 0) :
    psi α β (phi α β δ) = δ := by
  unfold phi psi
  have hne1 : (α + δ) / (β + δ) ≠ 1 := by
    intro h; exact hαβ (add_right_cancel (div_eq_one_iff_eq hβδ |>.mp h))
  have h1φ : 1 - (α + δ) / (β + δ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  rw [div_eq_iff h1φ]
  field_simp
  ring

/-- `phi α β δ ≠ 1` whenever `α ≠ β` and `β + δ ≠ 0`, since equality would force
`α = β`. -/
lemma phi_ne_one (α β δ : F) (hαβ : α ≠ β) (hβδ : β + δ ≠ 0) :
    phi α β δ ≠ 1 := by
  unfold phi
  intro h; exact hαβ (add_right_cancel (div_eq_one_iff_eq hβδ |>.mp h))

/-- `β + psi α β γ ≠ 0` whenever `α ≠ β` and `γ ≠ 1`; this is the denominator
nonvanishing needed to make `phi` and `psi` mutually inverse. -/
lemma psi_add_ne_zero (α β γ : F) (hαβ : α ≠ β) (hγ : γ ≠ 1) :
    β + psi α β γ ≠ 0 := by
  unfold psi
  intro h
  have h1γ : (1 : F) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have : (β + (γ * β - α) / (1 - γ)) * (1 - γ) = 0 := by rw [h, zero_mul]
  rw [add_mul, div_mul_cancel₀ _ h1γ] at this
  exact (sub_ne_zero.mpr (Ne.symm hαβ)) (by linear_combination this)

end Bijection

section Counting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For any `c ∈ F` and `s ≥ 1`, the number of solutions to `x^s = c` is at most `s`,
since the polynomial `X^s - c` has at most `s` roots. -/
lemma card_pow_eq_const_le (s : ℕ) (hs : 0 < s) (c : F) :
    (Finset.univ.filter (fun x : F => x ^ s = c)).card ≤ s := by
  have hp : (X ^ s - C c : F[X]) ≠ 0 := by
    intro h; have := congr_arg natDegree h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at this; omega
  have hinc : Finset.univ.filter (fun x : F => x ^ s = c) ⊆
      (X ^ s - C c : F[X]).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C,
        sub_eq_zero]
    exact (mem_filter.mp hx).2
  calc (Finset.univ.filter (fun x : F => x ^ s = c)).card
      ≤ (X ^ s - C c : F[X]).roots.toFinset.card := card_le_card hinc
    _ ≤ (X ^ s - C c : F[X]).roots.card := Multiset.toFinset_card_le _
    _ ≤ (X ^ s - C c : F[X]).natDegree := card_roots' _
    _ = s := natDegree_X_pow_sub_C

/-- In a finite field `F` of odd characteristic, exactly `(q-1)/2` elements satisfy
`x^((q-1)/2) = -1` (the quadratic nonresidues), where `q = |F|`. -/
lemma card_pow_eq_neg_one (hF : ringChar F ≠ 2) :
    (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)).card =
    Fintype.card F / 2 := by
  have hq_odd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hq_gt : 1 < Fintype.card F := Fintype.one_lt_card
  have hs_pos : 0 < Fintype.card F / 2 := Nat.div_pos (by omega) (by norm_num)
  have hone_ne : (1 : F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hA_le := card_pow_eq_const_le (F := F) (Fintype.card F / 2) hs_pos 1
  have hB_le := card_pow_eq_const_le (F := F) (Fintype.card F / 2) hs_pos (-1)
  suffices h : (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1)).card +
      (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)).card =
      Fintype.card F - 1 by omega
  have hAB_union : (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1)) ∪
      (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)) =
      Finset.univ.erase 0 := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_erase, ne_eq]
    constructor
    · intro hx
      refine ⟨fun hx0 => ?_, trivial⟩
      subst hx0
      rcases hx with h | h
      · exact zero_ne_one (show (0 : F) = 1 by rwa [zero_pow hs_pos.ne'] at h)
      · exact (neg_ne_zero.mpr (one_ne_zero (α := F)))
          (show (0 : F) = -1 by rwa [zero_pow hs_pos.ne'] at h).symm
    · exact fun ⟨hne, _⟩ => FiniteField.pow_dichotomy hF hne
  have hAB_disj : Disjoint (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = 1))
      (Finset.univ.filter (fun x : F => x ^ (Fintype.card F / 2) = -1)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2; exact hone_ne (h1 ▸ h2)
  rw [← card_union_of_disjoint hAB_disj, hAB_union, card_erase_of_mem (mem_univ 0),
      card_univ]

end Counting

section Rabin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Theorem 3.44 (Rabin 1980): for any pair of distinct elements `α, β ∈ F_q` with
`char F ≠ 2`, the number of shifts `δ` such that `α + δ` and `β + δ` are of different
type equals `(q-1)/2`. Proved by exhibiting a bijection with the set of `γ` such that
`γ^((q-1)/2) = -1`. -/
theorem rabin_card_differentTypeSet (hF : ringChar F ≠ 2) (α β : F) (hαβ : α ≠ β) :
    (differentTypeSet F α β).card = Fintype.card F / 2 := by
  set s := Fintype.card F / 2 with hs_def
  set S := differentTypeSet F α β
  set T := Finset.univ.filter (fun γ : F => γ ^ s = -1)
  have hT_card : T.card = s := card_pow_eq_neg_one hF
  have hone_ne : (1 : F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hs_pos : 0 < s := by
    have := FiniteField.odd_card_of_char_ne_two hF
    have := Fintype.one_lt_card (α := F)
    omega
  rw [← hT_card]
  apply Finset.card_bij (fun δ _ => phi α β δ)
  ·
    intro δ hδ
    simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType] at hδ
    obtain ⟨hαδ, hβδ, hne⟩ := hδ
    simp only [T, mem_filter, mem_univ, true_and]
    unfold phi
    rw [div_pow]


    rcases FiniteField.pow_dichotomy hF hαδ with ha | ha <;>
      rcases FiniteField.pow_dichotomy hF hβδ with hb | hb
    · exact absurd (ha ▸ hb.symm) hne
    · rw [ha, hb]; ring
    · rw [ha, hb]; simp [div_one]

    · exact absurd (ha ▸ hb.symm) hne

  ·
    intro δ₁ hδ₁ δ₂ hδ₂ hφ
    simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType] at hδ₁ hδ₂
    have hβδ₁ : β + δ₁ ≠ 0 := hδ₁.2.1
    have hβδ₂ : β + δ₂ ≠ 0 := hδ₂.2.1
    have h1 := psi_phi α β δ₁ hαβ hβδ₁
    have h2 := psi_phi α β δ₂ hαβ hβδ₂
    rw [← h1, ← h2, hφ]
  ·
    intro γ hγ
    simp only [T, mem_filter, mem_univ, true_and] at hγ
    have hγ_ne_1 : γ ≠ 1 := by
      intro h; rw [h, one_pow] at hγ; exact hone_ne hγ
    have hγ_ne_0 : γ ≠ 0 := by
      intro h; rw [h, zero_pow hs_pos.ne'] at hγ
      exact (neg_ne_zero.mpr (one_ne_zero (α := F))) hγ.symm
    refine ⟨psi α β γ, ?_, ?_⟩
    ·
      simp only [S, differentTypeSet, mem_filter, mem_univ, true_and, DifferentType]
      have hβψ := psi_add_ne_zero α β γ hαβ hγ_ne_1
      constructor
      ·
        intro h

        have : phi α β (psi α β γ) = 0 := by
          unfold phi; rw [h, zero_div]
        rw [phi_psi α β γ hαβ hγ_ne_1] at this
        exact hγ_ne_0 this
      constructor
      · exact hβψ
      ·
        intro heq


        have hphipsi : phi α β (psi α β γ) = γ := phi_psi α β γ hαβ hγ_ne_1
        have hrat : (α + psi α β γ) ^ s / (β + psi α β γ) ^ s = γ ^ s := by
          rw [← div_pow]
          show phi α β (psi α β γ) ^ s = γ ^ s
          rw [hphipsi]

        rw [heq, div_self (pow_ne_zero _ hβψ)] at hrat

        rw [hγ] at hrat
        exact hone_ne hrat

    ·
      exact phi_psi α β γ hαβ hγ_ne_1

end Rabin

section Algorithm

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Step 4b of Algorithm 3.45: compute `gcd(g, (X + δ)^((q-1)/2) - 1)`, a candidate
nontrivial factor of `g`. -/
noncomputable def berlekampRabinStep (g : F[X]) (δ : F) : F[X] :=
  EuclideanDomain.gcd g ((X + C δ) ^ (Fintype.card F / 2) - 1)

/-- Step 2 of Algorithm 3.45: compute `gcd(f, X^q - X)`, the product of `(X - α)` over
all roots `α ∈ F_q` of `f`. -/
noncomputable def berlekampRabinInit (f : F[X]) : F[X] :=
  EuclideanDomain.gcd f (X ^ Fintype.card F - X)

/-- Any root of `berlekampRabinStep F g δ` in `F` is also a root of `g`, because the
step output divides `g`. -/
theorem berlekampRabinStep_root_of_g (g : F[X]) (δ : F) (r : F)
    (hr : (berlekampRabinStep F g δ).IsRoot r) : g.IsRoot r :=
  hr.dvd (EuclideanDomain.gcd_dvd_left g _)

/-- Any root of `berlekampRabinInit F f` in `F` is a root of `f`. -/
theorem berlekampRabinInit_root_of_f (f : F[X]) (r : F)
    (hr : (berlekampRabinInit F f).IsRoot r) : f.IsRoot r :=
  hr.dvd (EuclideanDomain.gcd_dvd_left f _)

/-- Conversely, every root of `f` in `F_q` is a root of `gcd(f, X^q - X)`, since
`X^q - X` vanishes on all of `F_q` by Fermat's little theorem. -/
theorem berlekampRabinInit_root_complete (f : F[X]) (r : F)
    (hr : f.IsRoot r) : (berlekampRabinInit F f).IsRoot r := by
  unfold berlekampRabinInit
  have hrf : (X - C r) ∣ f := dvd_iff_isRoot.mpr hr
  have hrxq : (X - C r) ∣ (X ^ Fintype.card F - X : F[X]) := by
    rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X]
    exact sub_eq_zero.mpr (FiniteField.pow_card r)
  have hrgcd : (X - C r) ∣ EuclideanDomain.gcd f (X ^ Fintype.card F - X) :=
    EuclideanDomain.dvd_gcd hrf hrxq
  rw [IsRoot.def]
  exact dvd_iff_isRoot.mp hrgcd

/-- If `r` is a root of `berlekampRabinStep F g δ`, then `(r + δ)^((q-1)/2) = 1`,
which means `r + δ` is a quadratic residue in `F_q`. -/
theorem berlekampRabinStep_shift_pow (g : F[X]) (δ : F) (r : F)
    (hr : (berlekampRabinStep F g δ).IsRoot r) :
    (r + δ) ^ (Fintype.card F / 2) = 1 := by
  have h2 := hr.dvd (EuclideanDomain.gcd_dvd_right g _)
  rw [IsRoot.def, eval_sub, eval_one, eval_pow, eval_add, eval_X, eval_C,
      sub_eq_zero] at h2
  exact h2

/-- Read off the unique root from a monic linear polynomial `g = X - r`:
`extractRoot g = -coeff 0 / leadingCoeff`. -/
noncomputable def extractRoot (g : F[X]) : F :=
  -g.coeff 0 / g.leadingCoeff

/-- Step 4c of Algorithm 3.45: replace `g` by whichever of `h` or `g/h` has lower
degree, provided `h` is a nontrivial proper factor. -/
noncomputable def chooseFactor (g h : F[X]) : F[X] :=
  if 0 < h.natDegree ∧ h.natDegree < g.natDegree then
    if h.natDegree ≤ g.natDegree - h.natDegree then h
    else g / h
  else g

/-- A single iteration of the inner loop in Algorithm 3.45: run `berlekampRabinStep`
with shift `δ`, then `chooseFactor`. -/
noncomputable def berlekampRabinIteration (g : F[X]) (δ : F) : F[X] :=
  let h := berlekampRabinStep F g δ
  chooseFactor F g h

/-- The inner while-loop of Algorithm 3.45: iterate `berlekampRabinIteration` over a
supplied list of random shifts `δ`, stopping early once `deg g ≤ 1`. -/
noncomputable def berlekampRabinLoop : F[X] → List F → F[X]
  | g, [] => g
  | g, δ :: rest =>
    if g.natDegree ≤ 1 then g
    else berlekampRabinLoop (berlekampRabinIteration F g δ) rest

/-- Algorithm 3.45 (Rabin 1980): given a monic polynomial `f ∈ F_q[X]`, return some
root of `f` in `F_q` if one exists. Returns `0` if `f(0) = 0`; otherwise reduces to
the squarefree part `g = gcd(f, X^q - X)` containing exactly the roots, and iteratively
splits `g` using random shifts. -/
noncomputable def berlekampRabinAlgorithm (f : F[X]) (deltas : List F) : Option F :=

  if f.IsRoot 0 then some 0
  else

    let g := berlekampRabinInit F f

    if g.natDegree = 0 then none
    else

      let g' := berlekampRabinLoop F g deltas

      some (extractRoot F g')

set_option linter.unusedSectionVars false in
/-- For a monic linear polynomial `g`, `extractRoot g` is indeed a root of `g`. -/
theorem extractRoot_isRoot (g : F[X]) (hg : g.natDegree = 1) (hm : g.Monic) :
    g.IsRoot (extractRoot F g) := by
  have hlc : g.leadingCoeff = 1 := hm
  rw [extractRoot, hlc, div_one]
  rw [IsRoot.def]
  have hg_eq : g = X + C (g.coeff 0) := by
    have h1 : g.coeff 1 = 1 := by
      rw [← hlc, Polynomial.leadingCoeff]
      congr 1; omega
    ext n
    match n with
    | 0 => simp
    | 1 => simp [coeff_X, h1]
    | n + 2 =>
      have : g.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this, coeff_X]
  rw [hg_eq]
  simp [eval_add, eval_X, eval_C]

set_option linter.unusedSectionVars false in
/-- If `h ∣ g`, then every root of `chooseFactor F g h` is also a root of `g`,
regardless of which branch (h, g/h, or g) is taken. -/
theorem chooseFactor_root_of_g (g h : F[X]) (r : F) (hd : h ∣ g)
    (hr : (chooseFactor F g h).IsRoot r) : g.IsRoot r := by
  unfold chooseFactor at hr
  split_ifs at hr
  · exact hr.dvd hd
  · exact hr.dvd (EuclideanDomain.div_dvd_of_dvd hd)
  · exact hr

end Algorithm

section YunAlgorithm

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Inner loop of Yun's squarefree factorization (Algorithm 3.46): given `v, w` and a
fuel bound, repeatedly compute `g_i = gcd(v_i, w_i - v_i')` and refresh
`v_{i+1} = v_i / g_i`, `w_{i+1} = (w_i - v_i') / g_i`. -/
noncomputable def yunLoop : F[X] → F[X] → ℕ → List (F[X])
  | v, _w, 0 => [v]
  | v, w, fuel + 1 =>
    let g := EuclideanDomain.gcd v (w - Polynomial.derivative v)
    if v = g then [g]
    else
      let v' := v / g
      let w' := (w - Polynomial.derivative v) / g
      g :: yunLoop v' w' fuel

/-- Algorithm 3.46 (Yun): squarefree factorization of `f ∈ F_q[X]` (in characteristic
not dividing `deg f`). Returns a list `[g_1, …, g_m]` of squarefree pairwise coprime
polynomials with `f = g_1 · g_2^2 · ⋯ · g_m^m`. -/
noncomputable def yunSquarefreeFactor (f : F[X]) : List (F[X]) :=
  let u := EuclideanDomain.gcd f (Polynomial.derivative f)
  let v₁ := f / u
  let w₁ := Polynomial.derivative f / u
  yunLoop F v₁ w₁ f.natDegree

/-- Reconstruct `f` from its squarefree factorization `[g_1, …, g_m]` as the product
`∏_i g_i^i` (with 1-based indexing). -/
noncomputable def sqfreeProduct (factors : List (F[X])) : F[X] :=
  (factors.zipIdx 1 |>.map (fun ⟨g, i⟩ => g ^ i)).prod

/-- The correctness predicate for a squarefree factorization (output of
Algorithm 3.46): the list is nonempty, recovers `f` as `∏ g_i^i`, each `g_i` is
squarefree, the factors are pairwise coprime, and the last factor is not `1`. -/
structure IsSquarefreeFactorization (f : F[X]) (factors : List (F[X])) : Prop where
  nonempty : factors ≠ []
  prod_eq : f = sqfreeProduct F factors
  sqfree : ∀ g ∈ factors, Squarefree g
  coprime : factors.Pairwise (fun g h => IsCoprime g h)
  last_ne_one : factors.getLast nonempty ≠ 1

end YunAlgorithm

section YunCorrectness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- If `g^2 ∣ f`, then `g` divides `gcd(f, f')`. This is the easy direction used in
proving correctness of Yun's algorithm. -/
theorem sq_dvd_imp_dvd_gcd_derivative (g f : F[X]) (h : g ^ 2 ∣ f) :
    g ∣ EuclideanDomain.gcd f (Polynomial.derivative f) := by
  apply EuclideanDomain.dvd_gcd
  · exact dvd_trans (dvd_pow_self g (by norm_num : (2 : ℕ) ≠ 0)) h
  · have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
    simpa using this

/-- Characterization underlying Yun's algorithm: for an irreducible `g` (over a
perfect field), `g^2 ∣ f` iff `g ∣ gcd(f, f')`. The nontrivial direction uses
separability of irreducible polynomials over perfect fields. -/
theorem irreducible_sq_dvd_iff_dvd_gcd_derivative (g f : F[X])
    (hg : Irreducible g) :
    g ^ 2 ∣ f ↔ g ∣ EuclideanDomain.gcd f (Polynomial.derivative f) := by
  constructor
  · exact sq_dvd_imp_dvd_gcd_derivative g f
  · intro h
    have hgf : g ∣ f := dvd_trans h (EuclideanDomain.gcd_dvd_left f _)
    have hgf' : g ∣ Polynomial.derivative f :=
      dvd_trans h (EuclideanDomain.gcd_dvd_right f _)
    obtain ⟨q, hfq⟩ := hgf
    rw [hfq, derivative_mul] at hgf'
    have hgdq : g ∣ Polynomial.derivative g * q := by
      have h1 : g ∣ g * Polynomial.derivative q := dvd_mul_right g _
      rw [add_comm] at hgf'
      exact (dvd_add_right h1).mp hgf'
    have hgsep : g.Separable := PerfectField.separable_of_irreducible hg
    have hgq : g ∣ q := hgsep.dvd_of_dvd_mul_left hgdq
    rw [hfq, sq]
    exact mul_dvd_mul_left g hgq

set_option linter.unusedSectionVars false in
/-- Over a finite field (which is perfect), a polynomial is separable iff it is
squarefree. -/
theorem finite_field_separable_iff_squarefree (f : F[X]) :
    f.Separable ↔ Squarefree f :=
  PerfectField.separable_iff_squarefree

set_option linter.unusedSectionVars false in
/-- The initial gcd `gcd(f, f')` computed in Yun's algorithm divides `f`. -/
theorem yunInit_dvd (f : F[X]) :
    EuclideanDomain.gcd f (Polynomial.derivative f) ∣ f :=
  EuclideanDomain.gcd_dvd_left f _

end YunCorrectness

section CantorZassenhaus

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- One probabilistic splitting step in equal-degree (Cantor-Zassenhaus) factorization
(Step 3 of Algorithm 3.47): try `h₁ = gcd(g, u)`; if it is a proper factor, return it;
otherwise try `h₂ = gcd(g, u^((q^j - 1)/2) - 1)`; otherwise return `g`. -/
noncomputable def equalDegreeSplitStep (g u : F[X]) (j : ℕ) : F[X] :=
  let h₁ := EuclideanDomain.gcd g u
  if 0 < h₁.natDegree ∧ h₁.natDegree < g.natDegree then h₁
  else
    let s := (Fintype.card F ^ j - 1) / 2
    let h₂ := EuclideanDomain.gcd g (u ^ s - 1)
    if 0 < h₂.natDegree ∧ h₂.natDegree < g.natDegree then h₂
    else g

/-- `equalDegreeSplitStep F g u j` always divides `g`, in each of the three branches. -/
theorem equalDegreeSplitStep_dvd (g u : F[X]) (j : ℕ) :
    equalDegreeSplitStep F g u j ∣ g := by
  unfold equalDegreeSplitStep
  simp only
  split_ifs <;> [exact EuclideanDomain.gcd_dvd_left g u;
    exact EuclideanDomain.gcd_dvd_left g _; exact dvd_refl g]

/-- Any root in `F` of `equalDegreeSplitStep F g u j` is a root of `g`, since the
output divides `g`. -/
theorem equalDegreeSplitStep_root_of_g (g u : F[X]) (j : ℕ) (r : F)
    (hr : (equalDegreeSplitStep F g u j).IsRoot r) : g.IsRoot r :=
  hr.dvd (equalDegreeSplitStep_dvd F g u j)

/-- The recursive splitting loop in equal-degree factorization (Step 3 of
Algorithm 3.47): given `g` of degree `> j`, repeatedly split using
`equalDegreeSplitStep` and recurse on both pieces, until each factor has degree `j`. -/
noncomputable def equalDegreeFactorLoop (j : ℕ) : F[X] → List (F[X]) → List (F[X])
  | g, [] => [g]
  | g, u :: rest =>
    if g.natDegree ≤ j then [g]
    else
      let h := equalDegreeSplitStep F g u j
      if 0 < h.natDegree ∧ h.natDegree < g.natDegree then
        equalDegreeFactorLoop j h rest ++ equalDegreeFactorLoop j (g / h) rest
      else
        equalDegreeFactorLoop j g rest

/-- Distinct-degree factorization step (Step 2 of Algorithm 3.47): compute
`g_j = gcd(g, X^(q^j) - X)`, the product of irreducible factors of `g` of degree `j`,
and return the pair `(g_j, g / g_j)`. -/
noncomputable def distinctDegreeStep (g : F[X]) (j : ℕ) : F[X] × F[X] :=
  let gj := EuclideanDomain.gcd g (X ^ (Fintype.card F ^ j) - X)
  (gj, g / gj)

/-- Cantor-Zassenhaus factorization of a squarefree polynomial `g` (Steps 2–3 of
Algorithm 3.47): iterate `distinctDegreeStep` for `j = 1, 2, …`, then split each
`g_j` further using `equalDegreeFactorLoop` if needed. -/
noncomputable def factorSquarefree (g : F[X]) (randomPolys : List (F[X])) : List (F[X]) :=
  let rec loop (remaining : F[X]) (j : ℕ) (fuel : ℕ) (acc : List (F[X])) : List (F[X]) :=
    if fuel = 0 ∨ remaining.natDegree = 0 then acc
    else
      let (gj, remaining') := distinctDegreeStep F remaining j
      let factors :=
        if gj.natDegree = 0 then []
        else if gj.natDegree = j then [gj]
        else equalDegreeFactorLoop F j gj randomPolys
      loop remaining' (j + 1) (fuel - 1) (acc ++ factors)
  loop g 1 g.natDegree []

/-- Algorithm 3.47 (Cantor-Zassenhaus): compute the complete irreducible factorization
of a monic `f ∈ F_q[X]` as a list of pairs `(p, i)`, where `p` is an irreducible
factor with multiplicity `i`. Uses Yun for the squarefree factorization and
`factorSquarefree` for each squarefree piece. -/
noncomputable def cantorZassenhausAlgorithm (f : F[X])
    (randomPolys : List (F[X])) : List (F[X] × ℕ) :=

  let sqfreeFactors := yunSquarefreeFactor F f


  (sqfreeFactors.zipIdx 1).flatMap fun ⟨gᵢ, i⟩ =>
    let irreds := factorSquarefree F gᵢ randomPolys
    irreds.map fun p => (p, i)

/-- Correctness predicate for the output of `cantorZassenhausAlgorithm`: the indexed
family `factors : Fin n → F[X]` consists of irreducibles, `f = ∏ (factors i)^(mult i)`,
multiplicities are positive, and distinct indices give non-associated factors. -/
structure IsIrreducibleFactorization (f : F[X]) (n : ℕ)
    (factors : Fin n → F[X]) (multiplicities : Fin n → ℕ) : Prop where
  irred : ∀ i : Fin n, Irreducible (factors i)
  prod_eq : f = ∏ i : Fin n, (factors i) ^ (multiplicities i)
  mult_pos : ∀ i : Fin n, 0 < multiplicities i
  pairwise : ∀ i j : Fin n, i ≠ j → ¬ Associated (factors i) (factors j)

/-- The first component of `distinctDegreeStep F g j`, namely `gcd(g, X^(q^j) - X)`,
divides `g`. -/
theorem distinctDegreeStep_fst_dvd (g : F[X]) (j : ℕ) :
    (distinctDegreeStep F g j).1 ∣ g :=
  EuclideanDomain.gcd_dvd_left g _

end CantorZassenhaus

end BerlekampRabin
