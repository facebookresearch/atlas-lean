/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Ring.GeomSum
import Atlas.EllipticCurves.code.Divisors
import Atlas.EllipticCurves.code.TorsionEndomorphism

noncomputable section

open WeierstrassCurve.Affine

namespace WeilPairing

/-- Evaluation of a function `f : P → k` at a divisor `D = ∑ nₚ [P]`, producing the product
`∏ f(p) ^ nₚ` (Definition 23.18 in Sutherland's notes). -/
def functionEvalAtDivisor {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (f : P → k) (D : P →₀ ℤ) : k :=
  D.prod (fun p n => f p ^ n)

/-- Evaluation at a divisor is multiplicative in the divisor:
`f(D₁ + D₂) = f(D₁) · f(D₂)`. -/
theorem functionEvalAtDivisor_mul
    {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (f : P → k) (D₁ D₂ : P →₀ ℤ) :
    functionEvalAtDivisor f (D₁ + D₂) =
      functionEvalAtDivisor f D₁ * functionEvalAtDivisor f D₂ := by
  unfold functionEvalAtDivisor
  exact Finsupp.prod_add_index (fun a _ => zpow_zero (f a))
    (fun a _ b₁ b₂ => zpow_add (f a) b₁ b₂)


/-- The numerator `L_{P,Q}` of the line function from Definition 23.16, evaluated at a third point
`R`. Returns the value of the line through `P` and `Q` (or the tangent at `P` if `P = Q`). -/
noncomputable def lineFunction
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (P Q : W.Point) (R : W.Point) : F :=
  match P, Q, R with

  | .zero, _, _ => 1
  | _, .zero, _ => 1
  | _, _, .zero => 1

  | .some x₁ y₁ _, .some x₂ y₂ _, .some xR yR _ =>
    if x₁ = x₂ then
      if y₁ = y₂ then


        let denom := 2 * y₁ + W.a₁ * x₁ + W.a₃
        if denom = 0 then
          xR - x₁
        else
          let slope := (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / denom
          (yR - y₁) - slope * (xR - x₁)
      else

        xR - x₁
    else

      (yR - y₁) * (x₂ - x₁) - (xR - x₁) * (y₂ - y₁)

/-- The function `G_{P,Q} := L_{P,Q} / L_{P+Q, -(P+Q)}` from Definition 23.16, packaged as a
function into `Fˣ` and forced to `1` when the denominator/value vanishes. -/
noncomputable def lineFunctionG
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → W.Point → (W.Point → Fˣ) :=
  fun P Q R =>
    let num := lineFunction W P Q R
    let den := lineFunction W (P + Q) (-(P + Q)) R


    if hd : den = 0 then 1
    else
      let val := num / den
      if hv : val = 0 then 1
      else Units.mk0 val hv

variable {F₀ : Type*} [Field F₀] [DecidableEq F₀]

/-- The divisor of the line `L_{P,Q}`, namely `[P] + [Q] + [-(P+Q)] - 3[0]`. -/
def divLine {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 + Finsupp.single (-(P + Q)) 1
    - 3 • Finsupp.single (0 : W.Point) 1

/-- The divisor of `G_{P,Q}`, namely `[P] + [Q] - [P+Q] - [0]`. -/
def divG {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 - Finsupp.single (P + Q) 1
    - Finsupp.single (0 : W.Point) 1




/-- Two divisors `D₁, D₂` are linearly equivalent (with respect to a subgroup of principal
divisors `PrincE`) when `D₁ - D₂ ∈ PrincE`. -/
def LinearlyEquivalent {W : WeierstrassCurve.Affine F₀}
    (PrincE : AddSubgroup (W.Point →₀ ℤ))
    (D₁ D₂ : W.Point →₀ ℤ) : Prop :=
  D₁ - D₂ ∈ PrincE

section MillerFunction

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The Miller function `f_{n,P}` for natural `n`, defined recursively (Definition 23.23):
`f_{0,P} = f_{1,P} = 1` and `f_{n+2,P} = f_{n+1,P} · G_{P, (n+1)P}`. -/
def millerFunctionNat (P : W.Point) : ℕ → (W.Point → Fˣ)
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | (n + 2) => fun R =>
    millerFunctionNat P (n + 1) R * lineFunctionG W P ((↑(n + 1) : ℤ) • P) R

/-- The Miller function `f_{n,P}` extended to all integers (Definition 23.23):
for `n < 0`, `f_{-n,P} := (f_{n,P} · G_{nP, -nP})⁻¹`. -/
def millerFunction (P : W.Point) (n : ℤ) : W.Point → Fˣ :=
  match n with
  | (m : ℕ) => millerFunctionNat W P m
  | Int.negSucc m =>
    fun R => (millerFunctionNat W P (m + 1) R *
              lineFunctionG W ((↑(m + 1) : ℤ) • P) (-(↑(m + 1) : ℤ) • P) R)⁻¹

/-- The Miller function at index `0` is the constant function `1`. -/
@[simp]
theorem millerFunction_zero (P : W.Point) :
    millerFunction W P 0 = fun _ => 1 :=
  rfl

/-- The Miller function at index `1` is the constant function `1`. -/
@[simp]
theorem millerFunction_one (P : W.Point) :
    millerFunction W P 1 = fun _ => 1 :=
  rfl

/-- Recursive step for the natural-index Miller function:
`f_{n+1,P}(R) = f_{n,P}(R) · G_{P, nP}(R)` for `n ≥ 1`. -/
theorem millerFunctionNat_succ (P : W.Point) (n : ℕ) (hn : 1 ≤ n) (R : W.Point) :
    millerFunctionNat W P (n + 1) R =
      millerFunctionNat W P n R * lineFunctionG W P ((↑n : ℤ) • P) R := by
  cases n with
  | zero => omega
  | succ m => simp only [millerFunctionNat]

/-- Relation between the Miller function at `-n` and at `n`, for positive natural `n`. -/
theorem millerFunction_neg (P : W.Point) (n : ℕ) (hn : 0 < n) (R : W.Point) :
    millerFunction W P (-(↑n : ℤ)) R =
      (millerFunction W P (↑n : ℤ) R *
       lineFunctionG W ((↑n : ℤ) • P) (-(↑n : ℤ) • P) R)⁻¹ := by
  cases n with
  | zero => omega
  | succ m =>
    have hkey : -(↑(m + 1) : ℤ) = Int.negSucc m := by omega
    simp only [millerFunction, hkey]

end MillerFunction

section MillerProperties

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The divisor of `f_{n,P}`, namely `n[P] - (n-1)[0] - [nP]` (Lemma 23.24(i)). -/
def millerFunctionDivisor
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → ℤ → (W.Point →₀ ℤ) :=
  fun P n =>
    n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1
      - Finsupp.single ((n : ℤ) • P) 1

/-- Expands the definition of `millerFunctionDivisor` as
`n[P] - (n-1)[0] - [nP]` (Lemma 23.24(i)). -/
theorem millerFunction_divisor (P : W.Point) (n : ℤ) :
    millerFunctionDivisor W P n =
      n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1
        - Finsupp.single ((n : ℤ) • P) 1 := rfl




end MillerProperties

section MillerDerived

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The divisor `n[P] - (n-1)[0] - [nP]` has degree zero. -/
theorem millerFunction_divisor_deg_zero (P : W.Point) (n : ℤ) :
    (millerFunctionDivisor W P n).sum (fun _ k => k) = 0 := by
  rw [millerFunction_divisor]
  simp [Finsupp.sum_sub_index, Finsupp.sum_single_index]




end MillerDerived

/-- The group `μ_N(F)` of `N`-th roots of unity inside `Fˣ`. -/
def muN (N : ℕ) (F : Type*) [CommMonoid F] : Subgroup Fˣ :=
  rootsOfUnity N F

variable {F : Type*} [Field F] [DecidableEq F]

/-- The raw Weil pairing value (Lemma 23.26):
`e_n(P, Q) = f_{n,Q}(T) · f_{n,P}(Q - T) / (f_{n,P}(-T) · f_{n,Q}(P + T))`
for an auxiliary point `T`. -/
def weilPairingVal
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (N : ℕ) (P Q : W.Point) (T : W.Point) : Fˣ :=
  millerFunction W Q (N : ℤ) T *
    millerFunction W P (N : ℤ) (Q - T) *
  (millerFunction W P (N : ℤ) (-T) *
    millerFunction W Q (N : ℤ) (P + T))⁻¹









section Definition_23_19

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]

/-- Divisor-level Weil pairing (Definition 23.19): given functions `f₁, f₂` representing the
`n`-torsion of the divisors `D₁, D₂` (i.e., `div fᵢ = n · Dᵢ`), define
`e_n(D₁, D₂) := f₁(D₂) / f₂(D₁)`. -/
def weilPairingDiv (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) : k :=
  functionEvalAtDivisor f₁ D₂ * (functionEvalAtDivisor f₂ D₁)⁻¹

end Definition_23_19

section Lemma_23_21

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]



/-- Scaling a divisor by an integer `n` exponentiates the evaluation:
`f(n • D) = f(D)^n`. -/
theorem functionEvalAtDivisor_zsmul
    (f : P → k) (n : ℤ) (D : P →₀ ℤ) :
    functionEvalAtDivisor f (n • D) = functionEvalAtDivisor f D ^ n := by

  change (n • D).support.prod (fun a => f a ^ ((n • D) a)) =
    (D.support.prod (fun a => f a ^ (D a))) ^ n
  rw [Finset.prod_subset (s₁ := (n • D).support) Finsupp.support_smul
    (fun x _ hx => by
      rw [Finsupp.notMem_support_iff.mp hx, zpow_zero]),
    ← Finset.prod_zpow]
  exact Finset.prod_congr rfl (fun p _ => by
    rw [Finsupp.smul_apply, smul_eq_mul, zpow_mul'])


/-- The divisor-level Weil pairing is alternating: `e_n(D₁, D₂) · e_n(D₂, D₁) = 1`. -/
theorem weilPairingDiv_alternating
    (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) :
    weilPairingDiv f₁ f₂ D₁ D₂ * weilPairingDiv f₂ f₁ D₂ D₁ = 1 := by
  unfold weilPairingDiv
  group

/-- Inverse form of the alternating property:
`e_n(D₁, D₂) = e_n(D₂, D₁)⁻¹`. -/
theorem weilPairingDiv_alternating_inv
    (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) :
    weilPairingDiv f₁ f₂ D₁ D₂ = (weilPairingDiv f₂ f₁ D₂ D₁)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (weilPairingDiv_alternating f₁ f₂ D₁ D₂)

end Lemma_23_21









/-- A Galois automorphism `σ : F ≃+* F` induces a multiplicative automorphism of
`μ_N(F) ⊆ Fˣ`. -/
noncomputable def galoisActionOnMuN
    {F : Type*} [Field F] [DecidableEq F]
    (N : ℕ) (_hN : 0 < N) (_hchar : ¬ (ringChar F ∣ N))
    (σ : F ≃+* F) :
    ↥(muN N F) →* ↥(muN N F) where
  toFun := fun ⟨x, hx⟩ =>
    ⟨Units.map σ.toRingHom.toMonoidHom x, by
      simp only [muN, rootsOfUnity, Subgroup.mem_mk, Submonoid.mem_mk] at hx ⊢
      show (Units.map σ.toRingHom.toMonoidHom x) ^ N = 1
      rw [← map_pow, hx, map_one]⟩
  map_one' := by ext; simp [map_one]
  map_mul' := by intro a b; ext; simp [map_mul]







section EmbeddingDegree

variable {K : Type*} [Field K]



end EmbeddingDegree

section PairingFriendly

variable {K : Type*} [Field K]


end PairingFriendly

section TatePairing

/-- For any element `u` of a finite commutative group `G` and any divisor `n` of `|G|`,
the power `(u ^ (|G| / n))^n = 1`. -/
lemma pow_div_mem_rootsOfUnity
    {G : Type*} [CommGroup G] [Fintype G] (u : G) (n : ℕ) (hn : n ∣ Fintype.card G) :
    (u ^ (Fintype.card G / n)) ^ n = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hn, pow_card_eq_one]


end TatePairing

section Lemma2333

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]













end Lemma2333

section Corollary_23_25

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The Miller "double-and-add" algorithm: efficient evaluation of `f_{n,P}(Q)` using
`O(log n)` field operations (Corollary 23.25). At each step we either square the accumulator
(via the line `G_{mP, mP}`) or square and multiply by `G_{2mP, P}`. -/
def millerDoubleAndAdd (P : W.Point) (Q : W.Point) : ℕ → Fˣ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let m := (n + 2) / 2
    let acc := millerDoubleAndAdd P Q m

    let doubled := acc * acc * lineFunctionG W ((m : ℤ) • P) ((m : ℤ) • P) Q
    if (n + 2) % 2 = 0 then
      doubled
    else

      doubled * lineFunctionG W ((2 * m : ℤ) • P) ((1 : ℤ) • P) Q
  termination_by n => n


/-- Operation cost of the Miller double-and-add algorithm: roughly `log₂ n` doublings plus a few
extra operations per "add" step. -/
def millerEvalCost : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let m := (n + 2) / 2
    let sub_cost := millerEvalCost m
    if (n + 2) % 2 = 0 then
      sub_cost + 1
    else
      sub_cost + 2
  termination_by n => n

/-- Logarithmic bound on the Miller evaluation cost:
`millerEvalCost n ≤ 2 log₂ n + 2`, giving the `O(log n)` complexity of Corollary 23.25. -/
theorem millerEvalCost_le_log (n : ℕ) :
    millerEvalCost n ≤ 2 * Nat.log 2 n + 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [millerEvalCost]
    | 1 => simp [millerEvalCost]
    | n + 2 =>
      simp only [millerEvalCost]
      have hm : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have h_ih := ih ((n + 2) / 2) hm
      have h_log : Nat.log 2 (n + 2) = Nat.log 2 ((n + 2) / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by omega) (by omega)
      split_ifs with h
      ·
        omega
      ·
        omega

end Corollary_23_25

section Corollary_23_30




end Corollary_23_30

section Corollary_23_31

variable {F : Type*} [Field F] [DecidableEq F]






/-- The predicate "the subgroup generated by `P` and `Q` is cyclic": there exists a single
generator `R` whose multiples coincide with `⟨P, Q⟩`. -/
def IsSubgroupCyclicPair
    {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F}
    (P Q : W.Point) : Prop :=
  ∃ R : W.Point,
    AddSubgroup.closure ({P, Q} : Set W.Point) = AddSubgroup.zmultiples R




end Corollary_23_31

end WeilPairing
