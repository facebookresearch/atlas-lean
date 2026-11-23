/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Atlas.ArithmeticGeometry.code.EllipticCurves
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Atlas.ArithmeticGeometry.code.PadicElliptic
import Atlas.ArithmeticGeometry.code.WeierstrassValBound

open WeierstrassCurve






namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]




end EllipticCurveIsogeny


namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]















end EllipticCurveIsogeny

namespace EllipticCurveIsogeny





variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]





end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]


namespace FunctionFieldExtension



end FunctionFieldExtension




end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

universe u







end EllipticCurveIsogeny

section PointFinite

variable {R : Type*} [CommRing R] [Fintype R] (W : WeierstrassCurve R)

/-- Encode an affine Weierstrass point as `Option (R × R)`: the point at infinity is
`none`, and an affine point $(x, y)$ is `some (x, y)`. -/
noncomputable def WeierstrassCurve.Affine.Point.toOption
    (P : W.toAffine.Point) : Option (R × R) :=
  match P with
  | .zero => Option.none
  | .some x y _ => Option.some (x, y)

omit [Fintype R] in
/-- The encoding `toOption` is injective: distinct affine points have distinct
encodings. -/
lemma WeierstrassCurve.Affine.Point.toOption_injective :
    Function.Injective (WeierstrassCurve.Affine.Point.toOption W) := by
  intro a b hab
  simp only [WeierstrassCurve.Affine.Point.toOption] at hab
  cases a <;> cases b <;> simp_all

/-- If the base ring is finite, then the set of points of an affine Weierstrass curve
is also finite. -/
noncomputable instance WeierstrassCurve.Affine.Point.finite :
    Finite W.toAffine.Point :=
  Finite.of_injective _ (WeierstrassCurve.Affine.Point.toOption_injective W)

end PointFinite

/-- In a torsion-free abelian group, an element of finite additive order must be zero. -/
lemma eq_zero_of_isOfFinAddOrder_of_torsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    (g : G) (h : IsOfFinAddOrder g) : g = 0 := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h
  obtain ⟨n, hn, hng⟩ := h
  exact (IsAddTorsionFree.nsmul_right_injective hn.ne') (hng.trans (smul_zero n).symm)


/-- An elliptic curve over $\mathbb{Q}$ has good reduction at a prime $p$ if it
admits a model that reduces mod $p$ to an elliptic curve over $\mathbb{F}_p$. -/
structure HasGoodReduction (W : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] where
  reducedCurve : WeierstrassCurve (ZMod p)
  isElliptic : reducedCurve.IsElliptic










/-- A nonsingular point $(x_0, y_0)$ on a short Weierstrass curve $y^2 = x^3 + a_4 x + a_6$
satisfies the curve equation. -/
lemma curve_equation_short_weierstrass
    (W : WeierstrassCurve ℚ)
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀) :
    y₀ ^ 2 = x₀ ^ 3 + W.a₄ * x₀ + W.a₆ := by
  have heq := hns.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [WeierstrassCurve.toAffine] at heq
  simp only [hW1, hW2, hW3, zero_mul] at heq
  linarith

/-- A rational number with nonnegative $p$-adic valuation at every prime is an integer. -/
lemma rat_is_int_of_nonneg_padic_val (q : ℚ)
    (h : ∀ p : ℕ, Nat.Prime p → padicValRat p q ≥ 0) :
    ∃ z : ℤ, (z : ℚ) = q := by
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  by_contra hne
  have hd_pos := q.den_pos
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : q.den ≠ 1)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hge := h p hp
  simp only [padicValRat] at hge
  have hpd : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd (by omega) hpdiv
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hpn : ¬ (p ∣ q.num.natAbs) := by
    intro hpa
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpa hpdiv
    rw [hcop] at h1
    have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h1
    exact absurd this (Nat.not_le.mpr hp.one_lt)
  have hpn0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hpn
  simp only [padicValInt, hpn0] at hge
  omega

/-- If a rational $q$ has $q^2 \in \mathbb{Z}$, then $q \in \mathbb{Z}$. -/
lemma rat_sq_int_imp_int (q : ℚ) (h : ∃ z : ℤ, (z : ℚ) = q ^ 2) :
    ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨z, hz⟩ := h
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  have hq2_den : (q * q).den = 1 := by
    have : q * q = q ^ 2 := by ring
    rw [this, ← hz]; exact Rat.den_intCast z
  have hmul := Rat.mul_den q q
  rw [hq2_den] at hmul
  rw [show q.num * q.num = (q.num : ℤ) ^ 2 from by ring] at hmul
  rw [show q.den * q.den = q.den ^ 2 from by ring] at hmul
  rw [Int.natAbs_pow] at hmul
  rw [q.reduced.pow 2 2] at hmul
  simp at hmul
  nlinarith [sq_nonneg q.den]





section MultiplicationByN

variable {G : Type*} [AddCommGroup G]


end MultiplicationByN





section Theorem248

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]



end Theorem248

section Corollary2410

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]


end Corollary2410

/-- The base change of an elliptic curve $E/\mathbb{Q}$ to $\mathbb{Q}_p$ remains
elliptic (its discriminant remains a unit). -/
noncomputable instance baseChange_padic_isElliptic
    {p : ℕ} [Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (W.baseChange ℚ_[p]).IsElliptic := by
  constructor
  rw [show (W.baseChange ℚ_[p]).Δ = algebraMap ℚ ℚ_[p] W.Δ by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.Δ]]
  exact (algebraMap ℚ ℚ_[p]).isUnit_map ‹W.IsElliptic›.isUnit

/-- Membership in the $n$-th piece of the $p$-adic filtration on $E(\mathbb{Q}_p)$:
the point $O$ is always in, and an affine point $(x, y)$ lies in $E_n$ when $n = 0$
or when $y \neq 0$ and $v_p(x) - v_p(y) \geq n$. -/
def PadicFiltrationMem (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => n = 0 ∨ (y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y)


/-- The identity point lies in every piece $E_n$ of the $p$-adic filtration. -/
theorem PadicFiltrationMem.zero (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    PadicFiltrationMem W p n (.zero) :=
  trivial

/-- The filtration is monotone: if $P \in E_n$ and $m \leq n$, then $P \in E_m$. -/
theorem PadicFiltrationMem.of_le {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)] {n m : ℕ}
    {P : (W.baseChange ℚ_[p]).toAffine.Point}
    (h : PadicFiltrationMem W p n P) (hmn : m ≤ n) :
    PadicFiltrationMem W p m P := by
  match P with
  | .zero => trivial
  | .some x y hxy =>
    simp only [PadicFiltrationMem] at h ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl rfl
    · right
      rcases h with rfl | ⟨hy, hv⟩
      · omega
      · exact ⟨hy, le_trans (by exact_mod_cast hmn) hv⟩

noncomputable section

open Classical

/-- The $p$-adic filtration on $E(\mathbb{Q}_p)$: a decreasing family of
subgroups $E = E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$ defined via
the $p$-adic valuation, together with the (mild) assumptions
$a_1 = a_2 = a_3 = 0$ required for the addition-formula computations. -/
structure PadicFiltration (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] where
  group : ℕ → AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point
  antitone : Antitone group
  mem_iff : ∀ n P, P ∈ group n ↔ PadicFiltrationMem W p n P
  zero_eq_top : group 0 = ⊤
  ha₁ : W.a₁ = 0
  ha₂ : W.a₂ = 0
  ha₃ : W.a₃ = 0

/-- The $p$-adic valuation is invariant under negation: $v_p(-x) = v_p(x)$. -/
lemma padic_valuation_neg {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) (hx : x ≠ 0) :
    Padic.valuation (-x) = Padic.valuation x := by
  have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
  have h1 := Padic.norm_eq_zpow_neg_valuation hx
  have h2 := Padic.norm_eq_zpow_neg_valuation hx'
  rw [norm_neg] at h2
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact neg_injective ((zpow_right_strictMono₀ hp).injective (h2.symm.trans h1))


/-- Strict (non-Archimedean) triangle inequality: if $v_p(x) \neq v_p(y)$,
then $v_p(x+y) = \min(v_p(x), v_p(y))$. -/
lemma padic_valuation_add_eq_min {p : ℕ} [Fact (Nat.Prime p)] {x y : ℚ_[p]}
    (hxy : x + y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : Padic.valuation x ≠ Padic.valuation y) :
    Padic.valuation (x + y) = min (Padic.valuation x) (Padic.valuation y) := by
  have h1 := Padic.le_valuation_add hxy
  have h2 : min (Padic.valuation (x + y)) (Padic.valuation y) ≤ Padic.valuation x := by
    have h := Padic.le_valuation_add (show (x + y) + (-y) ≠ 0 by rwa [add_neg_cancel_right])
    rwa [padic_valuation_neg y hy, add_neg_cancel_right] at h
  have h3 : min (Padic.valuation (x + y)) (Padic.valuation x) ≤ Padic.valuation y := by
    have h := Padic.le_valuation_add (show (x + y) + (-x) ≠ 0 by
      rwa [show (x + y) + (-x) = y from by ring])
    rwa [padic_valuation_neg x hx, show (x + y) + (-x) = y from by ring] at h
  omega


/-- Subtractive form of the strict triangle inequality: if $v_p(x) \neq v_p(y)$,
then $v_p(x - y) = \min(v_p(x), v_p(y))$. -/
lemma padic_valuation_sub_eq_min {p : ℕ} [Fact (Nat.Prime p)] {x y : ℚ_[p]}
    (hxy : x - y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : Padic.valuation x ≠ Padic.valuation y) :
    Padic.valuation (x - y) = min (Padic.valuation x) (Padic.valuation y) := by
  rw [sub_eq_add_neg] at hxy ⊢
  rw [padic_valuation_add_eq_min hxy hx (neg_ne_zero.mpr hy)
      (by rwa [padic_valuation_neg y hy]),
    padic_valuation_neg y hy]



/-- The $n$-th level $E_n$ of the $p$-adic filtration is closed under negation:
if $P \in E_n$ then $-P \in E_n$. -/
theorem PadicFiltrationMem.neg_mem {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    {P : (W.baseChange ℚ_[p]).toAffine.Point}
    (hP : PadicFiltrationMem W p n P) :
    PadicFiltrationMem W p n (-P) := by
  match P with
  | .zero => trivial
  | .some x y hxy =>
    show n = 0 ∨ ((W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
      (n : ℤ) ≤ Padic.valuation x - Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y))
    have ha₁' : (W.baseChange ℚ_[p]).toAffine.a₁ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₁]
    have ha₃' : (W.baseChange ℚ_[p]).toAffine.a₃ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₃]
    have hneq : (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
      simp only [WeierstrassCurve.Affine.negY, ha₁', ha₃', zero_mul, sub_zero]
    rw [hneq]
    simp only [PadicFiltrationMem] at hP
    rcases hP with rfl | ⟨hy, hv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg y hy]; exact hv⟩



namespace PadicFiltration

variable {W : WeierstrassCurve ℚ} [W.IsElliptic]
variable {p : ℕ} [Fact (Nat.Prime p)]
variable (F : PadicFiltration W p)


/-- If reduction modulo $p$ is surjective on $E(\mathbb{Q}_p)$, then it remains
surjective when restricted to $E_0 = E(\mathbb{Q}_p)$. -/
lemma hensel_reduction_surjective
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red) :
    Function.Surjective (red.comp (F.group 0).subtype) := by
  intro q
  obtain ⟨x, hx⟩ := hred_surj q
  have hx_mem : x ∈ F.group 0 := by rw [F.zero_eq_top]; exact AddSubgroup.mem_top x
  exact ⟨⟨x, hx_mem⟩, hx⟩

/-- The reduction map $\rho: E_0 \to \widetilde{E}(\mathbb{F}_p)$ is surjective
with kernel $E_1$. -/
theorem reduction_surjective_with_kernel
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red)
    (hred_ker : red.ker = F.group 1) :
    ∃ (ρ : ↥(F.group 0) →+ Wred.toAffine.Point),
      Function.Surjective ρ ∧ ρ.ker = (F.group 1).addSubgroupOf (F.group 0) := by
  refine ⟨red.comp (F.group 0).subtype,
    F.hensel_reduction_surjective Wred red hred_surj, ?_⟩
  ext ⟨x, hx⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
    AddSubgroup.mem_addSubgroupOf, ← hred_ker, AddMonoidHom.mem_ker,
    AddSubgroup.coe_subtype]

/-- The first isomorphism theorem applied to the reduction map gives
$E_0/E_1 \cong \widetilde{E}(\mathbb{F}_p)$. -/
theorem quotient_zero_one_iso
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red)
    (hred_ker : red.ker = F.group 1) :
    Nonempty (↥(F.group 0) ⧸ (F.group 1).addSubgroupOf (F.group 0) ≃+ Wred.toAffine.Point) := by
  obtain ⟨ρ, hρ_surj, hρ_ker⟩ := F.reduction_surjective_with_kernel Wred red hred_surj hred_ker
  rw [← hρ_ker]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective ρ hρ_surj⟩

/-- For $n > 0$, the predicate `PadicFiltrationMem` agrees with the
`PadicElliptic.InPadicFiltration` predicate from the formal-group development. -/
lemma padicFiltrationMem_iff_inPadicFiltration (n : ℕ) (hn : 0 < n)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) :
    PadicFiltrationMem W p n P ↔ PadicElliptic.InPadicFiltration W n P := by
  match P with
  | .zero => simp [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
  | .some x y _ =>
    simp only [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
    constructor
    · intro h
      rcases h with rfl | h
      · omega
      · exact h
    · exact Or.inr




/-- The $p$-adic filtration is separated: $\bigcap_{n \geq 0} E_n = 0$. -/
theorem iInf_eq_bot :
    ⨅ n, F.group n = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [AddSubgroup.mem_iInf] at hP
  rw [AddSubgroup.mem_bot]
  match P with
  | .zero => rfl
  | .some x y hxy =>
    exfalso
    have hmem : ∀ n : ℕ, PadicFiltrationMem W p n (.some x y hxy) := fun n =>
      (F.mem_iff n _).mp (hP n)
    have hval : ∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y := by
      intro k
      rcases hmem k.succ with h | ⟨_, hv⟩
      · exact absurd h (Nat.succ_ne_zero k)
      · exact hv
    have : ¬ (∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y) := by
      push Not
      exact ⟨(Padic.valuation x - Padic.valuation y).toNat, by omega⟩
    exact this hval


end PadicFiltration

end

noncomputable section

open Classical

/-- If $p$ is prime, $\gcd(m, p) = 1$, and $m \cdot x = 0$ in $\mathbb{F}_p$,
then $x = 0$. (Multiplication by an integer coprime to $p$ is injective on
$\mathbb{F}_p$.) -/
lemma nsmul_eq_zero_in_zmod_prime {p : ℕ} (hp : Nat.Prime p)
    (m : ℕ) (hm : Nat.Coprime m p) (x : ZMod p) (h : m • x = 0) : x = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with hm0 | hx0
  · rw [ZMod.natCast_eq_zero_iff m p] at hm0
    have : p ∣ Nat.gcd m p := Nat.dvd_gcd hm0 (dvd_refl p)
    rw [hm] at this
    exact absurd this (Nat.Prime.not_dvd_one hp)
  · exact hx0

/-- Predicate: an affine point $P = (x, y) \in E(\mathbb{Q}_p)$ has
$p$-adically integral coordinates, i.e. $v_p(x) \geq 0$ and $v_p(y) \geq 0$
(the point at infinity is vacuously integral). -/
def CoordinatesPadicIntegral {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => 0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y

/-- Valuation bound from the Weierstrass equation: if the coefficients $a_i$
are $p$-integral and the point $(x, y)$ on $E$ does not have integral
coordinates, then $y \neq 0$ and $v_p(x) - v_p(y) \geq 1$. -/
theorem weierstrass_valuation_bound
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
    {x y : ℚ_[p]} (h : (W.baseChange ℚ_[p]).toAffine.Nonsingular x y)
    (h_not_int : ¬ (0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y)) :
    y ≠ 0 ∧ (1 : ℤ) ≤ Padic.valuation x - Padic.valuation y :=
  weierstrass_valuation_bound_proof h_coeff h h_not_int

/-- A point with non-integral coordinates lies in $E_1$ (in fact in some $E_n$
with $n > 0$) but does not lie in every $E_k$, since the filtration is
separated. -/
theorem non_integral_implies_in_filtration
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
    (F : PadicFiltration W p)
    (P : (W.baseChange ℚ_[p]).toAffine.Point)
    (h_not_integral : ¬ CoordinatesPadicIntegral P) :
    ∃ n : ℕ, 0 < n ∧ P ∈ F.group n ∧ ¬ (∀ k : ℕ, P ∈ F.group k) := by
  match P with
  | .zero => exact absurd trivial h_not_integral
  | .some x y hxy =>

    have hval := weierstrass_valuation_bound h_coeff hxy h_not_integral
    have h_in_1 : WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group 1 := by
      rw [F.mem_iff]
      show PadicFiltrationMem W p 1 (.some x y hxy)
      exact Or.inr hval

    have h_ne_zero : WeierstrassCurve.Affine.Point.some x y hxy ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hxy
    have h_not_all : ¬ (∀ k, WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group k) := by
      intro hall
      have h_in_bot : WeierstrassCurve.Affine.Point.some x y hxy ∈
          (⊥ : AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point) := by
        rw [← F.iInf_eq_bot]
        exact AddSubgroup.mem_iInf.mpr hall
      rw [AddSubgroup.mem_bot] at h_in_bot
      exact h_ne_zero h_in_bot
    exact ⟨1, Nat.one_pos, h_in_1, h_not_all⟩


end
