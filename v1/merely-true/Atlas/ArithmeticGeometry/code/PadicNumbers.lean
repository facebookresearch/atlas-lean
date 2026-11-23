/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib

namespace InverseLimit

/-- A countable inverse system: a sequence of types `obj n` together with transition maps
`map n : obj (n + 1) → obj n`. -/
structure NatInverseSystem where
  obj : ℕ → Type*
  map : ∀ n, obj (n + 1) → obj n

namespace NatInverseSystem

variable (S : NatInverseSystem)

/-- The inverse limit of a `NatInverseSystem` $S$: coherent sequences $(a_n)$ with
$a_n \in S_n$ and $S.\mathrm{map}\,n\,(a_{n+1}) = a_n$. -/
def InverseLimit : Type _ :=
  { a : ∀ n, S.obj n // ∀ n, S.map n (a (n + 1)) = a n }

/-- Canonical projection $\mathrm{proj}_n : \mathrm{InverseLimit}\,S \to S_n$. -/
def proj (n : ℕ) (a : S.InverseLimit) : S.obj n :=
  a.val n


/-- Extensionality: two elements of the inverse limit agree iff they agree in every projection. -/
@[ext]
theorem ext {a b : S.InverseLimit} (h : ∀ n, S.proj n a = S.proj n b) : a = b :=
  Subtype.ext (funext h)

/-- Universal property (lift): a compatible family `g n : X → S.obj n` factors through the
inverse limit. -/
def lift {X : Type*} (g : ∀ n, X → S.obj n)
    (hg : ∀ n x, S.map n (g (n + 1) x) = g n x) : X → S.InverseLimit :=
  fun x => ⟨fun n => g n x, fun n => hg n x⟩

/-- Computational rule for `lift`: projecting the lifted map recovers the original family. -/
theorem proj_lift {X : Type*} (g : ∀ n, X → S.obj n)
    (hg : ∀ n x, S.map n (g (n + 1) x) = g n x) (n : ℕ) (x : X) :
    S.proj n (S.lift g hg x) = g n x :=
  rfl

/-- Uniqueness of the lift: any map into the inverse limit whose projections agree with `g` is
equal to `S.lift g hg`. -/
theorem lift_unique {X : Type*} (g : ∀ n, X → S.obj n)
    (hg : ∀ n x, S.map n (g (n + 1) x) = g n x)
    (φ : X → S.InverseLimit) (hφ : ∀ n x, S.proj n (φ x) = g n x) :
    φ = S.lift g hg :=
  funext fun x => S.ext fun n => (hφ n x).trans (S.proj_lift g hg n x).symm

end NatInverseSystem

/-- A countable inverse system of commutative rings: a sequence of `CommRing`s with ring
homomorphism transition maps. -/
structure NatRingInverseSystem where
  obj : ℕ → Type*
  [instCommRing : ∀ n, CommRing (obj n)]
  map : ∀ n, obj (n + 1) →+* obj n

attribute [instance] NatRingInverseSystem.instCommRing

namespace NatRingInverseSystem

variable (S : NatRingInverseSystem)

/-- Forget the ring structure on a `NatRingInverseSystem`, viewing it as a `NatInverseSystem`. -/
def toNatInverseSystem : NatInverseSystem where
  obj := S.obj
  map n := S.map n

/-- The inverse limit of a `NatRingInverseSystem` realized as a subring of the product
$\prod_n S_n$, consisting of coherent sequences. -/
def invLimSubring : Subring (∀ n, S.obj n) where
  carrier := { a | ∀ n, S.map n (a (n + 1)) = a n }
  mul_mem' := fun {a b} ha hb n => by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  one_mem' := fun n => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb n => by
    simp only [Pi.add_apply, map_add, ha n, hb n]
  zero_mem' := fun n => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha n => by
    simp only [Pi.neg_apply, map_neg, ha n]

/-- The inverse limit of a `NatRingInverseSystem` as a commutative ring (alias for the subring
`invLimSubring`). -/
abbrev InverseLimitRing : Type _ := S.invLimSubring

instance : CommRing S.InverseLimitRing := inferInstance

/-- The $n$-th projection ring homomorphism `InverseLimitRing →+* S.obj n`. -/
def projRingHom (n : ℕ) : S.InverseLimitRing →+* S.obj n :=
  (Pi.evalRingHom (fun n => S.obj n) n).comp S.invLimSubring.subtype

end NatRingInverseSystem

section ZModSystem

/-- The `NatInverseSystem` whose $n$-th object is $\mathbb{Z}/p^{n+1}\mathbb{Z}$ and whose
transition maps are reduction modulo $p^{n+1}$ to $p^n$. -/
noncomputable def zmodInverseSystem (p : ℕ) [Fact (Nat.Prime p)] : NatInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

/-- The `NatRingInverseSystem` whose $n$-th object is the commutative ring
$\mathbb{Z}/p^{n+1}\mathbb{Z}$ with reduction ring homomorphisms. -/
noncomputable def zmodRingInverseSystem (p : ℕ) [Fact (Nat.Prime p)] :
    NatRingInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    CommRing (zmodRingInverseSystem p).InverseLimitRing :=
  inferInstance

end ZModSystem

end InverseLimit

/-- Definition 4.18 (discrete valuation): a function $v : R \to \mathbb{Z} \cup \{\infty\}$
satisfying $v(a) = \infty \iff a = 0$, $v(ab) = v(a) + v(b)$, and the ultrametric inequality
$\min(v(a), v(b)) \le v(a + b)$. -/
structure DiscreteValuation (R : Type*) [CommRing R] where
  val : R → WithTop ℤ
  val_eq_top_iff : ∀ a : R, val a = ⊤ ↔ a = 0
  val_mul : ∀ a b : R, val (a * b) = val a + val b
  val_add : ∀ a b : R, min (val a) (val b) ≤ val (a + b)

namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

instance : CoeFun (DiscreteValuation R) (fun _ => R → WithTop ℤ) where
  coe v := v.val

/-- Definitional unfolding: the coercion of the anonymous constructor `⟨f, h1, h2, h3⟩` to a
function is `f` itself. -/
@[simp]
theorem coe_mk (f : R → WithTop ℤ) (h1 h2 h3) :
    ((⟨f, h1, h2, h3⟩ : DiscreteValuation R) : R → WithTop ℤ) = f := rfl

/-- Extensionality for discrete valuations: agreement pointwise on $R$ implies equality. -/
@[ext]
theorem ext {v w : DiscreteValuation R} (h : ∀ x, v x = w x) : v = w := by
  cases v; cases w
  congr 1
  funext x
  exact h x

/-- A discrete valuation sends $0$ to $\infty$. -/
@[simp]
theorem val_zero : v 0 = ⊤ := (v.val_eq_top_iff 0).mpr rfl


end DiscreteValuation

namespace PadicIntegers

noncomputable section

open PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

/-- The subring of $\prod_n \mathbb{Z}/p^n\mathbb{Z}$ consisting of compatible sequences with
respect to all reduction maps $\mathbb{Z}/p^n\mathbb{Z} \to \mathbb{Z}/p^m\mathbb{Z}$ for
$m \le n$. This is the explicit inverse-limit model for $\mathbb{Z}_p$. -/
def zmodInvLimSubring : Subring (∀ n, ZMod (p ^ n)) where
  carrier := { a | ∀ (m n : ℕ) (h : m ≤ n),
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) (a n) = a m }
  mul_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.mul_apply, map_mul, ha m n hmn, hb m n hmn]
  one_mem' := fun m n hmn => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.add_apply, map_add, ha m n hmn, hb m n hmn]
  zero_mem' := fun m n hmn => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha m n hmn => by
    simp only [Pi.neg_apply, map_neg, ha m n hmn]

/-- The $n$-th projection ring homomorphism from `zmodInvLimSubring` to $\mathbb{Z}/p^n\mathbb{Z}$.
-/
def invLimProj (n : ℕ) : (zmodInvLimSubring p) →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n => ZMod (p ^ n)) n).comp (zmodInvLimSubring p).subtype

omit hp in
/-- Compatibility of the projections: the reduction $\mathbb{Z}/p^n\mathbb{Z} \to
\mathbb{Z}/p^m\mathbb{Z}$ composed with `invLimProj p n` equals `invLimProj p m` for $m \le n$. -/
theorem invLimProj_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (invLimProj p n) =
      invLimProj p m := by
  ext ⟨a, ha⟩
  simp only [invLimProj, RingHom.comp_apply, Pi.evalRingHom_apply, Subring.coe_subtype]
  exact ha m n h

/-- Forward map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
sends $x \in \mathbb{Z}_p$ to the compatible sequence of its reductions modulo $p^n$. -/
def padicIntToInvLim : ℤ_[p] →+* (zmodInvLimSubring p) where
  toFun x := ⟨fun n => toZModPow n x, fun m n h =>
    RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n h) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' x y := Subtype.ext (funext fun _ => map_mul _ x y)
  map_add' x y := Subtype.ext (funext fun _ => map_add _ x y)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)

/-- Inverse map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
obtained via the universal property `PadicInt.lift` from the family of compatible projections. -/
def invLimToPadicInt : (zmodInvLimSubring p) →+* ℤ_[p] :=
  PadicInt.lift (invLimProj_compat p)

/-- Theorem 4.6 (inverse-limit description): the ring isomorphism $\mathbb{Z}_p \simeq
\varprojlim_n \mathbb{Z}/p^n\mathbb{Z}$. -/
def padicIntEquivInvLim : ℤ_[p] ≃+* (zmodInvLimSubring p) :=
  RingEquiv.ofRingHom
    (padicIntToInvLim p)
    (invLimToPadicInt p)
    (RingHom.ext fun a => by
      ext n
      simp only [padicIntToInvLim, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        RingHom.comp_apply, RingHom.id_apply]
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) = (a : ∀ n, ZMod (p ^ n)) n
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) a from rfl,
        PadicInt.lift_spec]
      rfl)
    (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, RingHom.id_apply]
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) = _
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) (padicIntToInvLim p x) from rfl,
        PadicInt.lift_spec]
      simp [invLimProj, padicIntToInvLim])

instance : CommRing (zmodInvLimSubring p) := inferInstance

/-- Reducible alias for the commutative ring structure on $\mathbb{Z}_p$. -/
@[reducible] def padicInt_commRing : CommRing ℤ_[p] := inferInstance

end

end PadicIntegers

namespace PadicUnits

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The group of units of $\mathbb{Z}_p$, abbreviated `padicUnits p`. -/
abbrev padicUnits : Type := (ℤ_[p])ˣ

instance : Group (padicUnits p) := inferInstance

instance : CommGroup (padicUnits p) := inferInstance

end

end PadicUnits

namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $n$-th digit in the $p$-adic expansion of $a \in \mathbb{Z}_p$, defined via the
`PadicInt.appr` natural-number approximation. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

/-- Each $p$-adic digit lies in $\{0, 1, \ldots, p-1\}$. -/
theorem padicDigit_lt (a : ℤ_[p]) (n : ℕ) : padicDigit a n < p := by
  unfold padicDigit
  obtain ⟨k, hk⟩ := dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
  rw [hk, Nat.mul_div_cancel_left _ (pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))]
  have h_sub_lt : a.appr (n + 1) - a.appr n < p ^ (n + 1) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (appr_lt a (n + 1))
  rw [hk, pow_succ] at h_sub_lt
  exact Nat.lt_of_mul_lt_mul_left h_sub_lt

/-- The $p$-adic expansion of $a \in \mathbb{Z}_p$ as a sequence valued in `Fin p`, packaging
`padicDigit` together with the bound `padicDigit_lt`. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : ℕ) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩


/-- Reconstruction relation: the digit times $p^n$ equals the difference of consecutive
approximations of $a$. -/
theorem padicDigit_mul_pow (a : ℤ_[p]) (n : ℕ) :
    padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n := by
  unfold padicDigit
  exact Nat.div_mul_cancel (dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n))

/-- Successor relation for approximations: $a_{n+1} = a_n + d_n \cdot p^n$, where $d_n$ is the
$n$-th $p$-adic digit. -/
theorem appr_succ_eq (a : ℤ_[p]) (n : ℕ) :
    a.appr (n + 1) = a.appr n + padicDigit a n * p ^ n := by
  have hle : a.appr n ≤ a.appr (n + 1) := appr_mono a (Nat.le_succ n)
  have hd := padicDigit_mul_pow a n
  omega

/-- Closed-form for the approximation: $a_n = \sum_{k<n} d_k\,p^k$. -/
theorem appr_eq_sum_padicDigit (a : ℤ_[p]) (n : ℕ) :
    a.appr n = ∑ k ∈ range n, padicDigit a k * p ^ k := by
  induction n with
  | zero => simp [appr]
  | succ n ih =>
    rw [sum_range_succ, ← ih, appr_succ_eq]

/-- Given a sequence of digits $b : \mathbb{N} \to \mathrm{Fin}\,p$, the partial sum
$\sum_{k<n} b_k\,p^k \in \mathbb{Z}$. -/
noncomputable def digitPartialSum (b : ℕ → Fin p) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, (b k).val * (p : ℤ) ^ k

omit hp in
/-- The digit partial sum is nonnegative. -/
lemma digitPartialSum_nonneg (b : ℕ → Fin p) (n : ℕ) : 0 ≤ digitPartialSum b n := by
  apply Finset.sum_nonneg; intro k _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

omit hp in
/-- The partial sum is strictly bounded by $p^n$. -/
lemma digitPartialSum_lt (b : ℕ → Fin p) (n : ℕ) : digitPartialSum b n < (p : ℤ) ^ n := by
  induction n with
  | zero => simp [digitPartialSum]
  | succ n ih =>
    unfold digitPartialSum at ih ⊢; rw [Finset.sum_range_succ]
    have hb : ((b n).val : ℤ) ≤ p - 1 := by have := (b n).isLt; omega
    calc ∑ k ∈ Finset.range n, ((b k).val : ℤ) * (p : ℤ) ^ k + (b n).val * (p : ℤ) ^ n
        _ < (p : ℤ) ^ n + (p - 1) * (p : ℤ) ^ n := by
          have := mul_le_mul_of_nonneg_right hb (pow_nonneg (Nat.cast_nonneg p) n); linarith
        _ = (p : ℤ) ^ (n + 1) := by ring

set_option maxHeartbeats 800000 in
/-- Surjectivity of `padicExpansion`: every sequence $(b_n)_{n \in \mathbb{N}}$ with
$b_n \in \{0, \ldots, p - 1\}$ arises as the digit sequence of some $x \in \mathbb{Z}_p$. -/
theorem padicExpansion_surjective (b : ℕ → Fin p) :
    ∃ (x : ℤ_[p]), ∀ n, padicExpansion x n = b n := by

  set S := digitPartialSum b with hS_def

  have h_dvd : ∀ n, (p : ℤ) ^ n ∣ S (n + 1) - S n := by
    intro n; simp only [hS_def, digitPartialSum, Finset.sum_range_succ, add_sub_cancel_left]
    exact dvd_mul_left _ _

  set x : ℤ_[p] := PadicInt.ofIntSeq S
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub S p h_dvd)
  use x

  have h_appr_eq : ∀ n, (x.appr n : ℤ) = S n := by
    intro n
    have h_zmod := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub S p h_dvd n

    have h_dvd_diff : (p ^ n : ℤ) ∣ (x.appr n : ℤ) - S n := by
      have h_eq : (↑(x.appr n) : ZMod (p ^ n)) = (↑(S n) : ZMod (p ^ n)) := by
        change PadicInt.toZModPow n x = _; exact h_zmod
      have : ((↑(x.appr n) - S n : ℤ) : ZMod (p ^ n)) = 0 := by
        push_cast; exact sub_eq_zero.mpr h_eq
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at this

    have h_appr_lt : (x.appr n : ℤ) < (p : ℤ) ^ n := by exact_mod_cast appr_lt x n
    have h_S_lt : S n < (p : ℤ) ^ n := hS_def ▸ digitPartialSum_lt b n
    have h_S_nn : (0 : ℤ) ≤ S n := hS_def ▸ digitPartialSum_nonneg b n
    have hp_pos : (0 : ℤ) < (p : ℤ) ^ n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))
    obtain ⟨c, hc⟩ := h_dvd_diff
    have : -1 < c := by nlinarith [Nat.cast_nonneg (α := ℤ) (x.appr n)]
    have : c < 1 := by nlinarith
    rw [show c = 0 by omega, mul_zero] at hc; linarith

  intro n
  apply Fin.ext; show padicDigit x n = (b n).val
  have hle : x.appr n ≤ x.appr (n + 1) := by
    have : (x.appr n : ℤ) ≤ x.appr (n + 1) := by
      rw [h_appr_eq n, h_appr_eq (n + 1), hS_def, digitPartialSum, digitPartialSum,
          Finset.sum_range_succ]
      linarith [mul_nonneg (show (0 : ℤ) ≤ (b n).val from Nat.cast_nonneg _)
        (show (0 : ℤ) ≤ (p : ℤ) ^ n from pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast this
  suffices h : x.appr (n + 1) - x.appr n = (b n).val * p ^ n by
    unfold padicDigit; rw [h]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))
  zify [hle]
  rw [h_appr_eq (n + 1), h_appr_eq n, hS_def, digitPartialSum, digitPartialSum,
    Finset.sum_range_succ, add_sub_cancel_left]

/-- Injectivity of `padicExpansion`: two $p$-adic integers with the same digit sequence are
equal. -/
theorem padicExpansion_injective :
    Function.Injective (padicExpansion (p := p)) := by
  intro x y h
  have hd : ∀ n, padicDigit x n = padicDigit y n := by
    intro n; exact congr_arg Fin.val (congr_fun h n)
  have ha : ∀ n, x.appr n = y.appr n := by
    intro n
    rw [appr_eq_sum_padicDigit x n, appr_eq_sum_padicDigit y n]
    congr 1; ext k; congr 1; exact hd k
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have hx := appr_spec n x
  rw [ha n] at hx
  have h_sub : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    have := Ideal.sub_mem _ hx (appr_spec n y); rwa [sub_sub_sub_cancel_right] at this
  rw [← ker_toZModPow] at h_sub
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at h_sub

/-- Theorem 4.6 (bijection between $p$-adic expansions and $\mathbb{Z}_p$): the digit-extraction
map `padicExpansion : ℤ_[p] → (ℕ → Fin p)` is a bijection. -/
theorem padicExpansion_bijective :
    Function.Bijective (padicExpansion (p := p)) :=
  ⟨padicExpansion_injective, fun b =>
    let ⟨x, hx⟩ := padicExpansion_surjective b
    ⟨x, funext hx⟩⟩

end PadicInt

open PadicInt

section DVRDefinition

/-- A discrete valuation ring is a principal ideal ring. -/
theorem IsDiscreteValuationRing.isPrincipalIdealRing
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsPrincipalIdealRing R :=
  inferInstance

/-- A discrete valuation ring is a local ring. -/
theorem IsDiscreteValuationRing.isLocalRing
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsLocalRing R :=
  inferInstance


end DVRDefinition

section PadicIntDVR

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- $\mathbb{Z}_p$ is a discrete valuation ring. -/
theorem PadicInt.isDiscreteValuationRing : IsDiscreteValuationRing ℤ_[p] :=
  inferInstance

end PadicIntDVR

section Theorem48

open PadicInt

variable {p : ℕ} [hp : Fact p.Prime]


/-- The reduction $\mathbb{Z}_p \twoheadrightarrow \mathbb{Z}/p^m\mathbb{Z}$ is surjective. -/
theorem PadicInt.toZModPow_surjective (m : ℕ) :
    Function.Surjective (toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n, by simp [toZModPow, toZModHom]⟩

/-- Exactness statement: the image of multiplication by $p^m$ on $\mathbb{Z}_p$ coincides with the
kernel of the reduction `toZModPow m`. -/
theorem PadicInt.exact_mul_pow_p_toZModPow (m : ℕ) :
    Set.range (fun (a : ℤ_[p]) => (p : ℤ_[p]) ^ m * a) =
      ↑(RingHom.ker (toZModPow m : ℤ_[p] →+* ZMod (p ^ m))) := by
  rw [ker_toZModPow]
  ext x
  simp only [Set.mem_range, SetLike.mem_coe, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

/-- Ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$ obtained from the
first isomorphism theorem applied to `toZModPow m`. -/
noncomputable def PadicInt.quotientSpanPowPEquivZMod (m : ℕ) :
    ℤ_[p] ⧸ (Ideal.span {(p : ℤ_[p]) ^ m}) ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

end Theorem48
open PadicInt in
/-- Corollary 4.9: the ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$. -/
noncomputable def PadicInt.corollary_4_9 (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow (p := p) m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

section PadicValuation

noncomputable section

open PadicInt Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The $p$-adic valuation on $\mathbb{Z}_p$ extended to $\mathbb{N} \cup \{\infty\}$:
$v(0) = \infty$ and $v(a) = \mathrm{PadicInt.valuation}(a)$ otherwise. -/
def padicValuationDef (a : ℤ_[p]) : WithTop ℕ :=
  if a = 0 then ⊤ else ↑(PadicInt.valuation a)

/-- $v(0) = \infty$. -/
@[simp]
theorem padicValuationDef_zero : padicValuationDef (0 : ℤ_[p]) = ⊤ := by
  simp [padicValuationDef]

/-- For nonzero $a$, the extended valuation agrees with the natural-number-valued
`PadicInt.valuation`. -/
@[simp]
theorem padicValuationDef_of_ne_zero {a : ℤ_[p]} (ha : a ≠ 0) :
    padicValuationDef a = ↑(PadicInt.valuation a) := by
  simp [padicValuationDef, ha]

/-- A nonzero $p$-adic integer has finite valuation. -/
theorem padicValuationDef_ne_top {a : ℤ_[p]} (ha : a ≠ 0) : padicValuationDef a ≠ ⊤ := by
  simp [ha]


/-- Multiplicativity of the valuation: $v(ab) = v(a) + v(b)$ when both $a, b$ are nonzero. -/
theorem padicValuationDef_mul {a b : ℤ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValuationDef (a * b) = padicValuationDef a + padicValuationDef b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [padicValuationDef_of_ne_zero ha, padicValuationDef_of_ne_zero hb,
    padicValuationDef_of_ne_zero hab, PadicInt.valuation_mul ha hb, Nat.cast_add]


/-- Ultrametric inequality: $\min(v(a), v(b)) \le v(a + b)$. -/
theorem padicValuationDef_add (a b : ℤ_[p]) :
    min (padicValuationDef a) (padicValuationDef b) ≤ padicValuationDef (a + b) := by
  by_cases hab : a + b = 0
  · simp [hab]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [padicValuationDef_of_ne_zero ha, padicValuationDef_of_ne_zero hb,
    padicValuationDef_of_ne_zero hab]
  calc min (↑(a.valuation) : WithTop ℕ) ↑(b.valuation)
      = ↑(min a.valuation b.valuation) := by norm_cast
    _ ≤ ↑((a + b).valuation) := WithTop.coe_le_coe.mpr (PadicInt.le_valuation_add hab)

end

end PadicValuation

section Corollary4_13

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Corollary 4.13 (part): $\mathbb{Z}_p$ is an integral domain. -/
theorem PadicInt.isDomain : IsDomain ℤ_[p] :=
  inferInstance


end Corollary4_13

section Theorem4_15

noncomputable section

open PadicInt Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Any unit of $\mathbb{Z}_p$ has valuation $0$. -/
lemma unit_valuation_zero (u : ℤ_[p]ˣ) : PadicInt.valuation (u : ℤ_[p]) = 0 := by
  have hu_ne : (u : ℤ_[p]) ≠ 0 := u.ne_zero
  have huinv_ne : (↑u⁻¹ : ℤ_[p]) ≠ 0 := (u⁻¹).ne_zero
  have h1 : (u : ℤ_[p]) * (↑u⁻¹ : ℤ_[p]) = 1 := by exact_mod_cast u.mul_inv
  have hval : PadicInt.valuation (u : ℤ_[p]) + PadicInt.valuation (↑u⁻¹ : ℤ_[p]) = 0 := by
    rw [← PadicInt.valuation_mul hu_ne huinv_ne, h1, PadicInt.valuation_one]
  omega

/-- Theorem 4.15 (units): a nonzero $a \in \mathbb{Z}_p$ is a unit if and only if its valuation
is zero. -/
theorem thm_4_15_units_valuation (a : ℤ_[p]) (ha : a ≠ 0) :
    IsUnit a ↔ PadicInt.valuation a = 0 := by
  constructor
  · intro ⟨u, hu⟩
    rw [← hu]
    exact unit_valuation_zero u
  · intro h
    rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation ha, h]
    simp


/-- Theorem 4.15 (unique factorization): every nonzero $a \in \mathbb{Z}_p$ admits a unique
factorization $a = p^n \cdot u$ with $n \in \mathbb{N}$ and $u \in \mathbb{Z}_p^\times$. -/
theorem thm_4_15_unique_factorization (a : ℤ_[p]) (ha : a ≠ 0) :
    ∃! nu : ℕ × (ℤ_[p])ˣ, a = (p : ℤ_[p]) ^ nu.1 * ↑nu.2 := by

  refine ⟨⟨a.valuation, PadicInt.unitCoeff ha⟩, ?_, ?_⟩
  ·
    simp only
    rw [mul_comm]
    exact PadicInt.unitCoeff_spec ha
  ·
    rintro ⟨m, u⟩ hmu
    simp only at hmu
    have hu_ne : (u : ℤ_[p]) ≠ 0 := u.ne_zero
    have hu_val : PadicInt.valuation (u : ℤ_[p]) = 0 := unit_valuation_zero u
    have hp_ne : (p : ℤ_[p]) ≠ 0 := NeZero.ne _


    have hm_eq : m = a.valuation := by
      have : a.valuation = m := by
        rw [hmu, PadicInt.valuation_p_pow_mul m (u : ℤ_[p]) hu_ne, hu_val, add_zero]
      omega


    have hu_eq : u = PadicInt.unitCoeff ha := by
      ext
      have hspec := PadicInt.unitCoeff_spec ha
      have key : (p : ℤ_[p]) ^ m * (u : ℤ_[p]) =
          (p : ℤ_[p]) ^ m * ↑(PadicInt.unitCoeff ha) := by
        calc (p : ℤ_[p]) ^ m * (u : ℤ_[p])
            = a := hmu.symm
          _ = ↑(PadicInt.unitCoeff ha) * (p : ℤ_[p]) ^ a.valuation := hspec
          _ = ↑(PadicInt.unitCoeff ha) * (p : ℤ_[p]) ^ m := by rw [← hm_eq]
          _ = (p : ℤ_[p]) ^ m * ↑(PadicInt.unitCoeff ha) := by ring
      exact mul_left_cancel₀ (pow_ne_zero _ hp_ne) key
    exact Prod.ext hm_eq hu_eq

end

end Theorem4_15

section Theorem4_16

noncomputable section

open PadicInt Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Theorem 4.16: every nonzero ideal of $\mathbb{Z}_p$ is of the form $(p^m)$ for some
$m \in \mathbb{N}$. -/
theorem thm_4_16_nonzero_ideal_span_pow
    (I : Ideal ℤ_[p]) (hI : I ≠ ⊥) :
    ∃ m : ℕ, I = Ideal.span {(p : ℤ_[p]) ^ m} :=
  ideal_eq_span_pow_p hI


end

end Theorem4_16

section Corollary4_17

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Corollary 4.17 (part): $\mathbb{Z}_p$ is a principal ideal ring. -/
theorem PadicInt.isPrincipalIdealRing : IsPrincipalIdealRing ℤ_[p] :=
  inferInstance

/-- Corollary 4.17 (part): $\mathbb{Z}_p$ is a local ring. -/
theorem PadicInt.isLocalRing : IsLocalRing ℤ_[p] :=
  inferInstance

end Corollary4_17
