/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

namespace HeckeAlgebra

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B}

/-- The pair of scalars $(a_s, b_s)_{s ∈ B}$ defining the quadratic relation
$T_s^2 = a_s T_s + b_s T_1$ for a generic Hecke algebra. -/
structure StructureConstants (B : Type*) (R : Type*) [CommRing R] where
  a : B → R
  b : B → R

variable {R : Type*} [CommRing R]

/-- The structure constants are conjugacy-invariant if conjugate simple reflections
have equal $(a_s, b_s)$ values. -/
def StructureConstants.ConjugacyInvariant (sc : StructureConstants B R)
    (cs : CoxeterSystem M W) : Prop :=
  ∀ (s₁ s₂ : B) (w : W), w * cs.simple s₁ * w⁻¹ = cs.simple s₂ →
    sc.a s₁ = sc.a s₂ ∧ sc.b s₁ = sc.b s₂

/-- A generic Hecke algebra over $R$ for the Coxeter matrix $M$: an $R$-module
`carrier` with basis $\{T_w : w ∈ W\}$, satisfying the length-up rule
$T_s T_w = T_{sw}$ when $\ell(sw) > \ell(w)$, the quadratic relation
$T_s^2 = a_s T_s + b_s T_1$, left/right identity for $T_1$, two-sided generator
associativity, and a basis-span induction principle. -/
structure GenericAlgebra (M : CoxeterMatrix B) (R : Type*) [CommRing R] where
  carrier : Type*
  basis : M.Group → carrier
  smul : R → carrier → carrier
  mul : carrier → carrier → carrier
  add : carrier → carrier → carrier
  sc : StructureConstants B R
  length_up : let cs := M.toCoxeterSystem
    ∀ (s : B) (w : M.Group),
    cs.length (cs.simple s * w) > cs.length w →
    mul (basis (cs.simple s)) (basis w) = basis (cs.simple s * w)
  quadratic : let cs := M.toCoxeterSystem
    ∀ (s : B),
    mul (basis (cs.simple s)) (basis (cs.simple s)) =
      add (smul (sc.a s) (basis (cs.simple s)))
          (smul (sc.b s) (basis 1))
  identity_left : ∀ (x : carrier), mul (basis 1) x = x
  identity_right : ∀ (x : carrier), mul x (basis 1) = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  gen_left_assoc : let cs := M.toCoxeterSystem
    ∀ (s : B) (x y : carrier),
    mul (basis (cs.simple s)) (mul x y) = mul (mul (basis (cs.simple s)) x) y
  gen_right_assoc : let cs := M.toCoxeterSystem
    ∀ (t : B) (x y : carrier),
    mul (mul x y) (basis (cs.simple t)) = mul x (mul y (basis (cs.simple t)))
  basis_span : ∀ (P : carrier → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z


section CoxeterLemmas

variable {M : CoxeterMatrix B}

/-- Length inequality used in the right-length-up induction. -/
theorem length_swt_gt_sw (cs : CoxeterSystem M M.Group) (s t : B) (w : M.Group)
    (hsw : cs.length (cs.simple s * w) < cs.length w)
    (hwt : cs.length (w * cs.simple t) > cs.length w) :
    cs.length (cs.simple s * w * cs.simple t) > cs.length (cs.simple s * w) := by
  rcases cs.length_mul_simple (cs.simple s * w) t with h_up | h_down
  · omega
  · have key : cs.simple s * (cs.simple s * w * cs.simple t) = w * cs.simple t := by
      rw [← mul_assoc, cs.simple_mul_simple_cancel_left s]
    rcases cs.length_simple_mul (cs.simple s * w * cs.simple t) s with h1 | h1
    · rw [key] at h1
      rcases cs.length_simple_mul w s with hs1 | hs1 <;>
        rcases cs.length_mul_simple w t with ht1 | ht1 <;> omega
    · rw [key] at h1
      rcases cs.length_simple_mul w s with hs1 | hs1 <;>
        rcases cs.length_mul_simple w t with ht1 | ht1 <;> omega

/-- Cancellation identity $s · (s · w · t) = w · t$ in the Coxeter group. -/
theorem s_mul_swt_eq_wt (cs : CoxeterSystem M M.Group) (s t : B) (w : M.Group) :
    cs.simple s * (cs.simple s * w * cs.simple t) = w * cs.simple t := by
  rw [← mul_assoc, cs.simple_mul_simple_cancel_left s]

end CoxeterLemmas

/-- Length-down rule derived from the length-up rule and the quadratic relation:
when $\ell(sw) < \ell(w)$, $T_s T_w = a_s T_w + b_s T_{sw}$. -/
theorem GenericAlgebra.SatisfiesLengthDownRule (A : GenericAlgebra M R) :
    let cs := M.toCoxeterSystem
    ∀ (s : B) (w : M.Group),
      cs.length (cs.simple s * w) < cs.length w →
      A.mul (A.basis (cs.simple s)) (A.basis w) =
        A.add (A.smul (A.sc.a s) (A.basis w))
              (A.smul (A.sc.b s) (A.basis (cs.simple s * w))) := by
  intro cs s w hlength
  set sw := cs.simple s * w
  have hw : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
  have hlength_up_sw : cs.length (cs.simple s * sw) > cs.length sw := by
    rw [hw]; exact hlength
  have h_Ts_Tsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
    rw [A.length_up s sw hlength_up_sw, hw]
  calc A.mul (A.basis (cs.simple s)) (A.basis w)
      = A.mul (A.basis (cs.simple s))
              (A.mul (A.basis (cs.simple s)) (A.basis sw)) := by
          rw [h_Ts_Tsw]
      _ = A.mul (A.mul (A.basis (cs.simple s)) (A.basis (cs.simple s)))
                (A.basis sw) := by
          rw [A.gen_left_assoc]
      _ = A.mul (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
                       (A.smul (A.sc.b s) (A.basis 1)))
                (A.basis sw) := by
          rw [A.quadratic]
      _ = A.add (A.mul (A.smul (A.sc.a s) (A.basis (cs.simple s))) (A.basis sw))
               (A.mul (A.smul (A.sc.b s) (A.basis 1)) (A.basis sw)) := by
          rw [A.mul_add_left]
      _ = A.add (A.smul (A.sc.a s) (A.mul (A.basis (cs.simple s)) (A.basis sw)))
               (A.smul (A.sc.b s) (A.mul (A.basis 1) (A.basis sw))) := by
          rw [A.smul_mul_left, A.smul_mul_left]
      _ = A.add (A.smul (A.sc.a s) (A.basis w))
               (A.smul (A.sc.b s) (A.basis sw)) := by
          rw [h_Ts_Tsw, A.identity_left]

/-- Right-multiplication analogue of the length-up rule: when $\ell(wt) > \ell(w)$,
$T_w T_t = T_{wt}$. Proved by induction on $\ell(w)$. -/
theorem GenericAlgebra.SatisfiesRightLengthUpRule (A : GenericAlgebra M R) :
    let cs := M.toCoxeterSystem
    ∀ (t : B) (w : M.Group),
      cs.length (w * cs.simple t) > cs.length w →
      A.mul (A.basis w) (A.basis (cs.simple t)) = A.basis (w * cs.simple t) := by
  intro cs t
  suffices ∀ (n : ℕ) (w : M.Group), cs.length w ≤ n →
      cs.length (w * cs.simple t) > cs.length w →
      A.mul (A.basis w) (A.basis (cs.simple t)) = A.basis (w * cs.simple t) by
    intro w hwt
    exact this (cs.length w) w le_rfl hwt
  intro n
  induction n with
  | zero =>
    intro w hw hwt
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    simp only [one_mul]
    rw [A.identity_left]
  | succ n ih =>
    intro w hw hwt
    by_cases hw1 : w = 1
    · subst hw1; simp only [one_mul]; rw [A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w with sw_def
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt
      have h_TsTsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      have hswt_gt : cs.length (sw * cs.simple t) > cs.length sw := by
        rw [sw_def]; exact length_swt_gt_sw cs s t w hsw_lt hwt
      have h_ind : A.mul (A.basis sw) (A.basis (cs.simple t)) =
          A.basis (sw * cs.simple t) := by
        apply ih sw; omega; exact hswt_gt
      have hs_swt : cs.length (cs.simple s * (sw * cs.simple t)) >
          cs.length (sw * cs.simple t) := by
        rw [sw_def, s_mul_swt_eq_wt cs s t w]
        rcases cs.length_simple_mul w s with h | h <;>
          rcases cs.length_mul_simple w t with h' | h' <;>
          rcases cs.length_mul_simple (cs.simple s * w) t with h'' | h'' <;>
          (rw [sw_def] at hsw_lt hswt_gt; omega)
      calc A.mul (A.basis w) (A.basis (cs.simple t))
          = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw))
                  (A.basis (cs.simple t)) := by rw [h_TsTsw]
          _ = A.mul (A.basis (cs.simple s))
                    (A.mul (A.basis sw) (A.basis (cs.simple t))) := by
              rw [← A.gen_left_assoc]
          _ = A.mul (A.basis (cs.simple s)) (A.basis (sw * cs.simple t)) := by
              rw [h_ind]
          _ = A.basis (cs.simple s * (sw * cs.simple t)) := by
              rw [A.length_up s (sw * cs.simple t) hs_swt]
          _ = A.basis (w * cs.simple t) := by
              rw [sw_def, s_mul_swt_eq_wt cs s t w]

/-- Left-multiplication by a basis element is associative: $T_w · (y · z) = (T_w · y) · z$.
Proved by induction on $\ell(w)$ using `gen_left_assoc`. -/
theorem GenericAlgebra.basis_left_mul_assoc (A : GenericAlgebra M R) :
    let _cs := M.toCoxeterSystem
    ∀ (w : M.Group) (y z : A.carrier),
      A.mul (A.basis w) (A.mul y z) = A.mul (A.mul (A.basis w) y) z := by
  intro cs
  suffices ∀ (n : ℕ) (w : M.Group), cs.length w ≤ n →
      ∀ (y z : A.carrier),
        A.mul (A.basis w) (A.mul y z) = A.mul (A.mul (A.basis w) y) z by
    intro w y z
    exact this (cs.length w) w le_rfl y z
  intro n
  induction n with
  | zero =>
    intro w hw y z
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    simp only [A.identity_left]
  | succ n ih =>
    intro w hw y z
    by_cases hw1 : w = 1
    · subst hw1; simp only [A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt
      have h_basis_w : A.basis w = A.mul (A.basis (cs.simple s)) (A.basis sw) := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      calc A.mul (A.basis w) (A.mul y z)
          = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) (A.mul y z) := by
              rw [← h_basis_w]
          _ = A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) (A.mul y z)) := by
              rw [← A.gen_left_assoc]
          _ = A.mul (A.basis (cs.simple s)) (A.mul (A.mul (A.basis sw) y) z) := by
              rw [ih sw (by omega) y z]
          _ = A.mul (A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) y)) z := by
              rw [A.gen_left_assoc]
          _ = A.mul (A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) y) z := by
              rw [A.gen_left_assoc]
          _ = A.mul (A.mul (A.basis w) y) z := by
              rw [← h_basis_w]

/-- Full associativity of the generic Hecke product, $(x · y) · z = x · (y · z)$,
obtained from `basis_left_mul_assoc` via the basis-span principle. -/
theorem GenericAlgebra.mul_assoc (A : GenericAlgebra M R) :
    ∀ x y z, A.mul (A.mul x y) z = A.mul x (A.mul y z) := by


  suffices ∀ x, ∀ y z, A.mul (A.mul x y) z = A.mul x (A.mul y z) by
    intro x y z; exact this x y z
  apply A.basis_span (fun x => ∀ y z, A.mul (A.mul x y) z = A.mul x (A.mul y z))
  ·
    intro w y z
    exact (A.basis_left_mul_assoc w y z).symm
  ·
    intro x₁ x₂ hx₁ hx₂ y z
    calc A.mul (A.mul (A.add x₁ x₂) y) z
        = A.mul (A.add (A.mul x₁ y) (A.mul x₂ y)) z := by rw [A.mul_add_left]
      _ = A.add (A.mul (A.mul x₁ y) z) (A.mul (A.mul x₂ y) z) := by rw [A.mul_add_left]
      _ = A.add (A.mul x₁ (A.mul y z)) (A.mul x₂ (A.mul y z)) := by rw [hx₁, hx₂]
      _ = A.mul (A.add x₁ x₂) (A.mul y z) := by rw [A.mul_add_left]
  ·
    intro r x hx y z
    calc A.mul (A.mul (A.smul r x) y) z
        = A.mul (A.smul r (A.mul x y)) z := by rw [A.smul_mul_left]
      _ = A.smul r (A.mul (A.mul x y) z) := by rw [A.smul_mul_left]
      _ = A.smul r (A.mul x (A.mul y z)) := by rw [hx]
      _ = A.mul (A.smul r x) (A.mul y z) := by rw [A.smul_mul_left]

/-- Right-multiplication length-down rule: when $\ell(ws) < \ell(w)$,
$T_w T_s = a_s T_w + b_s T_{ws}$. -/
theorem GenericAlgebra.SatisfiesRightLengthDownRule (A : GenericAlgebra M R) :
    let cs := M.toCoxeterSystem
    ∀ (s : B) (w : M.Group),
      cs.length (w * cs.simple s) < cs.length w →
      A.mul (A.basis w) (A.basis (cs.simple s)) =
        A.add (A.smul (A.sc.a s) (A.basis w))
              (A.smul (A.sc.b s) (A.basis (w * cs.simple s))) := by
  intro cs s w hlength
  set ws := w * cs.simple s
  have hw : ws * cs.simple s = w := by
    show w * cs.simple s * cs.simple s = w
    exact cs.simple_mul_simple_cancel_right s
  have hlen_ws : cs.length (ws * cs.simple s) > cs.length ws := by
    rw [hw]; exact hlength
  have h_Tws_Ts : A.mul (A.basis ws) (A.basis (cs.simple s)) = A.basis w := by
    rw [A.SatisfiesRightLengthUpRule s ws hlen_ws, hw]
  calc A.mul (A.basis w) (A.basis (cs.simple s))
      = A.mul (A.mul (A.basis ws) (A.basis (cs.simple s)))
              (A.basis (cs.simple s)) := by
          rw [h_Tws_Ts]
      _ = A.mul (A.basis ws)
                (A.mul (A.basis (cs.simple s)) (A.basis (cs.simple s))) := by
          rw [A.mul_assoc]
      _ = A.mul (A.basis ws)
                (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
                       (A.smul (A.sc.b s) (A.basis 1))) := by
          rw [A.quadratic]
      _ = A.add (A.mul (A.basis ws) (A.smul (A.sc.a s) (A.basis (cs.simple s))))
               (A.mul (A.basis ws) (A.smul (A.sc.b s) (A.basis 1))) := by
          rw [A.mul_add_right]
      _ = A.add (A.smul (A.sc.a s) (A.mul (A.basis ws) (A.basis (cs.simple s))))
               (A.smul (A.sc.b s) (A.mul (A.basis ws) (A.basis 1))) := by
          rw [A.mul_smul_right, A.mul_smul_right]
      _ = A.add (A.smul (A.sc.a s) (A.basis w))
               (A.smul (A.sc.b s) (A.basis ws)) := by
          rw [h_Tws_Ts, A.identity_right]

/-- Data of an Iwahori–Hecke specialization: parameters $q_s$ for each simple
reflection $s$. -/
structure IwahoriHeckeData (B : Type*) (R : Type*) [CommRing R] where
  q : B → R

/-- Converts Iwahori–Hecke parameters $q_s$ into the generic structure constants
$(a_s, b_s) = (q_s - 1, q_s)$. -/
def IwahoriHeckeData.toStructureConstants (d : IwahoriHeckeData B R) :
    StructureConstants B R where
  a s := d.q s - 1
  b s := d.q s

end HeckeAlgebra
