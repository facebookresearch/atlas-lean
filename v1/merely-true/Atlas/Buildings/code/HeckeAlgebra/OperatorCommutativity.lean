/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Atlas.Buildings.code.CoxeterGroup.UnconditionalExchange
import Atlas.Buildings.code.HeckeAlgebra.Generic

open scoped Classical

namespace HeckeAlgebra

variable {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {R : Type*} [CommRing R]


/-- Left-multiplication operator $λ_s$ on the basis: $λ_s(T_w) = T_{sw}$ when
$\ell(sw) > \ell(w)$ and $λ_s(T_w) = a_s T_w + b_s T_{sw}$ otherwise. -/
noncomputable def lambdaOnBasis (cs : CoxeterSystem M M.Group)
    (a b : B → R) (s : B) (w : M.Group) : M.Group →₀ R :=
  if cs.length (cs.simple s * w) > cs.length w then
    Finsupp.single (cs.simple s * w) 1
  else
    Finsupp.single w (a s) + Finsupp.single (cs.simple s * w) (b s)

/-- Right-multiplication operator $ρ_t$ on the basis: $ρ_t(T_w) = T_{wt}$ when
$\ell(wt) > \ell(w)$ and $ρ_t(T_w) = a_t T_w + b_t T_{wt}$ otherwise. -/
noncomputable def rhoOnBasis (cs : CoxeterSystem M M.Group)
    (a b : B → R) (t : B) (w : M.Group) : M.Group →₀ R :=
  if cs.length (w * cs.simple t) > cs.length w then
    Finsupp.single (w * cs.simple t) 1
  else
    Finsupp.single w (a t) + Finsupp.single (w * cs.simple t) (b t)

/-- Linear extension of `lambdaOnBasis` to the free $R$-module $R[W]$. -/
noncomputable def lambdaLift (cs : CoxeterSystem M M.Group)
    (a b : B → R) (s : B) : (M.Group →₀ R) →ₗ[R] (M.Group →₀ R) :=
  Finsupp.linearCombination R (lambdaOnBasis cs a b s)

/-- Linear extension of `rhoOnBasis` to the free $R$-module $R[W]$. -/
noncomputable def rhoLift (cs : CoxeterSystem M M.Group)
    (a b : B → R) (t : B) : (M.Group →₀ R) →ₗ[R] (M.Group →₀ R) :=
  Finsupp.linearCombination R (rhoOnBasis cs a b t)


/-- Evaluation of `lambdaLift` on a single basis element: $λ_s(r · T_w) = r · λ_s(T_w)$. -/
theorem lambdaLift_single (cs : CoxeterSystem M M.Group) (a b : B → R) (s : B)
    (w : M.Group) (r : R) :
    lambdaLift cs a b s (Finsupp.single w r) = r • lambdaOnBasis cs a b s w := by
  simp [lambdaLift, Finsupp.linearCombination_single]

/-- Evaluation of `rhoLift` on a single basis element. -/
theorem rhoLift_single (cs : CoxeterSystem M M.Group) (a b : B → R) (t : B)
    (w : M.Group) (r : R) :
    rhoLift cs a b t (Finsupp.single w r) = r • rhoOnBasis cs a b t w := by
  simp [rhoLift, Finsupp.linearCombination_single]


/-- Coxeter-exchange consequence: if $\ell(swt) = \ell(w)$ and $\ell(sw) = \ell(wt)$,
then $swt = w$. -/
theorem swt_eq_w_of_length (cs : CoxeterSystem M M.Group)
    (s t : B) (w : M.Group)
    (h_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w)
    (h_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t)) :
    cs.simple s * w * cs.simple t = w := by
  have hex := CoxeterExchange.corollary_unconditional cs
  rcases cs.length_simple_mul w s with hsw_up | hsw_down
  · have hwt_up : cs.length (w * cs.simple t) = cs.length w + 1 := by omega
    rcases hex w s t hsw_up hwt_up with h_len | h_eq
    · omega
    · exact h_eq
  · have hs_sw_len : cs.length (cs.simple s * (cs.simple s * w)) =
        cs.length (cs.simple s * w) + 1 := by
      rw [cs.simple_mul_simple_cancel_left s]; omega
    have hswt_len : cs.length (cs.simple s * w * cs.simple t) =
        cs.length (cs.simple s * w) + 1 := by omega
    rcases hex (cs.simple s * w) s t hs_sw_len hswt_len with h_len | h_eq
    · rw [cs.simple_mul_simple_cancel_left s] at h_len; omega
    · rw [cs.simple_mul_simple_cancel_left s] at h_eq
      calc cs.simple s * w * cs.simple t
          = cs.simple s * (w * cs.simple t) := mul_assoc _ _ _
        _ = cs.simple s * (cs.simple s * w) := by rw [h_eq]
        _ = w := cs.simple_mul_simple_cancel_left s

/-- From $swt = w$ deduce $sw = wt$ by right-multiplying by $t$. -/
theorem sw_eq_wt_of_swt_eq_w (cs : CoxeterSystem M M.Group)
    (s t : B) (w : M.Group)
    (h : cs.simple s * w * cs.simple t = w) :
    cs.simple s * w = w * cs.simple t := by
  have h1 : cs.simple s * w * cs.simple t * cs.simple t = w * cs.simple t :=
    congr_arg (· * cs.simple t) h
  rwa [cs.simple_mul_simple_cancel_right] at h1


/-- Operator commutativity $λ_s ρ_t = ρ_t λ_s$ on basis elements (Section 6.1 step),
under the conjugacy-invariance assumption on the structure constants. -/
theorem lambda_rho_commute_on_basis
    (cs : CoxeterSystem M M.Group)
    (sc : StructureConstants B R)
    (hconj : sc.ConjugacyInvariant cs)
    (s t : B) (w : M.Group) :
    lambdaLift cs sc.a sc.b s (rhoOnBasis cs sc.a sc.b t w) =
    rhoLift cs sc.a sc.b t (lambdaOnBasis cs sc.a sc.b s w) := by


  have hassoc : cs.simple s * (w * cs.simple t) = cs.simple s * w * cs.simple t :=
    (mul_assoc _ _ _).symm
  have hassoc_len : cs.length (cs.simple s * (w * cs.simple t)) =
      cs.length (cs.simple s * w * cs.simple t) := congrArg cs.length hassoc

  rcases cs.length_simple_mul w s with hsw | hsw <;>
  rcases cs.length_mul_simple w t with hwt | hwt
  ·
    have h4 : cs.length (w * cs.simple t) > cs.length w := by omega
    have h3 : cs.length (cs.simple s * w) > cs.length w := by omega
    rcases cs.length_mul_simple (cs.simple s * w) t with hswt_up | hswt_down
    ·
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w) := by omega


      simp only [rhoOnBasis, if_pos h4, lambdaLift,
        Finsupp.linearCombination_single, one_smul,
        lambdaOnBasis, if_pos h1, if_pos h3,
        rhoLift, if_pos h2]
      rw [hassoc]
    ·
      have h_len_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w := by omega
      have h_len_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t) := by omega
      have hswt_w := swt_eq_w_of_length cs s t w h_len_swt h_len_sw_wt
      have hsw_wt := sw_eq_wt_of_swt_eq_w cs s t w hswt_w
      have conj : w * cs.simple t * w⁻¹ = cs.simple s := by
        calc w * cs.simple t * w⁻¹
            = cs.simple s * w * w⁻¹ := by rw [← hsw_wt]
          _ = cs.simple s := by group
      have hst := hconj t s w conj
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w)) := by omega


      simp only [rhoOnBasis, if_pos h4, lambdaLift,
        Finsupp.linearCombination_single, one_smul,
        lambdaOnBasis, if_neg h1n, if_pos h3,
        rhoLift, if_neg h2n]
      rw [hassoc, hswt_w, ← hsw_wt, hst.1, hst.2]
  ·
    have h3 : cs.length (cs.simple s * w) > cs.length w := by omega
    have h4n : ¬(cs.length (w * cs.simple t) > cs.length w) := by omega
    rcases cs.length_mul_simple (cs.simple s * w) t with hswt_up | hswt_down
    ·
      exfalso
      rcases cs.length_simple_mul (w * cs.simple t) s with h1 | h1
      · rw [hassoc_len] at h1; omega
      · rw [hassoc_len] at h1; omega
    ·
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w)) := by omega


      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]


      rw [show lambdaOnBasis cs sc.a sc.b s w = Finsupp.single (cs.simple s * w) 1
        from by simp only [lambdaOnBasis, if_pos h3]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (cs.simple s * (w * cs.simple t)) 1
        from by simp only [lambdaOnBasis, if_pos h1]]


      rw [rhoLift_single, one_smul]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w) (sc.a t) +
        Finsupp.single (cs.simple s * w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h2n]]
      simp only [Finsupp.smul_single', mul_one]
      rw [hassoc]
  ·
    have h3n : ¬(cs.length (cs.simple s * w) > cs.length w) := by omega
    have h4 : cs.length (w * cs.simple t) > cs.length w := by omega
    rcases cs.length_simple_mul (w * cs.simple t) s with hswt_up | hswt_down
    ·
      exfalso


      have hswt_up' : cs.length (cs.simple s * w * cs.simple t) =
          cs.length (w * cs.simple t) + 1 := by rw [← hassoc_len]; exact hswt_up
      rcases cs.length_mul_simple (cs.simple s * w) t with h1 | h1
      ·


        omega
      ·

        omega
    ·
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w) := by omega


      rw [show rhoOnBasis cs sc.a sc.b t w = Finsupp.single (w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h4]]
      rw [lambdaLift_single, one_smul]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (w * cs.simple t) (sc.a s) +
        Finsupp.single (cs.simple s * (w * cs.simple t)) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h1n]]


      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w = Finsupp.single (w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h4]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h2]]
      simp only [Finsupp.smul_single', mul_one]
      rw [hassoc]
  ·
    have h3n : ¬(cs.length (cs.simple s * w) > cs.length w) := by omega
    have h4n : ¬(cs.length (w * cs.simple t) > cs.length w) := by omega
    rcases cs.length_mul_simple (cs.simple s * w) t with hswt_up | hswt_down
    ·
      have h_len_swt : cs.length (cs.simple s * w * cs.simple t) = cs.length w := by omega
      have h_len_sw_wt : cs.length (cs.simple s * w) = cs.length (w * cs.simple t) := by omega
      have hswt_w := swt_eq_w_of_length cs s t w h_len_swt h_len_sw_wt
      have hsw_wt := sw_eq_wt_of_swt_eq_w cs s t w hswt_w
      have conj : w * cs.simple t * w⁻¹ = cs.simple s := by
        calc w * cs.simple t * w⁻¹
            = cs.simple s * w * w⁻¹ := by rw [← hsw_wt]
          _ = cs.simple s := by group
      have hst := hconj t s w conj
      have h1 : cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t) := by rw [hassoc_len]; omega
      have h2 : cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w) := by omega


      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]


      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (cs.simple s * (w * cs.simple t)) 1
        from by simp only [lambdaOnBasis, if_pos h1]]


      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w * cs.simple t) 1
        from by simp only [rhoOnBasis, if_pos h2]]

      rw [hassoc, hswt_w, ← hsw_wt, hst.1, hst.2]

    ·
      have h1n : ¬(cs.length (cs.simple s * (w * cs.simple t)) >
          cs.length (w * cs.simple t)) := by rw [hassoc_len]; omega
      have h2n : ¬(cs.length (cs.simple s * w * cs.simple t) >
          cs.length (cs.simple s * w)) := by omega


      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show lambdaLift cs sc.a sc.b s
        (Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)) =
        lambdaLift cs sc.a sc.b s (Finsupp.single w (sc.a t)) +
        lambdaLift cs sc.a sc.b s (Finsupp.single (w * cs.simple t) (sc.b t))
        from map_add _ _ _]
      rw [lambdaLift_single, lambdaLift_single]

      rw [show lambdaOnBasis cs sc.a sc.b s w =
        Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h3n]]
      rw [show lambdaOnBasis cs sc.a sc.b s (w * cs.simple t) =
        Finsupp.single (w * cs.simple t) (sc.a s) +
        Finsupp.single (cs.simple s * (w * cs.simple t)) (sc.b s)
        from by simp only [lambdaOnBasis, if_neg h1n]]

      rw [show rhoLift cs sc.a sc.b t
        (Finsupp.single w (sc.a s) + Finsupp.single (cs.simple s * w) (sc.b s)) =
        rhoLift cs sc.a sc.b t (Finsupp.single w (sc.a s)) +
        rhoLift cs sc.a sc.b t (Finsupp.single (cs.simple s * w) (sc.b s))
        from map_add _ _ _]
      rw [rhoLift_single, rhoLift_single]
      rw [show rhoOnBasis cs sc.a sc.b t w =
        Finsupp.single w (sc.a t) + Finsupp.single (w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h4n]]
      rw [show rhoOnBasis cs sc.a sc.b t (cs.simple s * w) =
        Finsupp.single (cs.simple s * w) (sc.a t) +
        Finsupp.single (cs.simple s * w * cs.simple t) (sc.b t)
        from by simp only [rhoOnBasis, if_neg h2n]]

      rw [hassoc]
      simp only [Finsupp.smul_single', smul_add]
      ring_nf
      abel


section GoalEighteen

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- Data of a candidate Hecke-algebra structure on a free $R$-module, packaging both
left and right length-up/length-down rules together with module operations,
two-sided generator associativity, and conjugacy invariance of $(a_s, b_s)$. -/
structure FreeModuleHeckeData (M : CoxeterMatrix B') (R : Type*) [CommRing R] where
  carrier : Type*
  basis : M.Group → carrier
  smul : R → carrier → carrier
  mul : carrier → carrier → carrier
  add : carrier → carrier → carrier
  a : B' → R
  b : B' → R
  left_length_up : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) > M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) = basis (M.toCoxeterSystem.simple s * w)
  left_length_down : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) < M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      add (smul (a s) (basis w)) (smul (b s) (basis (M.toCoxeterSystem.simple s * w)))
  right_length_up : ∀ (t : B') (w : M.Group),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple t) > M.toCoxeterSystem.length w →
    mul (basis w) (basis (M.toCoxeterSystem.simple t)) = basis (w * M.toCoxeterSystem.simple t)
  right_length_down : ∀ (t : B') (w : M.Group),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple t) < M.toCoxeterSystem.length w →
    mul (basis w) (basis (M.toCoxeterSystem.simple t)) =
      add (smul (a t) (basis w)) (smul (b t) (basis (w * M.toCoxeterSystem.simple t)))
  identity_left : ∀ (x : carrier), mul (basis 1) x = x
  identity_right : ∀ (x : carrier), mul x (basis 1) = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  add_comm : ∀ x y, add x y = add y x
  add_assoc' : ∀ x y z, add (add x y) z = add x (add y z)
  smul_add : ∀ (r : R) x y, smul r (add x y) = add (smul r x) (smul r y)
  smul_smul : ∀ (r₁ r₂ : R) x, smul r₁ (smul r₂ x) = smul (r₁ * r₂) x
  basis_span : ∀ (P : carrier → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z
  conj_inv : ∀ (s₁ s₂ : B') (w : M.Group),
    w * M.toCoxeterSystem.simple s₁ * w⁻¹ = M.toCoxeterSystem.simple s₂ →
    a s₁ = a s₂ ∧ b s₁ = b s₂
  gen_left_assoc : ∀ (s : B') (x y : carrier),
    mul (basis (M.toCoxeterSystem.simple s)) (mul x y) =
      mul (mul (basis (M.toCoxeterSystem.simple s)) x) y
  gen_right_assoc : ∀ (t : B') (x y : carrier),
    mul (mul x y) (basis (M.toCoxeterSystem.simple t)) =
      mul x (mul y (basis (M.toCoxeterSystem.simple t)))

/-- Converts a `FreeModuleHeckeData` into a `GenericAlgebra`: the quadratic relation
is derived from the left length-down rule applied at $w = s$. -/
def FreeModuleHeckeData.toGenericAlgebra (D : FreeModuleHeckeData M' R') :
    GenericAlgebra M' R' where
  carrier := D.carrier
  basis := D.basis
  smul := D.smul
  mul := D.mul
  add := D.add
  sc := ⟨D.a, D.b⟩
  length_up := D.left_length_up
  quadratic := by
    intro _cs s
    have h : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * M'.toCoxeterSystem.simple s) <
        M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s) := by
      rw [M'.toCoxeterSystem.simple_mul_simple_self s,
          M'.toCoxeterSystem.length_one, M'.toCoxeterSystem.length_simple]
      omega
    have key := D.left_length_down s (M'.toCoxeterSystem.simple s) h
    rw [M'.toCoxeterSystem.simple_mul_simple_self s] at key
    exact key
  identity_left := D.identity_left
  identity_right := D.identity_right
  mul_add_right := D.mul_add_right
  mul_add_left := D.mul_add_left
  mul_smul_right := D.mul_smul_right
  smul_mul_left := D.smul_mul_left
  gen_left_assoc := D.gen_left_assoc
  gen_right_assoc := D.gen_right_assoc
  basis_span := D.basis_span

end GoalEighteen


section GoalTwentyTwo

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- A word $s :: \mathit{rest}$ is reduced iff `rest` is reduced and prepending $s$ increases
the length by exactly one. -/
theorem isReduced_cons_iff (s : B') (rest : List B') :
    M'.toCoxeterSystem.IsReduced (s :: rest) ↔
    M'.toCoxeterSystem.IsReduced rest ∧
    M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * M'.toCoxeterSystem.wordProd rest) =
      M'.toCoxeterSystem.length (M'.toCoxeterSystem.wordProd rest) + 1 := by
  unfold CoxeterSystem.IsReduced
  simp only [M'.toCoxeterSystem.wordProd_cons, List.length_cons]
  constructor
  · intro h
    have hle := M'.toCoxeterSystem.length_wordProd_le rest
    rcases M'.toCoxeterSystem.length_simple_mul (M'.toCoxeterSystem.wordProd rest) s with h1 | h1
    · exact ⟨by omega, h1⟩
    · exact ⟨by omega, by omega⟩
  · intro ⟨_, hup⟩; omega

/-- Generator left-associativity for repeated foldl multiplication over a list of simple
generators: left-multiplying the accumulator by $T_s$ commutes with the fold. -/
theorem GenericAlgebra.foldl_gen_left' (A : GenericAlgebra M' R') (s : B')
    (init : A.carrier) (rest : List B') :
    A.mul (A.basis (M'.toCoxeterSystem.simple s))
      (List.foldl (fun acc u => A.mul acc (A.basis (M'.toCoxeterSystem.simple u))) init rest) =
    List.foldl (fun acc u => A.mul acc (A.basis (M'.toCoxeterSystem.simple u)))
      (A.mul (A.basis (M'.toCoxeterSystem.simple s)) init) rest := by
  induction rest generalizing init with
  | nil => simp
  | cons u rest' ih =>
    simp only [List.foldl_cons]
    rw [ih (A.mul init (A.basis (M'.toCoxeterSystem.simple u)))]
    congr 1
    exact A.gen_left_assoc s init (A.basis (M'.toCoxeterSystem.simple u))

end GoalTwentyTwo


section GoalEighteenUniqueness

variable {B' : Type*} {M' : CoxeterMatrix B'} {R' : Type*} [CommRing R']

/-- Any alternative multiplication `mul₂` on the same carrier satisfying the length-up,
quadratic, identity, distributivity, scalar, and left-associativity axioms automatically
satisfies the length-down rule of $A$. -/
theorem mul_alt_length_down (A : GenericAlgebra M' R')
    (mul₂ : A.carrier → A.carrier → A.carrier)
    (h_length_up : ∀ (s : B') (w : M'.Group),
      M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
        M'.toCoxeterSystem.length w →
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) =
        A.basis (M'.toCoxeterSystem.simple s * w))
    (h_quadratic : ∀ (s : B'),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s))
           (A.basis (M'.toCoxeterSystem.simple s)) =
        A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s)))
              (A.smul (A.sc.b s) (A.basis 1)))
    (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
    (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
    (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
    (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) =
        mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) :
    let cs := M'.toCoxeterSystem
    ∀ (s : B') (w : M'.Group),
      cs.length (cs.simple s * w) < cs.length w →
      mul₂ (A.basis (cs.simple s)) (A.basis w) =
        A.add (A.smul (A.sc.a s) (A.basis w))
              (A.smul (A.sc.b s) (A.basis (cs.simple s * w))) := by
  intro cs s w hlength
  set sw := cs.simple s * w
  have hw : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
  have hlength_up_sw : cs.length (cs.simple s * sw) > cs.length sw := by
    rw [hw]; exact hlength
  have h_Ts_Tsw : mul₂ (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
    rw [h_length_up s sw hlength_up_sw, hw]
  calc mul₂ (A.basis (cs.simple s)) (A.basis w)
      = mul₂ (A.basis (cs.simple s))
              (mul₂ (A.basis (cs.simple s)) (A.basis sw)) := by
          rw [h_Ts_Tsw]
      _ = mul₂ (mul₂ (A.basis (cs.simple s)) (A.basis (cs.simple s)))
                (A.basis sw) := by
          rw [h_gen_left_assoc]
      _ = mul₂ (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
                       (A.smul (A.sc.b s) (A.basis 1)))
                (A.basis sw) := by
          rw [h_quadratic]
      _ = A.add (mul₂ (A.smul (A.sc.a s) (A.basis (cs.simple s))) (A.basis sw))
               (mul₂ (A.smul (A.sc.b s) (A.basis 1)) (A.basis sw)) := by
          rw [h_mul_add_left]
      _ = A.add (A.smul (A.sc.a s) (mul₂ (A.basis (cs.simple s)) (A.basis sw)))
               (A.smul (A.sc.b s) (mul₂ (A.basis 1) (A.basis sw))) := by
          rw [h_smul_mul_left, h_smul_mul_left]
      _ = A.add (A.smul (A.sc.a s) (A.basis w))
               (A.smul (A.sc.b s) (A.basis sw)) := by
          rw [h_Ts_Tsw, h_identity_left]

/-- An alternative multiplication agrees with $A.\mathrm{mul}$ on products $T_s · y$ for any $y$,
under the standard axiom set on `mul₂`. -/
theorem mul_alt_gen_eq (A : GenericAlgebra M' R')
    (mul₂ : A.carrier → A.carrier → A.carrier)
    (h_length_up : ∀ (s : B') (w : M'.Group),
      M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
        M'.toCoxeterSystem.length w →
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) =
        A.basis (M'.toCoxeterSystem.simple s * w))
    (h_quadratic : ∀ (s : B'),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s))
           (A.basis (M'.toCoxeterSystem.simple s)) =
        A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s)))
              (A.smul (A.sc.b s) (A.basis 1)))
    (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
    (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
    (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
    (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
    (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
    (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) =
        mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y)
    (s : B') :
    ∀ y, mul₂ (A.basis (M'.toCoxeterSystem.simple s)) y =
         A.mul (A.basis (M'.toCoxeterSystem.simple s)) y := by
  apply A.basis_span (fun y =>
    mul₂ (A.basis (M'.toCoxeterSystem.simple s)) y =
    A.mul (A.basis (M'.toCoxeterSystem.simple s)) y)
  ·
    intro w
    rcases M'.toCoxeterSystem.length_simple_mul w s with h_up | h_down
    ·
      rw [h_length_up s w (by omega), A.length_up s w (by omega)]
    ·
      rw [mul_alt_length_down A mul₂ h_length_up h_quadratic h_identity_left
            h_mul_add_left h_smul_mul_left h_gen_left_assoc s w (by omega),
          A.SatisfiesLengthDownRule s w (by omega)]
  ·
    intro y₁ y₂ hy₁ hy₂
    rw [h_mul_add_right, hy₁, hy₂, A.mul_add_right]
  ·
    intro r y hy
    rw [h_mul_smul_right, hy, A.mul_smul_right]

/-- An alternative multiplication agrees with $A.\mathrm{mul}$ on $T_w · y$ for every $w$ and $y$,
by induction on $\ell(w)$. -/
theorem mul_alt_basis_left_eq (A : GenericAlgebra M' R')
    (mul₂ : A.carrier → A.carrier → A.carrier)
    (h_length_up : ∀ (s : B') (w : M'.Group),
      M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
        M'.toCoxeterSystem.length w →
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) =
        A.basis (M'.toCoxeterSystem.simple s * w))
    (h_quadratic : ∀ (s : B'),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s))
           (A.basis (M'.toCoxeterSystem.simple s)) =
        A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s)))
              (A.smul (A.sc.b s) (A.basis 1)))
    (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
    (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
    (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
    (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
    (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
    (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) =
        mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y) :
    ∀ (w : M'.Group) (y : A.carrier),
      mul₂ (A.basis w) y = A.mul (A.basis w) y := by
  set cs := M'.toCoxeterSystem

  suffices ∀ (n : ℕ) (w : M'.Group), cs.length w ≤ n →
      ∀ y, mul₂ (A.basis w) y = A.mul (A.basis w) y by
    intro w y; exact this (cs.length w) w le_rfl y
  intro n
  induction n with
  | zero =>
    intro w hw y
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    rw [h_identity_left, A.identity_left]
  | succ n ih =>
    intro w hw y
    by_cases hw1 : w = 1
    · subst hw1; rw [h_identity_left, A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt

      have h_mul2_TsTsw : mul₂ (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [h_length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]

      have h_mul_TsTsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      calc mul₂ (A.basis w) y
          = mul₂ (mul₂ (A.basis (cs.simple s)) (A.basis sw)) y := by
              rw [h_mul2_TsTsw]
          _ = mul₂ (A.basis (cs.simple s)) (mul₂ (A.basis sw) y) := by
              rw [← h_gen_left_assoc]
          _ = mul₂ (A.basis (cs.simple s)) (A.mul (A.basis sw) y) := by
              rw [ih sw (by omega) y]
          _ = A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) y) := by
              rw [mul_alt_gen_eq A mul₂ h_length_up h_quadratic h_identity_left
                    h_mul_add_right h_mul_add_left h_mul_smul_right h_smul_mul_left
                    h_gen_left_assoc s]
          _ = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) y := by
              rw [A.gen_left_assoc]
          _ = A.mul (A.basis w) y := by
              rw [h_mul_TsTsw]

/-- Uniqueness of the generic Hecke multiplication: any alternative product `mul₂`
on $A$'s carrier satisfying the same axioms must equal $A.\mathrm{mul}$ on all inputs. -/
theorem generic_algebra_unique (A : GenericAlgebra M' R')
    (mul₂ : A.carrier → A.carrier → A.carrier)
    (h_length_up : ∀ (s : B') (w : M'.Group),
      M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
        M'.toCoxeterSystem.length w →
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (A.basis w) =
        A.basis (M'.toCoxeterSystem.simple s * w))
    (h_quadratic : ∀ (s : B'),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s))
           (A.basis (M'.toCoxeterSystem.simple s)) =
        A.add (A.smul (A.sc.a s) (A.basis (M'.toCoxeterSystem.simple s)))
              (A.smul (A.sc.b s) (A.basis 1)))
    (h_identity_left : ∀ x, mul₂ (A.basis 1) x = x)
    (h_identity_right : ∀ x, mul₂ x (A.basis 1) = x)
    (h_mul_add_right : ∀ x y z, mul₂ x (A.add y z) = A.add (mul₂ x y) (mul₂ x z))
    (h_mul_add_left : ∀ x y z, mul₂ (A.add x y) z = A.add (mul₂ x z) (mul₂ y z))
    (h_mul_smul_right : ∀ (r : R') x y, mul₂ x (A.smul r y) = A.smul r (mul₂ x y))
    (h_smul_mul_left : ∀ (r : R') x y, mul₂ (A.smul r x) y = A.smul r (mul₂ x y))
    (h_gen_left_assoc : ∀ (s : B') (x y : A.carrier),
      mul₂ (A.basis (M'.toCoxeterSystem.simple s)) (mul₂ x y) =
        mul₂ (mul₂ (A.basis (M'.toCoxeterSystem.simple s)) x) y)
    (h_gen_right_assoc : ∀ (t : B') (x y : A.carrier),
      mul₂ (mul₂ x y) (A.basis (M'.toCoxeterSystem.simple t)) =
        mul₂ x (mul₂ y (A.basis (M'.toCoxeterSystem.simple t)))) :
    ∀ x y, mul₂ x y = A.mul x y := by

  have h_basis_left : ∀ (w : M'.Group) (y : A.carrier),
      mul₂ (A.basis w) y = A.mul (A.basis w) y :=
    mul_alt_basis_left_eq A mul₂ h_length_up h_quadratic h_identity_left
      h_mul_add_right h_mul_add_left h_mul_smul_right h_smul_mul_left
      h_gen_left_assoc

  intro x
  apply A.basis_span (fun x => ∀ y, mul₂ x y = A.mul x y)
  ·
    exact h_basis_left
  ·
    intro x₁ x₂ hx₁ hx₂ y
    rw [h_mul_add_left, hx₁, hx₂, A.mul_add_left]
  ·
    intro r x hx y
    rw [h_smul_mul_left, hx, A.smul_mul_left]

end GoalEighteenUniqueness

end HeckeAlgebra
