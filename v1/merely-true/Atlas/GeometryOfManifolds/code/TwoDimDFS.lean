/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.DifferentialForms
import Atlas.GeometryOfManifolds.code.SymplecticManifolds

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

/-- Real polynomials in two variables $\mathbb{R}[x_0, x_1]$, used as the function ring
underlying the polynomial DFS on $\mathbb{R}^2$. -/
abbrev Poly2 := MvPolynomial (Fin 2) ℝ

/-- Polynomial $p$-forms on $\mathbb{R}^2$: scalars for $p = 0, 2$, pairs of polynomials for
$p = 1$ (the components of $f\, dx + g\, dy$), and trivial in degrees $\ge 3$. -/
@[reducible] def Symp2Ω : ℕ → Type
  | 0 => Poly2
  | 1 => Poly2 × Poly2
  | 2 => Poly2
  | _ + 3 => PUnit

/-- Polynomial vector fields on $\mathbb{R}^2$: pairs $(a, b)$ representing
$a\, \partial_x + b\, \partial_y$. -/
@[reducible] def Symp2VF : Type := Poly2 × Poly2


/-- Each degree of polynomial forms on $\mathbb{R}^2$ inherits an additive commutative group. -/
noncomputable instance symp2AddCommGroup : ∀ p, AddCommGroup (Symp2Ω p)
  | 0 => inferInstanceAs (AddCommGroup Poly2)
  | 1 => inferInstanceAs (AddCommGroup (Poly2 × Poly2))
  | 2 => inferInstanceAs (AddCommGroup Poly2)
  | _ + 3 => inferInstanceAs (AddCommGroup PUnit)

/-- Each degree of polynomial forms on $\mathbb{R}^2$ inherits an $\mathbb{R}$-module structure. -/
noncomputable instance symp2Module : ∀ p, Module ℝ (Symp2Ω p)
  | 0 => inferInstanceAs (Module ℝ Poly2)
  | 1 => inferInstanceAs (Module ℝ (Poly2 × Poly2))
  | 2 => inferInstanceAs (Module ℝ Poly2)
  | _ + 3 => inferInstanceAs (Module ℝ PUnit)


/-- Exterior derivative on polynomial forms on $\mathbb{R}^2$: $df = (\partial_x f, \partial_y f)$
on $0$-forms, $d(f\,dx + g\,dy) = \partial_x g - \partial_y f$ on $1$-forms, and $0$ in higher degree. -/
noncomputable def symp2d : ∀ {p : ℕ}, Symp2Ω p → Symp2Ω (p + 1)
  | 0, f => (MvPolynomial.pderiv (0 : Fin 2) f, MvPolynomial.pderiv (1 : Fin 2) f)
  | 1, (f, g) => MvPolynomial.pderiv (0 : Fin 2) g - MvPolynomial.pderiv (1 : Fin 2) f
  | 2, _ => PUnit.unit
  | _ + 3, _ => PUnit.unit

/-- Interior product $\iota_X$ on polynomial forms on $\mathbb{R}^2$ with $X = (a, b)$:
on $1$-forms $\iota_X(f, g) = af + bg$, on $2$-forms $\iota_X h = (-hb, ha)$, and $0$ in higher degree. -/
noncomputable def symp2Iota : Symp2VF → ∀ {p : ℕ}, Symp2Ω (p + 1) → Symp2Ω p
  | (a, b), 0, (f, g) => a * f + b * g
  | (a, b), 1, h => (-h * b, h * a)
  | _, 2, _ => (0 : Poly2)
  | _, (_ + 3), _ => PUnit.unit

/-- Scaling a polynomial $p$-form on $\mathbb{R}^2$ by a polynomial $0$-form, defined componentwise. -/
noncomputable def symp2fMul : ∀ {p : ℕ}, Symp2Ω 0 → Symp2Ω p → Symp2Ω p
  | 0, f, α => f * α
  | 1, f, (a, b) => (f * a, f * b)
  | 2, f, h => f * h
  | _ + 3, _, _ => PUnit.unit

/-- Wedge product of a polynomial $1$-form with a polynomial $p$-form on $\mathbb{R}^2$,
yielding a $(p+1)$-form; nontrivial only for $p = 0$ and $p = 1$. -/
noncomputable def symp2wedge1 : ∀ {p : ℕ}, Symp2Ω 1 → Symp2Ω p → Symp2Ω (p + 1)
  | 0, (f, g), α => (f * α, g * α)
  | 1, (f₁, g₁), (f₂, g₂) => f₁ * g₂ - g₁ * f₂
  | 2, _, _ => PUnit.unit
  | _ + 3, _, _ => PUnit.unit

/-- Lie derivative $\mathcal{L}_X$ on polynomial forms on $\mathbb{R}^2$, defined via Cartan's
magic formula $\mathcal{L}_X = d \circ \iota_X + \iota_X \circ d$. -/
noncomputable def symp2L : Symp2VF → ∀ {p : ℕ}, Symp2Ω p → Symp2Ω p
  | X, 0, f => symp2Iota X (symp2d f)
  | X, 1, α => symp2d (symp2Iota X α) + symp2Iota X (symp2d α)
  | X, 2, h => symp2d (symp2Iota X h) + symp2Iota X (symp2d h)
  | _, _ + 3, _ => PUnit.unit


/-- Commutativity of partial derivatives on $\mathbb{R}[x_0, x_1]$:
$\partial_i \partial_j f = \partial_j \partial_i f$. -/
lemma pderiv_comm_poly (i j : Fin 2) (f : Poly2) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp [MvPolynomial.pderiv_X, Derivation.leibniz]
    rw [hp]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Pi.single, Function.update] <;> ring


/-- Polynomial forms on $\mathbb{R}^2$ assemble into a `DifferentialFormSpace`, giving a
two-dimensional scaffolding (DFS) for the local model of a symplectic surface. -/
noncomputable instance symp2DFS : DifferentialFormSpace Symp2Ω Symp2VF where
  instAddCommGroup := symp2AddCommGroup
  instModule := symp2Module
  fMul := symp2fMul
  wedge1 := symp2wedge1
  d := symp2d
  ι := symp2Iota
  L := symp2L
  d_add := by
    intro p
    match p with
    | 0 => intro α β; simp [symp2d, map_add, Prod.mk_add_mk]
    | 1 => intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩; simp [symp2d, map_add]; ring
    | 2 => intro _ _; rfl
    | _ + 3 => intro _ _; rfl
  d_smul := by
    intro p
    match p with
    | 0 => intro r α; simp [symp2d, Derivation.map_smul, Prod.smul_mk]
    | 1 => intro r ⟨a, b⟩; simp [symp2d, Derivation.map_smul, smul_sub]
    | 2 => intro _ _; rfl
    | _ + 3 => intro _ _; rfl
  d_squared := by
    intro p
    match p with
    | 0 =>
      intro f
      show MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 f) -
           MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 f) = 0
      have : (MvPolynomial.pderiv (0 : Fin 2)) ((MvPolynomial.pderiv (1 : Fin 2)) f) =
             (MvPolynomial.pderiv (1 : Fin 2)) ((MvPolynomial.pderiv (0 : Fin 2)) f) := by
        induction f using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp [map_add, hp, hq]
        | mul_X p i hp =>
          simp [MvPolynomial.pderiv_X, Derivation.leibniz]
          rw [hp]
          fin_cases i <;> simp [Pi.single, Function.update] <;> ring
      rw [sub_eq_zero]; exact this
    | 1 => intro ⟨_, _⟩; exact Subsingleton.elim _ _
    | 2 => intro _; exact Subsingleton.elim _ _
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  d_fMul := by
    intro p
    match p with
    | 0 =>
      intro f α
      simp only [symp2d, symp2fMul, symp2wedge1]
      congr 1 <;> simp [Derivation.leibniz] <;> ring
    | 1 =>
      intro f ⟨a, b⟩
      simp only [symp2d, symp2fMul, symp2wedge1]
      simp [Derivation.leibniz]
      ring
    | 2 =>
      intro f α
      exact Subsingleton.elim _ _
    | _ + 3 =>
      intro f α
      exact Subsingleton.elim _ _
  fMul_add_left := by
    intro p
    match p with
    | 0 => intro f g α; simp [symp2fMul, add_mul]
    | 1 => intro f g ⟨a, b⟩; simp [symp2fMul, add_mul, Prod.mk_add_mk]
    | 2 => intro f g h; simp [symp2fMul, add_mul]
    | _ + 3 => intro _ _ _; rfl
  fMul_add_right := by
    intro p
    match p with
    | 0 => intro f α β; simp [symp2fMul, mul_add]
    | 1 => intro f ⟨a₁, b₁⟩ ⟨a₂, b₂⟩; simp [symp2fMul, mul_add, Prod.mk_add_mk]
    | 2 => intro f h₁ h₂; simp [symp2fMul, mul_add]
    | _ + 3 => intro _ _ _; rfl
  fMul_smul := by
    intro p
    match p with
    | 0 => intro r f α; simp [symp2fMul]
    | 1 => intro r f ⟨a, b⟩; simp [symp2fMul, Prod.smul_mk]
    | 2 => intro r f h; simp [symp2fMul]
    | _ + 3 => intro _ _ _; rfl
  wedge1_add_right := by
    intro p
    match p with
    | 0 => intro ⟨f, g⟩ α β; simp [symp2wedge1, mul_add, Prod.mk_add_mk]
    | 1 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ ⟨f₃, g₃⟩; simp [symp2wedge1, mul_add]; ring
    | 2 => intro _ _ _; rfl
    | _ + 3 => intro _ _ _; rfl
  wedge1_smul_right := by
    intro p
    match p with
    | 0 => intro ⟨f, g⟩ r α; simp [symp2wedge1, mul_comm, Algebra.mul_smul_comm, Prod.smul_mk]
    | 1 => intro ⟨f₁, g₁⟩ r ⟨f₂, g₂⟩; simp [symp2wedge1, Algebra.mul_smul_comm, smul_sub]
    | 2 => intro _ _ _; rfl
    | _ + 3 => intro _ _ _; rfl
  ι_add := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩; simp [symp2Iota, mul_add]; ring
    | 1 => intro h₁ h₂; simp [symp2Iota]; constructor <;> ring
    | 2 => intro _ _; simp [symp2Iota]
    | _ + 3 => intro _ _; rfl
  ι_smul := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro r ⟨f, g⟩; simp [symp2Iota]
    | 1 => intro r h; simp [symp2Iota]
    | 2 => intro r _; simp [symp2Iota]
    | _ + 3 => intro _ _; rfl
  ι_fMul := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro f ⟨g, h⟩; simp [symp2Iota, symp2fMul]; ring
    | 1 => intro f h; simp [symp2Iota, symp2fMul]; constructor <;> ring
    | 2 => intro f _; simp [symp2Iota, symp2fMul]
    | _ + 3 => intro _ _; rfl
  ι_wedge1 := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
           simp [symp2Iota, symp2fMul, symp2wedge1]
           constructor <;> ring
    | 1 => intro ⟨f₁, g₁⟩ h
           simp [symp2Iota, symp2fMul, symp2wedge1]
           ring
    | 2 => intro ⟨f₁, g₁⟩ _
           simp [symp2Iota, symp2fMul, symp2wedge1]
    | _ + 3 => intro _ _; rfl
  ι_squared := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro h; simp [symp2Iota]; ring
    | 1 => intro h; simp [symp2Iota]
    | 2 => intro _; simp [symp2Iota]
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  ι_ι_anticomm := by
    intro ⟨a, b⟩ ⟨c, d⟩ p
    match p with
    | 0 => intro h; simp [symp2Iota]; ring
    | 1 => intro h; simp [symp2Iota]
    | 2 => intro _; simp [symp2Iota]
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  L_add := by
    intro X p
    match p with
    | 0 =>
      intro α β
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add]
      ring
    | 1 =>
      intro ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add]
      apply Prod.ext <;> simp [Derivation.leibniz] <;> ring
    | 2 =>
      intro α β
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add, add_mul, neg_add]
      ring
    | _ + 3 => intro _ _; rfl
  L_smul := by
    intro X p
    match p with
    | 0 =>
      intro r α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, Derivation.map_smul, smul_add, Algebra.mul_smul_comm]
    | 1 =>
      intro r ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, Derivation.map_smul]
      apply Prod.ext <;> simp [Algebra.mul_smul_comm, smul_add, smul_sub, sub_mul]
    | 2 =>
      intro r α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, smul_mul_assoc, map_neg,
                 Derivation.map_smul, smul_neg, smul_sub, add_zero,
                 neg_mul]
    | _ + 3 => intro _ _; rfl
  L_zero_eq_ι_d := by
    intro X f; rfl
  L_comm_d := by
    intro X p
    match p with
    | 0 =>
      intro f
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota]
      apply Prod.ext <;> simp [sub_mul] <;> rw [pderiv_comm_poly 0 1 f] <;> ring
    | 1 =>
      intro ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      unfold symp2L symp2d symp2Iota
      simp only [add_zero]
      simp [Derivation.leibniz, map_add, map_sub, pderiv_comm_poly]
      ring
    | 2 =>
      intro α; exact Subsingleton.elim _ _
    | _ + 3 => intro _; rfl
  L_fMul := by
    intro X p
    match p with
    | 0 =>
      intro f α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul]
      simp [Derivation.leibniz]
      ring
    | 1 =>
      intro f ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul]
      apply Prod.ext <;> simp [Derivation.leibniz] <;> ring
    | 2 =>
      intro f α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul, add_zero]
      simp [Derivation.leibniz, map_neg]
      ring
    | _ + 3 => intro _ _; rfl
  ext_fdα := by
    intro p T hT_add hT_smul hT_gen
    match p with
    | 0 =>


      intro ⟨α₁, α₂⟩
      have hx : symp2fMul (p := 1) α₁ (symp2d (p := 0) (MvPolynomial.X 0)) = (α₁, 0) := by
        simp [symp2fMul, symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, mul_one, mul_zero]
      have hy : symp2fMul (p := 1) α₂ (symp2d (p := 0) (MvPolynomial.X 1)) = (0, α₂) := by
        simp [symp2fMul, symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, mul_one, mul_zero]
      have heq : (α₁, α₂) = symp2fMul (p := 1) α₁ (symp2d (p := 0) (MvPolynomial.X 0)) +
                             symp2fMul (p := 1) α₂ (symp2d (p := 0) (MvPolynomial.X 1)) := by
        rw [hx, hy]; simp [Prod.mk_add_mk]
      rw [heq, hT_add]
      simp [hT_gen]
    | 1 =>


      intro h
      have hgen : symp2d (p := 1) ((0 : Poly2), MvPolynomial.X (0 : Fin 2)) = (1 : Poly2) := by
        simp [symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, map_zero]
      have hmul : symp2fMul (p := 2) h (1 : Poly2) = h := by
        simp [symp2fMul, mul_one]
      have heq : h = symp2fMul (p := 2) h (symp2d (p := 1) ((0 : Poly2), MvPolynomial.X (0 : Fin 2))) := by
        rw [hgen, hmul]
      rw [heq]
      exact hT_gen h ((0 : Poly2), MvPolynomial.X (0 : Fin 2))
    | _ + 2 =>

      intro β
      exact Subsingleton.elim _ _


  ι_one_form_nondegenerate := by
    intro ⟨f, g⟩ h


    have h1 := h (1, 0)
    have h2 := h (0, 1)
    simp [symp2Iota] at h1 h2
    exact Prod.ext h1 h2


  ι_two_form_nondegenerate := by
    intro ω h


    have h1 := h (1, 0)
    simp [symp2Iota] at h1
    exact h1


/-- The standard symplectic structure on $\mathbb{R}^2$: the constant area form
$\omega = 1 \in \Omega^2$, which is closed and nondegenerate. -/
noncomputable def symp2Manifold : SymplecticManifold Symp2Ω Symp2VF where
  ω := (1 : Poly2)
  closed := by
    show symp2d (p := 2) (1 : Poly2) = (0 : Symp2Ω 3)
    rfl
  nondegenerate := by
    show Function.Injective (fun (X : Symp2VF) => symp2Iota X (p := 1) (1 : Poly2))
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp [symp2Iota] at h
    exact Prod.ext h.2 h.1


/-- Hodge star operator on polynomial forms on $\mathbb{R}^2$: $\star f = f$ on $0$- and $2$-forms,
and $\star(f\, dx + g\, dy) = -g\, dx + f\, dy$ on $1$-forms. -/
noncomputable def symp2HodgeStar : ∀ {p : ℕ}, Symp2Ω p → Symp2Ω p
  | 0, f => f
  | 1, (f, g) => (-g, f)
  | 2, h => h
  | _ + 3, x => x

end
