/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.DifferentialForms

set_option autoImplicit false

/-- Polynomial $p$-forms on $\mathbb{R}$: real polynomials in degrees $0$ and $1$, trivial otherwise. -/
@[reducible] def PolyΩ : ℕ → Type
  | 0 => Polynomial ℝ
  | 1 => Polynomial ℝ
  | _ + 2 => PUnit

/-- Polynomial vector fields on $\mathbb{R}$: a single polynomial coefficient $X(t) \partial_t$. -/
@[reducible] def PolyVF : Type := Polynomial ℝ

/-- Each degree of polynomial forms inherits an additive commutative group structure. -/
noncomputable instance polyΩ_acg : ∀ p, AddCommGroup (PolyΩ p)
  | 0 => inferInstanceAs (AddCommGroup (Polynomial ℝ))
  | 1 => inferInstanceAs (AddCommGroup (Polynomial ℝ))
  | _ + 2 => inferInstanceAs (AddCommGroup PUnit)

/-- Each degree of polynomial forms inherits an $\mathbb{R}$-module structure. -/
noncomputable instance polyΩ_mod : ∀ p, Module ℝ (PolyΩ p)
  | 0 => inferInstanceAs (Module ℝ (Polynomial ℝ))
  | 1 => inferInstanceAs (Module ℝ (Polynomial ℝ))
  | _ + 2 => inferInstanceAs (Module ℝ PUnit)

/-- Multiplication of a polynomial $0$-form (function) by a $p$-form: pointwise polynomial product. -/
noncomputable def polyFMul : {p : ℕ} → PolyΩ 0 → PolyΩ p → PolyΩ p
  | 0, f, α => f * α
  | 1, f, α => f * α
  | _ + 2, _, _ => PUnit.unit

/-- Wedge of a $1$-form with a $p$-form on $\mathbb{R}$: nontrivial only when $p = 0$. -/
noncomputable def polyWedge1 : {p : ℕ} → PolyΩ 1 → PolyΩ p → PolyΩ (p + 1)
  | 0, ω, α => ω * α
  | _ + 1, _, _ => PUnit.unit

/-- Exterior derivative on polynomial forms: $d f = f'\, dt$ for a $0$-form, zero in higher degree. -/
noncomputable def polyD : {p : ℕ} → PolyΩ p → PolyΩ (p + 1)
  | 0, f => Polynomial.derivative f
  | _ + 1, _ => PUnit.unit

/-- Interior product (contraction) $\iota_X$ of a vector field $X$ with a polynomial form. -/
noncomputable def polyIota (X : PolyVF) : {p : ℕ} → PolyΩ (p + 1) → PolyΩ p
  | 0, α => X * α
  | 1, _ => (0 : Polynomial ℝ)
  | _ + 2, _ => PUnit.unit

/-- Lie derivative $\mathcal{L}_X$ on polynomial forms, via Cartan's magic formula
$\mathcal{L}_X = d \circ \iota_X + \iota_X \circ d$. -/
noncomputable def polyLie (X : PolyVF) : {p : ℕ} → PolyΩ p → PolyΩ p
  | 0, f => X * Polynomial.derivative f
  | 1, g => Polynomial.derivative (X * g)
  | _ + 2, _ => PUnit.unit

/-- Formal antiderivative of a real polynomial: $\int (\sum a_n t^n)\, dt = \sum \tfrac{a_n}{n+1} t^{n+1}$. -/
noncomputable def polyAntideriv (g : Polynomial ℝ) : Polynomial ℝ :=
  g.sum (fun n a => Polynomial.monomial (n + 1) (a / (↑(n + 1) : ℝ)))

/-- Fundamental theorem of calculus for polynomials: $\frac{d}{dt} \int g(t)\, dt = g(t)$. -/
lemma derivative_antideriv (g : Polynomial ℝ) :
    Polynomial.derivative (polyAntideriv g) = g := by
  unfold polyAntideriv Polynomial.sum
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel]
  have key : ∀ n ∈ g.support,
      (Polynomial.monomial n) (g.coeff n / ↑(n + 1) * ↑(n + 1)) =
      (Polynomial.monomial n) (g.coeff n) := by
    intro n _; congr 1; field_simp
  rw [Finset.sum_congr rfl key]
  conv_rhs => rw [g.as_sum_support]

/-- Polynomial forms on $\mathbb{R}$ assemble into a `DifferentialFormSpace`, providing a
testbed scaffolding for de Rham cohomology in dimension $1$. -/
noncomputable instance polyDFS : DifferentialFormSpace PolyΩ PolyVF where
  instAddCommGroup := polyΩ_acg
  instModule := polyΩ_mod

  fMul := polyFMul
  wedge1 := polyWedge1
  d := polyD
  ι := fun X => polyIota X
  L := fun X => polyLie X


  d_add := by
    intro p α β
    match p with
    | 0 => exact Polynomial.derivative_add
    | _ + 1 => rfl


  d_smul := by
    intro p r α
    match p with
    | 0 => exact Polynomial.derivative_smul r α
    | _ + 1 => rfl


  d_squared := by
    intro p α
    match p with
    | 0 => rfl
    | _ + 1 => rfl


  d_fMul := by
    intro p f α
    match p with
    | 0 =>
      simp only [polyFMul, polyD, polyWedge1]
      exact Polynomial.derivative_mul
    | 1 => rfl
    | _ + 2 => rfl


  fMul_add_left := by
    intro p f g α
    match p with
    | 0 => simp only [polyFMul]; exact add_mul f g α
    | 1 => simp only [polyFMul]; exact add_mul f g α
    | _ + 2 => rfl


  fMul_add_right := by
    intro p f α β
    match p with
    | 0 => simp only [polyFMul]; exact mul_add f α β
    | 1 => simp only [polyFMul]; exact mul_add f α β
    | _ + 2 => rfl


  fMul_smul := by
    intro p r f α
    match p with
    | 0 => simp only [polyFMul]; exact smul_mul_assoc r f α
    | 1 => simp only [polyFMul]; exact smul_mul_assoc r f α
    | _ + 2 => rfl


  wedge1_add_right := by
    intro p ω α β
    match p with
    | 0 => simp only [polyWedge1]; exact mul_add ω α β
    | _ + 1 => rfl


  wedge1_smul_right := by
    intro p ω r α
    match p with
    | 0 => simp only [polyWedge1]; exact mul_smul_comm r ω α
    | _ + 1 => rfl


  ι_add := by
    intro X p α β
    match p with
    | 0 => simp only [polyIota]; exact mul_add X α β
    | 1 => simp only [polyIota]; ring
    | _ + 2 => rfl


  ι_smul := by
    intro X p r α
    match p with
    | 0 => simp only [polyIota]; exact mul_smul_comm r X α
    | 1 => simp only [polyIota]; simp [smul_zero]
    | _ + 2 => rfl


  ι_fMul := by
    intro X p f α
    match p with
    | 0 =>
      simp only [polyIota, polyFMul]
      ring
    | 1 =>
      simp only [polyIota, polyFMul]
      ring
    | _ + 2 => rfl


  ι_wedge1 := by
    intro X p ω α
    match p with
    | 0 =>
      simp only [polyIota, polyWedge1, polyFMul]
      ring
    | _ + 1 => rfl


  ι_squared := by
    intro X p α
    match p with
    | 0 =>
      simp only [polyIota]
      ring
    | 1 =>
      simp only [polyIota]
    | _ + 2 =>
      simp only [polyIota]


  ι_ι_anticomm := by
    intro X Y p α
    match p with
    | 0 =>
      simp only [polyIota]
      ring
    | 1 =>
      simp only [polyIota]
      simp [neg_zero]
    | _ + 2 =>
      simp only [polyIota]


  L_add := by
    intro X p α β
    match p with
    | 0 =>
      simp only [polyLie]
      rw [Polynomial.derivative_add, mul_add]
    | 1 =>
      simp only [polyLie]
      rw [mul_add, Polynomial.derivative_add]
    | _ + 2 => rfl


  L_smul := by
    intro X p r α
    match p with
    | 0 =>
      simp only [polyLie]
      rw [Polynomial.derivative_smul, mul_smul_comm]
    | 1 =>
      simp only [polyLie]
      rw [mul_smul_comm, Polynomial.derivative_smul]
    | _ + 2 => rfl


  L_zero_eq_ι_d := by
    intro X f
    simp only [polyLie, polyD, polyIota]


  L_comm_d := by
    intro X p α
    match p with
    | 0 =>
      simp only [polyLie, polyD]
    | _ + 1 => rfl


  L_fMul := by
    intro X p f α
    match p with
    | 0 =>
      simp only [polyLie, polyFMul]
      simp only [Polynomial.derivative_mul]; ring
    | 1 =>
      simp only [polyLie, polyFMul]
      simp only [Polynomial.derivative_mul]; ring
    | _ + 2 => rfl


  ext_fdα := by
    intro p T h_add h_smul h_gen
    match p with
    | 0 =>


      intro β
      have h1 : ∀ α : PolyΩ 0, T (polyFMul (1 : PolyΩ 0) (polyD α)) = 0 :=
        fun α => h_gen 1 α
      have h2 : ∀ α : PolyΩ 0, T (polyD α) = 0 := by
        intro α
        have := h1 α
        simp only [polyFMul, polyD] at this ⊢
        simpa using this
      rw [show β = Polynomial.derivative (polyAntideriv β) from (derivative_antideriv β).symm]
      exact h2 (polyAntideriv β)
    | _ + 1 =>

      intro β
      exact Subsingleton.elim _ _


  ι_one_form_nondegenerate := by
    intro α h


    have h1 := h (1 : PolyVF)
    simp only [polyIota] at h1
    simpa using h1


  ι_two_form_nondegenerate := by
    intro ω _
    exact Subsingleton.elim _ _

/-- The space of polynomial $0$-forms is nontrivial: $0 \ne 1$. -/
theorem polyOmega_zero_nontrivial : (0 : PolyΩ 0) ≠ (1 : PolyΩ 0) :=
  one_ne_zero.symm

/-- The space of polynomial $1$-forms is nontrivial: $0 \ne 1$. -/
theorem polyOmega_one_nontrivial : (0 : PolyΩ 1) ≠ (1 : PolyΩ 1) :=
  one_ne_zero.symm

/-- Nontriviality instance for polynomial $0$-forms. -/
instance : Nontrivial (PolyΩ 0) := ⟨⟨0, 1, polyOmega_zero_nontrivial⟩⟩

/-- Nontriviality instance for polynomial $1$-forms. -/
instance : Nontrivial (PolyΩ 1) := ⟨⟨0, 1, polyOmega_one_nontrivial⟩⟩
