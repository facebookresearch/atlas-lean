/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineIsometry.LatticeChains

set_option linter.unusedSectionVars false

open AffineIsometryBuilding DVRContext

/-- An anisotropic symmetric bilinear form context: a symmetric bilinear form
$\langle \cdot, \cdot \rangle$ over $k$ that is anisotropic (no nonzero
isotropic vectors), together with the ambient DVR data, Hensel-style
solvability of quadratic equations, and closure properties of the integral
self-pairings. Used to construct the maximal lattice on which the form is
integral. -/
structure AnisotropicFormContext where
  C : DVRContext
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  form_symm : ∀ v w : Fin C.n → C.k, form v w = form w v
  form_add_left : ∀ v₁ v₂ w : Fin C.n → C.k,
    form (v₁ + v₂) w = form v₁ w + form v₂ w
  form_smul_left : ∀ (c : C.k) (v w : Fin C.n → C.k),
    form (c • v) w = c * form v w
  anisotropic : ∀ v : Fin C.n → C.k, form v v = 0 → v = 0
  two_is_unit : C.isUnitInO (C.embed (1 + 1 : C.𝔬))
  hensel : ∀ (b c : C.k),
    C.isUnitInO b → C.isInMaxIdeal c →
    ∃ α : C.k, α * α + b * α + c = 0


  isInO_zero : C.isInO (0 : C.k)
  isInO_add : ∀ {x y : C.k}, C.isInO x → C.isInO y → C.isInO (x + y)
  isInO_mul : ∀ {x y : C.k}, C.isInO x → C.isInO y → C.isInO (x * y)
  isInO_neg : ∀ {x : C.k}, C.isInO x → C.isInO (-x)
  isUnitInO_inv : ∀ {x : C.k}, C.isUnitInO x → C.isInO x⁻¹
  isInO_embed : ∀ r : C.𝔬, C.isInO (C.embed r)


  selfpair_add_closed : ∀ v w : Fin C.n → C.k,
    C.isInO (form v v) → C.isInO (form w w) → C.isInO (form (v + w) (v + w))


  spans_data : ∀ v : Fin C.n → C.k,
    ∃ (m : ℕ) (cs : Fin m → C.k) (vs : Fin m → Fin C.n → C.k),
      (∀ j, C.isInO (form (vs j) (vs j))) ∧ v = ∑ j, cs j • vs j

namespace AnisotropicFormContext

variable (ctx : AnisotropicFormContext)

/-- The image of $2 = 1 + 1$ under the embedding $\mathfrak{o} \hookrightarrow k$
is nonzero, since $2$ is a unit. -/
lemma embed_two_ne_zero : ctx.C.embed (1 + 1 : ctx.C.𝔬) ≠ 0 := by
  intro h0
  obtain ⟨r, hr_unit, hr_eq⟩ := ctx.two_is_unit
  have : r = 0 := ctx.C.embed_injective (by rw [hr_eq, h0, map_zero])
  subst this; exact not_isUnit_zero hr_unit

/-- The form vanishes on the zero vector in the left slot. -/
lemma form_zero_left (w : Fin ctx.C.n → ctx.C.k) : ctx.form 0 w = 0 := by
  have h := ctx.form_smul_left (0 : ctx.C.k) (0 : Fin ctx.C.n → ctx.C.k) w
  simp [zero_mul] at h
  exact h

/-- The form vanishes on the zero vector in the right slot. -/
lemma form_zero_right (v : Fin ctx.C.n → ctx.C.k) : ctx.form v 0 = 0 := by
  rw [ctx.form_symm]; exact ctx.form_zero_left v

/-- The form value $\langle 0, 0 \rangle = 0$ is integral. -/
lemma form_zero_isInO : ctx.C.isInO (ctx.form (0 : Fin ctx.C.n → ctx.C.k) (0 : Fin ctx.C.n → ctx.C.k)) := by
  rw [ctx.form_zero_left]; exact ctx.isInO_zero

/-- The difference of integral elements is integral. -/
lemma isInO_sub {x y : ctx.C.k} (hx : ctx.C.isInO x) (hy : ctx.C.isInO y) :
    ctx.C.isInO (x - y) := by
  rw [sub_eq_add_neg]; exact ctx.isInO_add hx (ctx.isInO_neg hy)

/-- Bilinearity of the form on the right slot. -/
lemma form_add_right (v w₁ w₂ : Fin ctx.C.n → ctx.C.k) :
    ctx.form v (w₁ + w₂) = ctx.form v w₁ + ctx.form v w₂ := by
  rw [ctx.form_symm v (w₁ + w₂), ctx.form_add_left, ctx.form_symm w₁ v, ctx.form_symm w₂ v]

/-- The form is $k$-linear in the right slot. -/
lemma form_smul_right (c : ctx.C.k) (v w : Fin ctx.C.n → ctx.C.k) :
    ctx.form v (c • w) = c * ctx.form v w := by
  rw [ctx.form_symm v (c • w), ctx.form_smul_left, ctx.form_symm w v]

/-- Scaling preserves integrality of the self-pairing
$\langle cv, cv \rangle = c^2 \langle v, v \rangle$. -/
lemma smul_selfpair_isInO (c : ctx.C.k) (v : Fin ctx.C.n → ctx.C.k)
    (hc : ctx.C.isInO c) (hv : ctx.C.isInO (ctx.form v v)) :
    ctx.C.isInO (ctx.form (c • v) (c • v)) := by
  rw [ctx.form_smul_left, ctx.form_smul_right]
  exact ctx.isInO_mul hc (ctx.isInO_mul hc hv)

/-- Integral $\mathfrak{o}$-linear combinations of vectors with integral
self-pairings have integral self-pairing. -/
lemma closed_under_o_combination_data
    (coeffs : Fin ctx.C.n → ctx.C.k) (vectors : Fin ctx.C.n → (Fin ctx.C.n → ctx.C.k))
    (hcoeffs : ∀ i, ctx.C.isInO (coeffs i))
    (hvecs : ∀ i, ctx.C.isInO (ctx.form (vectors i) (vectors i))) :
    ctx.C.isInO (ctx.form (∑ i, coeffs i • vectors i) (∑ i, coeffs i • vectors i)) := by
  have : ∀ (s : Finset (Fin ctx.C.n)),
      ctx.C.isInO (ctx.form (∑ i ∈ s, coeffs i • vectors i)
        (∑ i ∈ s, coeffs i • vectors i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ctx.form_zero_isInO
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact ctx.selfpair_add_closed _ _
        (ctx.smul_selfpair_isInO _ _ (hcoeffs _) (hvecs _)) ih
  exact this Finset.univ

/-- The maximal lattice of an anisotropic form: the $\mathfrak{o}$-lattice
$\{v : \langle v, v \rangle \in \mathfrak{o}\}$ of vectors with integral
self-pairing. -/
def maxLat : OLattice ctx.C where
  carrier := {v | ctx.C.isInO (ctx.form v v)}
  zero_mem := ctx.form_zero_isInO
  add_mem := fun hx hy => ctx.selfpair_add_closed _ _ hx hy
  smul_mem := by
    intro r x hx
    show ctx.C.isInO (ctx.form (ctx.C.oscal r x) (ctx.C.oscal r x))

    have oscal_eq : ctx.C.oscal r x = ctx.C.embed r • x := by
      ext i; simp [DVRContext.oscal, Pi.smul_apply, smul_eq_mul]
    rw [oscal_eq, ctx.form_smul_left, ctx.form_smul_right]

    exact ctx.isInO_mul (ctx.isInO_embed r) (ctx.isInO_mul (ctx.isInO_embed r) hx)
  spans_V := ctx.spans_data
  closed_under_o_combination := by
    intro coeffs vectors hcoeffs hvecs
    exact ctx.closed_under_o_combination_data coeffs vectors hcoeffs
      (fun i => hvecs i)

/-- Completeness of `maxLat`: every vector with integral self-pairing is in it. -/
lemma maxLat_complete : ∀ v : Fin ctx.C.n → ctx.C.k,
    ctx.C.isInO (ctx.form v v) → v ∈ ctx.maxLat.carrier :=
  fun _v hv => hv

/-- The form is integral on the maximal lattice: $\langle v, w \rangle \in
\mathfrak{o}$ for all $v, w$ with integral self-pairings, by the polarisation
identity and the fact that $2$ is a unit. -/
lemma maxLat_integral : ∀ v ∈ ctx.maxLat.carrier, ∀ w ∈ ctx.maxLat.carrier,
    ctx.C.isInO (ctx.form v w) := by
  intro v hv w hw

  have hvw_sum : ctx.C.isInO (ctx.form (v + w) (v + w)) :=
    ctx.selfpair_add_closed v w hv hw

  have expand : ctx.form (v + w) (v + w) =
      ctx.form v v + ctx.form v w + ctx.form w v + ctx.form w w := by
    rw [ctx.form_add_left v w (v + w)]
    rw [ctx.form_symm v (v + w), ctx.form_add_left v w v,
        ctx.form_symm v v, ctx.form_symm w v]
    rw [ctx.form_symm w (v + w), ctx.form_add_left v w w,
        ctx.form_symm v w, ctx.form_symm w w]
    ring

  have symm_vw : ctx.form w v = ctx.form v w := ctx.form_symm w v


  have h_two_vw : ctx.form v w + ctx.form v w =
      ctx.form (v + w) (v + w) - ctx.form v v - ctx.form w w := by
    rw [expand, symm_vw]; ring

  have h_two_vw_inO : ctx.C.isInO (ctx.form v w + ctx.form v w) := by
    rw [h_two_vw]
    exact ctx.isInO_sub (ctx.isInO_sub hvw_sum hv) hw

  have h2_eq : ctx.form v w + ctx.form v w = ctx.C.embed (1 + 1 : ctx.C.𝔬) * ctx.form v w := by
    simp [map_add, map_one]; ring
  rw [h2_eq] at h_two_vw_inO

  have h2_ne : ctx.C.embed (1 + 1 : ctx.C.𝔬) ≠ 0 := ctx.embed_two_ne_zero
  have h_rewrite : ctx.form v w =
      (ctx.C.embed (1 + 1 : ctx.C.𝔬))⁻¹ * (ctx.C.embed (1 + 1 : ctx.C.𝔬) * ctx.form v w) := by
    rw [← mul_assoc, inv_mul_cancel₀ h2_ne, one_mul]

  rw [h_rewrite]
  exact ctx.isInO_mul (ctx.isUnitInO_inv ctx.two_is_unit) h_two_vw_inO

end AnisotropicFormContext
