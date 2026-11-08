/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.LatticesValuations

namespace DVRContext

variable (C : DVRContext)


/-- *Anisotropic quadratic space data*: a symmetric bilinear form on $V = k^n$ that is
anisotropic ($B(v,v) = 0 \Rightarrow v = 0$), together with the auxiliary hypotheses needed
to construct the unique maximal $\mathfrak{o}$-valued lattice: $2$ is a unit in
$\mathfrak{o}$, the uniformizer's image is nonzero, $\mathfrak{o}$ is integrally closed for
squares ($a^2 \in \mathfrak{o} \Rightarrow a \in \mathfrak{o}$), $\mathfrak{o}$ is
Henselian, and a normalisation hypothesis controlling the valuation of cross-ratios
$B(x,y)/B(x,x)$. -/
structure AnisotropicQuadSpace where
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  form_symm : ∀ v w, form v w = form w v
  form_smul_left : ∀ (r : C.k) v w, form (r • v) w = r * form v w
  form_add_left : ∀ u v w, form (u + v) w = form u w + form v w
  anisotropic : ∀ v, form v v = 0 → v = 0
  two_unit : C.isUnitInO (2 : C.k)
  embed_pi_ne_zero : C.embed C.uniformizer ≠ 0
  dvr_sq_integral : ∀ a : C.k, C.isInO (a * a) → C.isInO a
  inst_henselian : HenselianLocalRing C.𝔬
  hmax : C.maxIdeal = @IsLocalRing.maximalIdeal C.𝔬 C.inst_comm_ring.toCommSemiring
    inst_henselian.toIsLocalRing
  dvr_normalize_ratio : ∀ (a d : C.k),
    ¬C.isInO a → C.isInO d → d ≠ 0 →
    ∃ (n : ℕ), 0 < n ∧
      C.isUnitInO (C.embed C.uniformizer ^ n * (a * d⁻¹)) ∧
      ∀ (e : C.k), C.isInO e →
        C.isInMaxIdeal (C.embed C.uniformizer ^ (2 * n) * (e * d⁻¹))

namespace AnisotropicQuadSpace

variable {C} (B : AnisotropicQuadSpace C)


/-- *Right linearity of $B$*: derived from symmetry and left linearity, $B(v, r w) = r
B(v, w)$. -/
lemma form_smul_right (r : C.k) (v w : Fin C.n → C.k) :
    B.form v (r • w) = r * B.form v w := by
  rw [B.form_symm, B.form_smul_left, B.form_symm]

/-- *Right additivity of $B$*: derived from symmetry and left additivity,
$B(u, v + w) = B(u, v) + B(u, w)$. -/
lemma form_add_right (u v w : Fin C.n → C.k) :
    B.form u (v + w) = B.form u v + B.form u w := by
  rw [B.form_symm, B.form_add_left, B.form_symm v, B.form_symm w]

/-- *Vanishing of $B$ at zero on the left*: $B(0, v) = 0$. -/
lemma form_zero_left (v : Fin C.n → C.k) : B.form 0 v = 0 := by
  have h : (0 : Fin C.n → C.k) = (0 : C.k) • v := by
    ext i; simp [Pi.smul_apply, smul_eq_mul]
  rw [h, B.form_smul_left, zero_mul]

/-- *Vanishing of $B$ at zero on the right*: $B(v, 0) = 0$. -/
lemma form_zero_right (v : Fin C.n → C.k) : B.form v 0 = 0 := by
  rw [B.form_symm, form_zero_left]

/-- *Polarisation expansion*: $B(x + y, x + y) = B(x, x) + 2 B(x, y) + B(y, y)$, the
characteristic-zero expansion of the quadratic form along a sum. -/
lemma form_add_expand (x y : Fin C.n → C.k) :
    B.form (x + y) (x + y) = B.form x x + 2 * B.form x y + B.form y y := by
  rw [B.form_add_left, form_add_right, form_add_right]
  rw [B.form_symm y x]; ring

/-- *Scaling identity*: $B(r x, r x) = r^2 B(x, x)$ -- the quadratic form is homogeneous of
degree $2$. -/
lemma form_smul_self (r : C.k) (x : Fin C.n → C.k) :
    B.form (r • x) (r • x) = r * r * B.form x x := by
  rw [B.form_smul_left, form_smul_right, mul_assoc]


/-- *$2$ is a unit in $\mathfrak{o}$*: transfers the $2$-is-a-unit-in-$k$ hypothesis of an
anisotropic quadratic space to a statement at the level of the ring $\mathfrak{o}$, by
exploiting injectivity of the embedding $\iota : \mathfrak{o} \hookrightarrow k$. -/
lemma two_unit_o (B : AnisotropicQuadSpace C) : IsUnit (2 : C.𝔬) := by
  have h := B.two_unit
  change ∃ r : C.𝔬, IsUnit r ∧ C.embed r = 2 at h
  obtain ⟨r, hr_unit, hr_eq⟩ := h
  have h1 : C.embed r = C.embed (2 : C.𝔬) := by simp [hr_eq, map_ofNat]
  exact (C.embed_injective h1) ▸ hr_unit

/-- *Hensel's lemma applied to monic quadratic equations*: given $b \in \mathfrak{o}^\times$
and $c \in \mathfrak{m}$, the polynomial $X^2 + 2 b X + c$ has a root $\alpha \in
\mathfrak{o}$. This is the key application of `HenselianLocalRing.is_henselian` used in
constructing the maximal $\mathfrak{o}$-valued lattice. -/
theorem hensel_quadratic_root (B : AnisotropicQuadSpace C) (b c : C.k)
    (hb : C.isUnitInO b) (hc : C.isInMaxIdeal c) :
    ∃ α : C.k, C.isInO α ∧ α * α + 2 * b * α + c = 0 := by

  change ∃ r : C.𝔬, IsUnit r ∧ C.embed r = b at hb
  change ∃ r : C.𝔬, r ∈ C.maxIdeal ∧ C.embed r = c at hc
  obtain ⟨b_o, hb_unit, hb_eq⟩ := hb
  obtain ⟨c_o, hc_mem, hc_eq⟩ := hc

  haveI := B.inst_henselian
  set f := Polynomial.X ^ 2 + Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o with hf_def

  have hf_assoc : f = Polynomial.X ^ 2 +
      (Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o) := by
    rw [hf_def]; ring
  have hmonic : f.Monic := by
    rw [hf_assoc]
    apply Polynomial.monic_X_pow_add
    calc Polynomial.degree (Polynomial.C (2 * b_o) * Polynomial.X + Polynomial.C c_o)
        ≤ max (Polynomial.degree (Polynomial.C (2 * b_o) * Polynomial.X))
              (Polynomial.degree (Polynomial.C c_o)) := Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := max_le_max (Polynomial.degree_C_mul_X_le _) Polynomial.degree_C_le
      _ = 1 := by simp
      _ < 2 := by norm_cast

  have hf0 : f.eval 0 = c_o := by
    simp [hf_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C]

  have hf'0 : (Polynomial.derivative f).eval 0 = 2 * b_o := by
    simp [hf_def, Polynomial.derivative_add, Polynomial.derivative_pow,
          Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_mul,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  have hf'0_unit : IsUnit ((Polynomial.derivative f).eval 0) := by
    rw [hf'0]; exact B.two_unit_o.mul hb_unit

  rw [B.hmax] at hc_mem
  have hf0_mem : f.eval 0 ∈ IsLocalRing.maximalIdeal C.𝔬 := by rwa [hf0]

  obtain ⟨a, ha_root, _⟩ := HenselianLocalRing.is_henselian f hmonic 0 hf0_mem hf'0_unit

  use C.embed a
  constructor
  · exact ⟨a, rfl⟩
  ·
    rw [Polynomial.IsRoot] at ha_root
    simp only [hf_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at ha_root


    have h_ring : a * a + 2 * b_o * a + c_o = 0 := by ring_nf; ring_nf at ha_root; exact ha_root
    have := congr_arg C.embed h_ring
    simp only [map_add, map_mul, map_zero, map_ofNat] at this
    rwa [hb_eq, hc_eq] at this


/-- *The maximal $\mathfrak{o}$-integral set*: vectors $v \in V$ such that $B(v, v) \in
\mathfrak{o}$. This is shown below to be the carrier of the unique maximal
$\mathfrak{o}$-valued lattice. -/
def integralCarrier : Set (Fin C.n → C.k) :=
  { v | C.isInO (B.form v v) }

/-- *$\mathfrak{o}$-valued lattice*: a lattice $\Lambda$ is $\mathfrak{o}$-valued if the form
$B$ takes values in $\mathfrak{o}$ on $\Lambda \times \Lambda$. -/
def IsOValued (Λ : C.OLattice) : Prop :=
  ∀ v w, v ∈ Λ.carrier → w ∈ Λ.carrier → C.isInO (B.form v w)


/-- *Cross terms are integral*: if $B(x, x), B(y, y) \in \mathfrak{o}$, then $B(x, y) \in
\mathfrak{o}$. The proof argues by contradiction: a non-integral cross-pairing combined with
integral self-pairings would force a nontrivial isotropic vector via Hensel's lemma,
contradicting anisotropy. -/
theorem form_cross_integral [DVRClosure C]
    (x y : Fin C.n → C.k)
    (hx : C.isInO (B.form x x))
    (hy : C.isInO (B.form y y)) :
    C.isInO (B.form x y) := by

  by_cases hx_zero : x = 0
  · rw [hx_zero, B.form_zero_left]; exact DVRClosure.isInO_zero
  have hxx_ne : B.form x x ≠ 0 := fun h => hx_zero (B.anisotropic x h)
  by_contra hxy_neg
  have hy_ne : y ≠ 0 := by
    intro h; exact hxy_neg (by rw [h, B.form_zero_right]; exact DVRClosure.isInO_zero)


  obtain ⟨n, hn_pos, hb_unit, hc_maxideal⟩ :=
    B.dvr_normalize_ratio (B.form x y) (B.form x x) hxy_neg hx hxx_ne
  set pi := C.embed C.uniformizer
  set b := pi ^ n * (B.form x y * (B.form x x)⁻¹)
  set c := pi ^ (2 * n) * (B.form y y * (B.form x x)⁻¹)
  obtain ⟨α, hα_inO, hα_root⟩ := B.hensel_quadratic_root b c hb_unit (hc_maxideal _ hy)


  set w := (α • x : Fin C.n → C.k) + (pi ^ n • y : Fin C.n → C.k)
  have hw_form : B.form w w = B.form x x * (α * α + 2 * b * α + c) := by
    show B.form (α • x + pi ^ n • y) (α • x + pi ^ n • y) =
      B.form x x * (α * α + 2 * b * α + c)
    rw [B.form_add_expand, B.form_smul_self, B.form_smul_self]
    rw [B.form_smul_left, B.form_smul_right]


    show α * α * B.form x x + 2 * (α * (pi ^ n * B.form x y)) +
      pi ^ n * (pi ^ n) * B.form y y =
      B.form x x * (α * α + 2 * (pi ^ n * (B.form x y * (B.form x x)⁻¹)) * α +
        pi ^ (2 * n) * (B.form y y * (B.form x x)⁻¹))
    have hxx_inv : B.form x x * (B.form x x)⁻¹ = 1 := by
      exact mul_inv_cancel₀ hxx_ne
    have hpow : pi ^ n * pi ^ n = pi ^ (2 * n) := by
      rw [← pow_add]; ring_nf
    field_simp
    ring
  have hw_zero : B.form w w = 0 := by rw [hw_form, hα_root, mul_zero]


  have hw_eq_zero : w = 0 := B.anisotropic w hw_zero


  have hcomp : ∀ i, α * x i + pi ^ n * y i = 0 := by
    intro i
    have : (α • x + pi ^ n • y) i = (0 : Fin C.n → C.k) i := by
      exact congr_fun hw_eq_zero i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this


  by_cases hα_zero : α = 0
  ·
    have : y = 0 := by
      ext i
      have := hcomp i
      rw [hα_zero, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero n B.embed_pi_ne_zero)
    exact hy_ne this
  ·
    have hprop : x = (-(pi ^ n * α⁻¹)) • y := by
      ext i
      have hi := hcomp i
      have hα_mul : α * x i = -(pi ^ n * y i) := eq_neg_of_add_eq_zero_left hi
      have : x i = -(pi ^ n * α⁻¹) * y i := by
        have h1 := hα_mul
        have h2 : x i = α⁻¹ * (α * x i) := by
          rw [← mul_assoc, inv_mul_cancel₀ hα_zero, one_mul]
        rw [h1] at h2
        rw [h2]; ring
      simp [Pi.smul_apply, smul_eq_mul, this]

    have hxy_eq : B.form x y = -(pi ^ n * α⁻¹) * B.form y y := by
      conv_lhs => rw [hprop]
      rw [B.form_smul_left]

    have hxx_eq : B.form x x = (-(pi ^ n * α⁻¹)) * (-(pi ^ n * α⁻¹)) * B.form y y := by
      conv_lhs => rw [hprop]
      rw [B.form_smul_self]

    have hxy_sq : B.form x y * B.form x y = B.form x x * B.form y y := by
      rw [hxy_eq, hxx_eq]; ring

    have hxy_sq_inO : C.isInO (B.form x y * B.form x y) := by
      rw [hxy_sq]; exact DVRClosure.isInO_mul hx hy

    exact hxy_neg (B.dvr_sq_integral (B.form x y) hxy_sq_inO)


/-- *$B$-integral set is closed under addition*: combining `form_add_expand` with
`form_cross_integral`, the carrier $\{v : B(v, v) \in \mathfrak{o}\}$ is closed under
addition. -/
theorem integralCarrier_add_closed [DVRClosure C]
    (x y : Fin C.n → C.k)
    (hx : x ∈ B.integralCarrier) (hy : y ∈ B.integralCarrier) :
    x + y ∈ B.integralCarrier := by
  simp only [integralCarrier, Set.mem_setOf_eq] at hx hy ⊢
  rw [B.form_add_expand]
  have hxy := B.form_cross_integral x y hx hy
  exact DVRClosure.isInO_add
    (DVRClosure.isInO_add hx
      (DVRClosure.isInO_mul (by exact B.two_unit.elim fun r ⟨hr, he⟩ => ⟨r, he⟩) hxy))
    hy


/-- *Zero is $B$-integral*: $B(0, 0) = 0 \in \mathfrak{o}$. -/
theorem integralCarrier_zero_mem [DVRClosure C] : (0 : Fin C.n → C.k) ∈ B.integralCarrier := by
  simp only [integralCarrier, Set.mem_setOf_eq, B.form_zero_left]
  exact DVRClosure.isInO_zero

/-- *$B$-integral set is closed under $\mathfrak{o}$-scaling*: for $r \in \mathfrak{o}$ and
$v$ with $B(v, v) \in \mathfrak{o}$, also $B(r v, r v) = r^2 B(v, v) \in \mathfrak{o}$. -/
theorem integralCarrier_smul_mem [DVRClosure C] (r : C.𝔬) (v : Fin C.n → C.k)
    (hv : v ∈ B.integralCarrier) :
    C.oscal r v ∈ B.integralCarrier := by
  simp only [integralCarrier, Set.mem_setOf_eq] at hv ⊢
  have heq : C.oscal r v = C.embed r • v := by
    ext i; simp [DVRContext.oscal, Pi.smul_apply, smul_eq_mul]
  rw [heq, B.form_smul_self]
  exact DVRClosure.isInO_mul (DVRClosure.isInO_mul ⟨r, rfl⟩ ⟨r, rfl⟩) hv


/-- *Every $\mathfrak{o}$-valued lattice lies inside the maximal integral carrier*: this is
the maximality statement -- if $\Lambda$ takes $\mathfrak{o}$-values then in particular each
$v \in \Lambda$ has $B(v, v) \in \mathfrak{o}$. -/
theorem oValued_subset_integralCarrier (Λ : C.OLattice) (hΛ : B.IsOValued Λ) :
    Λ.carrier ⊆ B.integralCarrier :=
  fun _ hv => hΛ _ _ hv hv


/-- *Unique maximal $\mathfrak{o}$-valued lattice*: for an anisotropic quadratic space, the
carrier $\{v : B(v, v) \in \mathfrak{o}\}$ is closed under addition, contains zero, is closed
under $\mathfrak{o}$-scaling, has $B$-values in $\mathfrak{o}$, and contains every other
$\mathfrak{o}$-valued lattice. This combines the previous closure lemmas with the maximality
statement to certify the existence and uniqueness of the maximal $\mathfrak{o}$-valued
lattice. -/
theorem unique_maximal_oValued_lattice [DVRClosure C] :

    (∀ x y : Fin C.n → C.k, x ∈ B.integralCarrier → y ∈ B.integralCarrier →
      x + y ∈ B.integralCarrier) ∧

    ((0 : Fin C.n → C.k) ∈ B.integralCarrier) ∧

    (∀ (r : C.𝔬) (v : Fin C.n → C.k), v ∈ B.integralCarrier →
      C.oscal r v ∈ B.integralCarrier) ∧

    (∀ v w : Fin C.n → C.k, v ∈ B.integralCarrier → w ∈ B.integralCarrier →
      C.isInO (B.form v w)) ∧

    (∀ (Λ : C.OLattice), B.IsOValued Λ → Λ.carrier ⊆ B.integralCarrier) :=
  ⟨fun x y hx hy => B.integralCarrier_add_closed x y hx hy,
   B.integralCarrier_zero_mem,
   fun r v hv => B.integralCarrier_smul_mem r v hv,
   fun v w hv hw => B.form_cross_integral v w hv hw,
   fun Λ hΛ => B.oValued_subset_integralCarrier Λ hΛ⟩

end AnisotropicQuadSpace
end DVRContext
