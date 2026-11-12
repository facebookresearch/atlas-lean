/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent

noncomputable section

namespace PicardProjective

open MvPolynomial


/-- A nonzero homogeneous polynomial has a unique degree of homogeneity. -/
lemma homogeneous_degree_unique {σ : Type*} {k : Type*} [Field k]
    {f : MvPolynomial σ k} {d₁ d₂ : ℕ}
    (hf : f ≠ 0) (h1 : f.IsHomogeneous d₁) (h2 : f.IsHomogeneous d₂) :
    d₁ = d₂ := by
  rw [Ne, MvPolynomial.ext_iff] at hf; push Not at hf
  obtain ⟨s, hs⟩ := hf; rw [MvPolynomial.coeff_zero] at hs
  linarith [h1 hs, h2 hs]

/-- Every unit in k[x_1,...,x_n] is a constant, hence homogeneous of degree 0. -/
lemma isUnit_isHomogeneous_zero {σ : Type*} {k : Type*} [Field k]
    {u : MvPolynomial σ k} (hu : IsUnit u) : u.IsHomogeneous 0 := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hu
  obtain ⟨r, _, rfl⟩ := hu; exact isHomogeneous_C σ r

/-- Associated homogeneous polynomials (i.e. differing by a unit) have the same
degree. -/
lemma associated_homogeneous_same_degree {σ : Type*} {k : Type*} [Field k]
    {f g : MvPolynomial σ k} {d₁ d₂ : ℕ}
    (hg : g ≠ 0) (hfh : f.IsHomogeneous d₁) (hgh : g.IsHomogeneous d₂)
    (h : Associated f g) : d₁ = d₂ := by
  obtain ⟨u, hu⟩ := h
  have : (f * u).IsHomogeneous (d₁ + 0) := hfh.mul (isUnit_isHomogeneous_zero u.isUnit)
  simp only [Nat.add_zero] at this; rw [hu] at this
  exact homogeneous_degree_unique hg this hgh


/-- The polynomial ring k[x_1,...,x_n] is a UFD. -/
theorem mvPolynomial_fin_ufd (k : Type*) [Field k] (n : ℕ) :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) k) := inferInstance

/-- The polynomial ring R[x_σ] over a UFD R (with any number of variables) is a UFD. -/
theorem mvPolynomial_ufd_of_ufd (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (σ : Type*) :
    UniqueFactorizationMonoid (MvPolynomial σ R) := inferInstance

/-- The (divisor) class group of a polynomial ring over a field is trivial. -/
instance classGroup_mvPolynomial_subsingleton (k : Type*) [Field k] (σ : Type*) :
    Subsingleton (ClassGroup (MvPolynomial σ k)) := inferInstance

/-- The class group of the univariate polynomial ring k[x] is trivial. -/
instance classGroup_polynomial_subsingleton (k : Type*) [Field k] :
    Subsingleton (ClassGroup (Polynomial k)) := inferInstance

/-- The class group of k[x_1,...,x_n] is the trivial group with a unique element. -/
instance classGroup_mvPolynomial_unique (k : Type*) [Field k] (n : ℕ) :
    Unique (ClassGroup (MvPolynomial (Fin n) k)) := Unique.mk' _

/-- The class group of k[x_1,...,x_n] is isomorphic (as a group) to the trivial
group `Unit`. -/
def classGroup_mvPolynomial_mulEquiv_unit (k : Type*) [Field k] (n : ℕ) :
    ClassGroup (MvPolynomial (Fin n) k) ≃* (Unit : Type) := MulEquiv.ofUnique


/-- A homogeneous fraction: a pair of nonzero homogeneous polynomials of recorded
degrees, representing a section of a twist O(d) on projective space. -/
structure HomogFraction (σ : Type*) (k : Type*) [Field k] where
  num : MvPolynomial σ k
  den : MvPolynomial σ k
  num_ne : num ≠ 0
  den_ne : den ≠ 0
  ndeg : ℕ
  ddeg : ℕ
  nhom : num.IsHomogeneous ndeg
  dhom : den.IsHomogeneous ddeg

/-- The degree of a homogeneous fraction: numerator degree minus denominator degree. -/
def HomogFraction.degree (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : ℤ :=
  (p.ndeg : ℤ) - (p.ddeg : ℤ)

/-- Equivalence relation on homogeneous fractions identifying those that represent
the same line bundle class in Pic(P^n). -/
def HomogFraction.PicEquiv (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) : Prop :=
  ∃ (a b : MvPolynomial σ k) (da db : ℕ),
    a ≠ 0 ∧ b ≠ 0 ∧ a.IsHomogeneous da ∧ b.IsHomogeneous db ∧
    da = db ∧ Associated (p.num * b * q.den) (q.num * a * p.den)

/-- Reflexivity of the Pic equivalence relation on homogeneous fractions. -/
lemma HomogFraction.PicEquiv.rfl' (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : p.PicEquiv σ k p :=
  ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
   isHomogeneous_one σ k, isHomogeneous_one σ k,
   rfl, Associated.refl _⟩

/-- Symmetry of the Pic equivalence relation. -/
lemma HomogFraction.PicEquiv.symm' (σ : Type*) (k : Type*) [Field k]
    {p q : HomogFraction σ k}
    (h : p.PicEquiv σ k q) : q.PicEquiv σ k p := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  exact ⟨b, a, db, da, hb, ha, hbh, hah, hd.symm, hass.symm⟩

/-- Transitivity of the Pic equivalence relation. -/
lemma HomogFraction.PicEquiv.trans' (σ : Type*) (k : Type*) [Field k]
    {p q r : HomogFraction σ k}
    (h1 : p.PicEquiv σ k q) (h2 : q.PicEquiv σ k r) :
    p.PicEquiv σ k r := by
  obtain ⟨a₁, b₁, da₁, db₁, ha₁, hb₁, ha₁h, hb₁h, hd₁, hass₁⟩ := h1
  obtain ⟨a₂, b₂, da₂, db₂, ha₂, hb₂, ha₂h, hb₂h, hd₂, hass₂⟩ := h2
  refine ⟨a₁ * a₂, b₁ * b₂, da₁ + da₂, db₁ + db₂,
    mul_ne_zero ha₁ ha₂, mul_ne_zero hb₁ hb₂,
    ha₁h.mul ha₂h, hb₁h.mul hb₂h, by omega, ?_⟩
  have h1' := hass₁.mul_right (b₂ * r.den)
  have h2' := hass₂.mul_right (a₁ * p.den)
  have heq1 : q.num * a₁ * p.den * (b₂ * r.den) =
    q.num * b₂ * r.den * (a₁ * p.den) := by ring
  rw [heq1] at h1'
  have h3 := h1'.trans h2'
  have heq2 : p.num * b₁ * q.den * (b₂ * r.den) =
    q.den * (p.num * (b₁ * b₂) * r.den) := by ring
  have heq3 : r.num * a₂ * q.den * (a₁ * p.den) =
    q.den * (r.num * (a₁ * a₂) * p.den) := by ring
  rw [heq2, heq3] at h3
  exact Associated.of_mul_left h3 (Associated.refl _) q.den_ne

/-- The setoid on homogeneous fractions induced by the Pic equivalence relation. -/
instance homogFractionSetoid (σ : Type*) (k : Type*) [Field k] :
    Setoid (HomogFraction σ k) where
  r := HomogFraction.PicEquiv σ k
  iseqv := ⟨HomogFraction.PicEquiv.rfl' σ k,
            fun h => HomogFraction.PicEquiv.symm' σ k h,
            fun h1 h2 => HomogFraction.PicEquiv.trans' σ k h1 h2⟩

/-- The graded Picard group: equivalence classes of homogeneous fractions, modeling
Pic(P^n) by twisting sheaves up to isomorphism. -/
def GradedPicardGroup (σ : Type*) (k : Type*) [Field k] :=
  Quotient (homogFractionSetoid σ k)


/-- The degree function is compatible with the Pic equivalence relation: equivalent
homogeneous fractions have the same degree. -/
lemma degree_compat (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) (h : p.PicEquiv σ k q) :
    p.degree σ k = q.degree σ k := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  unfold HomogFraction.degree
  have lhs_ne : p.num * b * q.den ≠ 0 := mul_ne_zero (mul_ne_zero p.num_ne hb) q.den_ne
  have rhs_ne : q.num * a * p.den ≠ 0 := mul_ne_zero (mul_ne_zero q.num_ne ha) p.den_ne
  have lhs_hom : (p.num * b * q.den).IsHomogeneous (p.ndeg + db + q.ddeg) :=
    (p.nhom.mul hbh).mul q.dhom
  have rhs_hom : (q.num * a * p.den).IsHomogeneous (q.ndeg + da + p.ddeg) :=
    (q.nhom.mul hah).mul p.dhom
  have := associated_homogeneous_same_degree rhs_ne lhs_hom rhs_hom hass
  omega

/-- The degree map Pic(P^n) → ℤ defined on equivalence classes. -/
def GradedPicardGroup.degreeMap (σ : Type*) (k : Type*) [Field k] :
    GradedPicardGroup σ k → ℤ :=
  Quotient.lift (HomogFraction.degree σ k) (degree_compat σ k)


/-- Multiplication of homogeneous fractions: corresponds to tensor product of twists
in Pic(P^n). -/
def HomogFraction.mul (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) : HomogFraction σ k where
  num := p.num * q.num
  den := p.den * q.den
  num_ne := mul_ne_zero p.num_ne q.num_ne
  den_ne := mul_ne_zero p.den_ne q.den_ne
  ndeg := p.ndeg + q.ndeg
  ddeg := p.ddeg + q.ddeg
  nhom := p.nhom.mul q.nhom
  dhom := p.dhom.mul q.dhom

/-- The trivial homogeneous fraction 1/1, representing the structure sheaf O_{P^n}. -/
def HomogFraction.one (σ : Type*) (k : Type*) [Field k] : HomogFraction σ k where
  num := 1
  den := 1
  num_ne := one_ne_zero
  den_ne := one_ne_zero
  ndeg := 0
  ddeg := 0
  nhom := isHomogeneous_one σ k
  dhom := isHomogeneous_one σ k

/-- Inverse of a homogeneous fraction: swap numerator and denominator, corresponding
to the dual line bundle. -/
def HomogFraction.inv (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : HomogFraction σ k where
  num := p.den
  den := p.num
  num_ne := p.den_ne
  den_ne := p.num_ne
  ndeg := p.ddeg
  ddeg := p.ndeg
  nhom := p.dhom
  dhom := p.nhom

/-- Multiplication of homogeneous fractions respects the Pic equivalence relation. -/
lemma mul_compat (σ : Type*) (k : Type*) [Field k]
    {p₁ p₂ q₁ q₂ : HomogFraction σ k}
    (hp : p₁.PicEquiv σ k p₂) (hq : q₁.PicEquiv σ k q₂) :
    (p₁.mul σ k q₁).PicEquiv σ k (p₂.mul σ k q₂) := by
  obtain ⟨ap, bp, dap, dbp, hap, hbp, haph, hbph, hdp, hassp⟩ := hp
  obtain ⟨aq, bq, daq, dbq, haq, hbq, haqh, hbqh, hdq, hassq⟩ := hq
  refine ⟨ap * aq, bp * bq, dap + daq, dbp + dbq,
    mul_ne_zero hap haq, mul_ne_zero hbp hbq,
    haph.mul haqh, hbph.mul hbqh, by omega, ?_⟩
  obtain ⟨u₁, hu₁⟩ := hassp
  obtain ⟨u₂, hu₂⟩ := hassq
  exact ⟨u₁ * u₂, by
    simp only [HomogFraction.mul, Units.val_mul]
    calc p₁.num * q₁.num * (bp * bq) * (p₂.den * q₂.den) * (↑u₁ * ↑u₂)
        = (p₁.num * bp * p₂.den * ↑u₁) * (q₁.num * bq * q₂.den * ↑u₂) := by ring
      _ = (p₂.num * ap * p₁.den) * (q₂.num * aq * q₁.den) := by rw [hu₁, hu₂]
      _ = p₂.num * q₂.num * (ap * aq) * (p₁.den * q₁.den) := by ring⟩

/-- Inversion of homogeneous fractions respects the Pic equivalence relation. -/
lemma inv_compat (σ : Type*) (k : Type*) [Field k]
    {p q : HomogFraction σ k}
    (h : p.PicEquiv σ k q) : (p.inv σ k).PicEquiv σ k (q.inv σ k) := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  refine ⟨b, a, db, da, hb, ha, hbh, hah, hd.symm, ?_⟩
  simp only [HomogFraction.inv]
  obtain ⟨u, hu⟩ := hass.symm
  exact ⟨u, by
    calc p.den * a * q.num * ↑u
        = q.num * a * p.den * ↑u := by ring
      _ = p.num * b * q.den := hu
      _ = q.den * b * p.num := by ring⟩

/-- The zero element of the graded Picard group (additive notation): the class of
the trivial fraction. -/
instance gradedPicardGroupZero (σ : Type*) (k : Type*) [Field k] :
    Zero (GradedPicardGroup σ k) :=
  ⟨⟦HomogFraction.one σ k⟧⟩

/-- Addition in the graded Picard group: induced from multiplication of fractions. -/
instance gradedPicardGroupAdd (σ : Type*) (k : Type*) [Field k] :
    Add (GradedPicardGroup σ k) :=
  ⟨Quotient.lift₂ (fun p q => ⟦p.mul σ k q⟧)
    (fun _ _ _ _ hp hq => Quotient.sound (mul_compat σ k hp hq))⟩

/-- Negation in the graded Picard group: induced from inversion of fractions. -/
instance gradedPicardGroupNeg (σ : Type*) (k : Type*) [Field k] :
    Neg (GradedPicardGroup σ k) :=
  ⟨Quotient.lift (fun p => ⟦p.inv σ k⟧)
    (fun _ _ h => Quotient.sound (inv_compat σ k h))⟩

/-- Two homogeneous fractions with identical components are equivalent. -/
lemma ring_assoc_equiv (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k)
    (hn : p.num = q.num) (hd : p.den = q.den)
    (_ : p.ndeg = q.ndeg) (_ : p.ddeg = q.ddeg) :
    p.PicEquiv σ k q := by
  refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
    isHomogeneous_one σ k, isHomogeneous_one σ k, rfl, ?_⟩
  rw [mul_one, mul_one, hn, hd]

/-- The graded Picard group is an additive commutative group. -/
instance gradedPicardGroupAddCommGroup (σ : Type*) (k : Type*) [Field k] :
    AddCommGroup (GradedPicardGroup σ k) where
  add_assoc a b c := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, mul_assoc, Nat.add_assoc]
  zero_add a := by
    induction a using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, HomogFraction.one]
  add_zero a := by
    induction a using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, HomogFraction.one]
  neg_add_cancel a := by
    induction a using Quotient.ind
    rename_i p
    apply Quotient.sound
    refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
      isHomogeneous_one σ k, isHomogeneous_one σ k, rfl, ?_⟩
    simp only [HomogFraction.mul, HomogFraction.inv, HomogFraction.one]
    have h : p.den * p.num * 1 * 1 = 1 * 1 * (p.num * p.den) := by ring
    rw [h]
  add_comm a b := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    apply ring_assoc_equiv <;> simp [HomogFraction.mul, mul_comm, Nat.add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec


/-- The degree map is additive: deg(L ⊗ M) = deg(L) + deg(M). -/
lemma degreeMap_add (σ : Type*) (k : Type*) [Field k]
    (a b : GradedPicardGroup σ k) :
    GradedPicardGroup.degreeMap σ k (a + b) =
      GradedPicardGroup.degreeMap σ k a + GradedPicardGroup.degreeMap σ k b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i p q
  show (p.mul σ k q).degree σ k = p.degree σ k + q.degree σ k
  simp only [HomogFraction.degree, HomogFraction.mul]
  push_cast; ring

/-- The degree map as an additive group homomorphism Pic(P^n) → ℤ. -/
def GradedPicardGroup.degreeHom (σ : Type*) (k : Type*) [Field k] :
    GradedPicardGroup σ k →+ ℤ where
  toFun := GradedPicardGroup.degreeMap σ k
  map_zero' := by
    simp only [GradedPicardGroup.degreeMap]
    change Quotient.lift (HomogFraction.degree σ k) _ ⟦HomogFraction.one σ k⟧ = 0
    simp [HomogFraction.degree, HomogFraction.one]
  map_add' := degreeMap_add σ k


/-- The homogeneous fraction representing the d-th twist O(d) on P^n. -/
def twistFraction (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    HomogFraction (Fin (n + 1)) k :=
  if hd : 0 ≤ d then
    { num := (X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ d.toNat
      den := 1
      num_ne := pow_ne_zero _ (X_ne_zero _)
      den_ne := one_ne_zero
      ndeg := d.toNat
      ddeg := 0
      nhom := by simpa using (isHomogeneous_X k (0 : Fin (n + 1))).pow d.toNat
      dhom := isHomogeneous_one _ k }
  else
    { num := 1
      den := (X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ (-d).toNat
      num_ne := one_ne_zero
      den_ne := pow_ne_zero _ (X_ne_zero _)
      ndeg := 0
      ddeg := (-d).toNat
      nhom := isHomogeneous_one _ k
      dhom := by simpa using (isHomogeneous_X k (0 : Fin (n + 1))).pow (-d).toNat }

/-- The twist O(d) has degree d. -/
lemma twistFraction_degree (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    (twistFraction n k d).degree (Fin (n + 1)) k = d := by
  unfold twistFraction HomogFraction.degree
  split
  · simp only [Int.toNat_of_nonneg (by omega : 0 ≤ d)]
    omega
  · simp only [Int.toNat_of_nonneg (by omega : 0 ≤ -d)]
    omega

/-- The twisting sheaf O(d) in Pic(P^n), as the class of the d-th twist fraction. -/
def twistingSheafPow (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    GradedPicardGroup (Fin (n + 1)) k :=
  ⟦twistFraction n k d⟧

/-- The Serre twisting sheaf O(1) generating Pic(P^n) ≅ ℤ. -/
def twistingSheaf (n : ℕ) (k : Type*) [Field k] :
    GradedPicardGroup (Fin (n + 1)) k :=
  twistingSheafPow n k 1

/-- The degree homomorphism Pic(P^n) → ℤ is surjective (every integer is realized by
some O(d)). -/
lemma degreeHom_surjective (n : ℕ) (k : Type*) [Field k] :
    Function.Surjective (GradedPicardGroup.degreeHom (Fin (n + 1)) k) := by
  intro d
  exact ⟨twistingSheafPow n k d, by
    simp only [GradedPicardGroup.degreeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact twistFraction_degree n k d⟩


/-- A homogeneous fraction of degree 0 is equivalent to the trivial fraction. -/
lemma degree_zero_equiv_one (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) (hdeg : p.degree σ k = 0) :
    p.PicEquiv σ k (HomogFraction.one σ k) := by
  have hdeq : p.ndeg = p.ddeg := by unfold HomogFraction.degree at hdeg; omega
  refine ⟨p.num, p.den, p.ndeg, p.ddeg, p.num_ne, p.den_ne,
    p.nhom, p.dhom, hdeq, ?_⟩
  simp only [HomogFraction.one]
  have : p.num * p.den * 1 = 1 * p.num * p.den := by ring
  rw [this]

/-- The degree homomorphism is injective: any line bundle of degree 0 is trivial. -/
lemma degreeHom_injective (σ : Type*) (k : Type*) [Field k] :
    Function.Injective (GradedPicardGroup.degreeHom σ k) := by
  intro x y hxy
  induction x using Quotient.ind
  induction y using Quotient.ind
  apply Quotient.sound
  rename_i p q
  have hpq : p.degree σ k = q.degree σ k := hxy


  have hdeq : p.ndeg + q.ddeg = q.ndeg + p.ddeg := by
    unfold HomogFraction.degree at hpq; omega
  refine ⟨p.num * q.den, q.num * p.den,
    p.ndeg + q.ddeg, q.ndeg + p.ddeg,
    mul_ne_zero p.num_ne q.den_ne, mul_ne_zero q.num_ne p.den_ne,
    p.nhom.mul q.dhom, q.nhom.mul p.dhom, hdeq, ?_⟩
  have : p.num * (q.num * p.den) * q.den = q.num * (p.num * q.den) * p.den := by ring
  rw [this]


/-- The fundamental identification Pic(P^n) ≅ ℤ as additive groups, via the degree map. -/
def gradedPicardGroup_equiv_int (k : Type*) [Field k] (n : ℕ) :
    GradedPicardGroup (Fin (n + 1)) k ≃+ ℤ :=
  AddEquiv.ofBijective
    (GradedPicardGroup.degreeHom (Fin (n + 1)) k)
    ⟨degreeHom_injective (Fin (n + 1)) k,
     degreeHom_surjective n k⟩

/-- Under the equivalence Pic(P^n) ≅ ℤ, the twist O(d) corresponds to the integer d. -/
theorem degree_twistingSheafPow (k : Type*) [Field k] (n : ℕ) (d : ℤ) :
    (gradedPicardGroup_equiv_int k n) (twistingSheafPow n k d) = d := by
  simp only [gradedPicardGroup_equiv_int, AddEquiv.ofBijective,
    GradedPicardGroup.degreeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact twistFraction_degree n k d

/-- The Serre twisting sheaf O(1) corresponds to the integer 1 under Pic(P^n) ≅ ℤ. -/
theorem degree_twistingSheaf (k : Type*) [Field k] (n : ℕ) :
    (gradedPicardGroup_equiv_int k n) (twistingSheaf n k) = 1 :=
  degree_twistingSheafPow k n 1

/-- Pic(P^n) is generated by O(1): every line bundle on P^n is some O(d). -/
theorem picardGroup_generated_by_O1 (k : Type*) [Field k] (n : ℕ)
    (L : GradedPicardGroup (Fin (n + 1)) k) :
    ∃ d : ℤ, L = twistingSheafPow n k d := by
  use (gradedPicardGroup_equiv_int k n) L
  apply (gradedPicardGroup_equiv_int k n).injective
  rw [degree_twistingSheafPow]

end PicardProjective
