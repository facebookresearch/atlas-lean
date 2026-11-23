/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic

/-- Notation `𝔽 p` for the finite field with `p` elements, defined as
`ZMod p` (the quotient `ℤ / p ℤ`). Matches Definition 3.2. -/
abbrev 𝔽 (p : ℕ) := ZMod p

/-- Alternative non-`abbrev` synonym `Fp p := ZMod p` for `𝔽 p`. -/
def Fp (p : ℕ) : Type := ZMod p

open Polynomial in
/-- Notation `𝔽q p n` for the finite field with `p^n` elements, defined
as `GaloisField p n` (the splitting field of `X^(p^n) - X` over `𝔽_p`).
Matches Definition 3.4. -/
abbrev 𝔽q (p : ℕ) [Fact p.Prime] (n : ℕ) := GaloisField p n

section Def34

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open Polynomial

/-- `𝔽q p n` is, by definition, the splitting field of `X^(p^n) - X` over
`𝔽_p`, matching the splitting-field description in Definition 3.4. -/
theorem 𝔽q_isSplittingField :
    IsSplittingField (ZMod p) (𝔽q p n) (X ^ p ^ n - X : (ZMod p)[X]) := by
  show IsSplittingField (ZMod p) (SplittingField (X ^ p ^ n - X : (ZMod p)[X])) _
  infer_instance

/-- Frobenius identity in `𝔽q p n`: every element satisfies `x^(p^n) = x`,
i.e. `𝔽q p n` consists of roots of `X^(p^n) - X`. -/
theorem 𝔽q_frobenius (hn : n ≠ 0) (x : 𝔽q p n) : x ^ (p ^ n) = x := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  have hcard : Nat.card (𝔽q p n) = p ^ n := GaloisField.card p n hn
  rw [show p ^ n = Fintype.card (𝔽q p n) from by rw [Fintype.card_eq_nat_card]; omega]
  exact FiniteField.pow_card x

/-- Theorem 3.6 (cardinality half): `𝔽q p n` has exactly `p^n` elements. -/
theorem 𝔽q_card (hn : n ≠ 0) : Nat.card (𝔽q p n) = p ^ n :=
  GaloisField.card p n hn

/-- `𝔽q p 1` is canonically isomorphic to `𝔽_p = ZMod p` as a `ZMod p`-algebra. -/
noncomputable def 𝔽q_equivZModP : 𝔽q p 1 ≃ₐ[ZMod p] ZMod p :=
  GaloisField.equivZmodP p

end Def34

section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Theorem 3.6, cardinality half: `|𝔽q p n| = p^n`. -/
theorem 𝔽q_card_thm36 (hn : n ≠ 0) : Nat.card (𝔽q p n) = p ^ n :=
  GaloisField.card p n hn

/-- Theorem 3.6, uniqueness half (data form): a choice of ring isomorphism
between any finite field `K` of cardinality `p^n` and `𝔽q p n`. -/
noncomputable def 𝔽q_ringEquiv_of_card (hn : n ≠ 0)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p ^ n) :
    K ≃+* 𝔽q p n := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  have hcard : Fintype.card (𝔽q p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p n hn
  exact FiniteField.ringEquivOfCardEq (hK.trans hcard.symm)

/-- Theorem 3.6, uniqueness half (propositional form): any finite field of
cardinality `p^n` is isomorphic to `𝔽q p n`. -/
theorem 𝔽q_unique_of_card (hn : n ≠ 0)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p ^ n) :
    Nonempty (K ≃+* 𝔽q p n) :=
  ⟨𝔽q_ringEquiv_of_card p n hn K hK⟩

/-- Alias of `𝔽q_unique_of_card` with implicit arguments restructured. -/
theorem Fq_unique_of_card {K : Type*} [Field K] [Fintype K]
    (hn : n ≠ 0) (hcard : Fintype.card K = p ^ n) :
    Nonempty (K ≃+* 𝔽q p n) :=
  𝔽q_unique_of_card p n hn K hcard

/-- Two finite fields of the same cardinality are isomorphic — a general form
of the uniqueness statement in Theorem 3.6. -/
theorem finite_fields_isomorphic_of_card_eq
    (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Fintype K₁] [Fintype K₂]
    (h : Fintype.card K₁ = Fintype.card K₂) :
    Nonempty (K₁ ≃+* K₂) :=
  ⟨FiniteField.ringEquivOfCardEq h⟩

end Theorem_3_6

section Theorem_3_8

variable (p : ℕ) [Fact p.Prime] (m n : ℕ)

/-- Theorem 3.8: `𝔽_{p^m}` embeds into `𝔽_{p^n}` (as a `ZMod p`-algebra) iff
`m ∣ n`. -/
theorem 𝔽q_subfield_iff (hm : m ≠ 0) (hn : n ≠ 0) :
    Nonempty (𝔽q p m →ₐ[ZMod p] 𝔽q p n) ↔ m ∣ n := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd,
    GaloisField.finrank p hm, GaloisField.finrank p hn]

end Theorem_3_8

section Theorem_3_3

/-- `𝔽 p` is a field whenever `p` is prime. -/
instance Fp_field (p : ℕ) [hp : Fact (Nat.Prime p)] : Field (𝔽 p) := ZMod.instField p

/-- Theorem 3.3 (existence of canonical embedding): every field `K` of
characteristic `p` admits a canonical injective ring homomorphism from `𝔽 p`. -/
theorem Fp_canonical_map (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [CharP K p] :
    ∃ f : 𝔽 p →+* K, Function.Injective f :=
  ⟨ZMod.castHom (dvd_refl p) K, ZMod.castHom_injective K⟩

/-- Theorem 3.3 (uniqueness): every field of cardinality `p` (with `p` prime)
is isomorphic to `𝔽 p`. -/
theorem Fp_unique_of_card (p : ℕ) (hp : Nat.Prime p)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p) :
    Nonempty (𝔽 p ≃+* K) :=
  ⟨ZMod.ringEquivOfPrime K hp hK⟩

/-- Two fields of prime cardinality `p` are isomorphic, by Theorem 3.3. -/
theorem fields_of_card_prime_isomorphic (p : ℕ) (hp : Nat.Prime p)
    (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Fintype K₁] [Fintype K₂]
    (hK₁ : Fintype.card K₁ = p) (hK₂ : Fintype.card K₂ = p) :
    Nonempty (K₁ ≃+* K₂) := by
  have e₁ := ZMod.ringEquivOfPrime K₁ hp hK₁
  have e₂ := ZMod.ringEquivOfPrime K₂ hp hK₂
  exact ⟨e₁.symm.trans e₂⟩

/-- Restatement of `Fp_canonical_map`: any field of characteristic `p` contains
a copy of `𝔽 p` via an injective ring homomorphism. -/
theorem char_p_contains_Fp (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [CharP K p] :
    ∃ f : 𝔽 p →+* K, Function.Injective f :=
  Fp_canonical_map p K

/-- Alias of `Fp_unique_of_card`: any field of prime cardinality `p` is
isomorphic to `𝔽 p`. -/
theorem Fp_unique_of_card_prime (p : ℕ) (hp : Nat.Prime p)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p) :
    Nonempty (𝔽 p ≃+* K) :=
  Fp_unique_of_card p hp K hK

end Theorem_3_3

namespace Polynomial

section Def317

variable {k : Type*} [Field k]

/-- Definition 3.17: `f` is separable iff it has `deg f` distinct roots in
any algebraic closure — encoded here via Mathlib's `Polynomial.Separable`. -/
def IsSeparablePoly (f : k[X]) : Prop := f.Separable

/-- A polynomial is inseparable iff it is not separable. -/
def IsInseparablePoly (f : k[X]) : Prop := ¬f.Separable

/-- Unfolding lemma: `IsSeparablePoly f` is definitionally `f.Separable`. -/
theorem isSeparablePoly_iff_separable (f : k[X]) : IsSeparablePoly f ↔ f.Separable :=
  Iff.rfl

/-- Unfolding lemma: `IsInseparablePoly f` is definitionally `¬ f.Separable`. -/
theorem isInseparablePoly_iff_not_separable (f : k[X]) :
    IsInseparablePoly f ↔ ¬f.Separable :=
  Iff.rfl

/-- One of the equivalent formulations from Definition 3.17: separability is
the same as `f` being coprime to its derivative `f'`. -/
theorem separable_iff_coprime_derivative (f : k[X]) :
    f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl

/-- Definition 3.17, distinct-roots criterion: if `f` splits over `K`, then
`f` is separable iff `|{roots of f in K}| = deg f`. -/
theorem separable_iff_card_rootSet_eq_natDegree {K : Type*} [Field K] [Algebra k K]
    {f : k[X]} (hf : f ≠ 0) (hsplit : (f.map (algebraMap k K)).Splits) :
    f.Separable ↔ Fintype.card (f.rootSet K) = f.natDegree :=
  (card_rootSet_eq_natDegree_iff_of_splits hf hsplit).symm

/-- A separable polynomial is squarefree (one half of the squarefree-on-every-
extension characterization in Definition 3.17). -/
theorem separable_implies_squarefree {f : k[X]} (hsep : f.Separable) :
    Squarefree f :=
  hsep.squarefree

/-- Over a perfect field, separability and squarefreeness coincide for
polynomials. -/
theorem separable_iff_squarefree_of_perfectField [PerfectField k] (f : k[X]) :
    f.Separable ↔ Squarefree f :=
  PerfectField.separable_iff_squarefree

end Def317

section Lem320

variable {k : Type*} [Field k]

/-- Lemma 3.20: an irreducible polynomial `f` is inseparable iff its formal
derivative `f'` is identically zero. -/
theorem irreducible_inseparable_iff_derivative_eq_zero
    {f : k[X]} (hf : Irreducible f) :
    ¬ f.Separable ↔ derivative f = 0 := by
  rw [separable_iff_derivative_ne_zero hf, not_not]

end Lem320

end Polynomial

section Theorem_3_12

open Subgroup in
/-- Theorem 3.12: every finite subgroup of the multiplicative group `kˣ` of a
field is cyclic. -/
theorem finite_mult_subgroup_of_field_isCyclic
    (k : Type*) [Field k] (G : Subgroup kˣ) [Finite G] : IsCyclic G :=
  isCyclic_subgroup_units G

end Theorem_3_12

section Corollary_3_13

/-- Corollary 3.13: the multiplicative group `kˣ` of a finite field is cyclic. -/
theorem finite_field_mult_isCyclic
    (k : Type*) [Field k] [Fintype k] : IsCyclic kˣ := by
  have : IsCyclic (⊤ : Subgroup kˣ) := finite_mult_subgroup_of_field_isCyclic k ⊤
  exact isCyclic_of_surjective Subgroup.topEquiv Subgroup.topEquiv.surjective

/-- Specialization of Corollary 3.13 to `𝔽q p n`: the multiplicative group
`(𝔽q p n)ˣ` is cyclic. -/
noncomputable instance 𝔽q_units_isCyclic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCyclic (𝔽q p n)ˣ := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  exact finite_field_mult_isCyclic (𝔽q p n)

end Corollary_3_13

section Definition_3_14

variable (p : ℕ) [Fact p.Prime]

open Polynomial

/-- Definition 3.14: a monic irreducible `f ∈ 𝔽_p[x]` is primitive iff its
adjoined root has order `p^(deg f) - 1` (i.e. generates the multiplicative
group of `𝔽_p[x]/(f)`). -/
def Polynomial.IsPrimitivePolynomial (f : (ZMod p)[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1

/-- A primitive polynomial is monic. -/
theorem Polynomial.IsPrimitivePolynomial.monic {f : (ZMod p)[X]}
    (hf : f.IsPrimitivePolynomial p) : f.Monic :=
  hf.1

/-- A primitive polynomial is irreducible. -/
theorem Polynomial.IsPrimitivePolynomial.irreducible {f : (ZMod p)[X]}
    (hf : f.IsPrimitivePolynomial p) : Irreducible f :=
  hf.2.1

/-- For a primitive polynomial `f`, its adjoined root has order `p^(deg f) - 1`. -/
theorem Polynomial.IsPrimitivePolynomial.root_orderOf {f : (ZMod p)[X]}
    (hf : f.IsPrimitivePolynomial p) :
    orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 :=
  hf.2.2

end Definition_3_14

open Polynomial in
/-- Equivalence: a field `k` is perfect (Definition 3.21) iff every
irreducible polynomial in `k[x]` is separable. -/
theorem perfectField_iff_irreducible_separable (k : Type*) [Field k] :
    PerfectField k ↔ ∀ f : k[X], Irreducible f → f.Separable := by
  constructor
  · intro h f hf
    exact @PerfectField.separable_of_irreducible k _ h f hf
  · intro h
    exact ⟨fun hf => h _ hf⟩

/-- Theorem 3.22: every finite field is perfect. -/
theorem finite_field_isPerfect (K : Type*) [Field K] [Finite K] : PerfectField K :=
  inferInstance

section Theorem_3_9

variable (p : ℕ) [hp : Fact p.Prime]

open Polynomial

/-- Theorem 3.9 (data form): for any irreducible `f ∈ 𝔽_p[x]` of positive
degree `n`, the quotient ring `𝔽_p[x]/(f)` is ring-isomorphic to `𝔽_{p^n}`. -/
noncomputable def quotient_irred_ringEquiv_𝔽q
    (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (hn : f.natDegree ≠ 0) :
    AdjoinRoot f ≃+* 𝔽q p f.natDegree := by


  have hf0 : f ≠ 0 := hf.out.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  haveI : Fintype (AdjoinRoot f) := Module.fintypeOfFintype pb.basis
  have hcard_adj : Fintype.card (AdjoinRoot f) = p ^ f.natDegree := by
    have := Module.card_fintype pb.basis
    rw [Fintype.card_fin, AdjoinRoot.powerBasis_dim, ZMod.card] at this
    exact this

  haveI : Fintype (𝔽q p f.natDegree) := Fintype.ofFinite _
  have hcard_gf : Fintype.card (𝔽q p f.natDegree) = p ^ f.natDegree := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p f.natDegree hn
  exact FiniteField.ringEquivOfCardEq (hcard_adj.trans hcard_gf.symm)

/-- Theorem 3.9 (propositional form): for irreducible `f` of positive degree,
`𝔽_p[x]/(f) ≃ 𝔽_{p^{deg f}}`. -/
theorem quotient_irred_iso_𝔽q
    (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (hn : f.natDegree ≠ 0) :
    Nonempty (AdjoinRoot f ≃+* 𝔽q p f.natDegree) :=
  ⟨quotient_irred_ringEquiv_𝔽q p f hn⟩

end Theorem_3_9

section Corollary_3_10

variable (p : ℕ) [hp : Fact p.Prime]

open Polynomial

/-- Corollary 3.10: every irreducible `f ∈ 𝔽_p[x]` of positive degree `n`
splits completely in `𝔽_{p^n}`. -/
theorem irred_splits_in_𝔽q
    (f : (ZMod p)[X]) (hf : Irreducible f) (hn : f.natDegree ≠ 0) :
    (f.map (algebraMap (ZMod p) (𝔽q p f.natDegree))).Splits := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero


  have hfr : Module.finrank (ZMod p) (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf0).finrank.trans (AdjoinRoot.powerBasis_dim hf0)
  have hgfr : Module.finrank (ZMod p) (𝔽q p f.natDegree) = f.natDegree :=
    GaloisField.finrank p hn
  have hdvd : Module.finrank (ZMod p) (AdjoinRoot f) ∣
      Module.finrank (ZMod p) (𝔽q p f.natDegree) := by
    rw [hfr, hgfr]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd

  let α := φ (AdjoinRoot.root f)
  have hα : aeval α f = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

  have hint : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  have hmin_irr : Irreducible (minpoly (ZMod p) α) := minpoly.irreducible hint
  have hmin_dvd : minpoly (ZMod p) α ∣ f := minpoly.dvd _ _ hα

  have hf_dvd_min : f ∣ minpoly (ZMod p) α :=
    (hmin_irr.associated_of_dvd hf hmin_dvd).symm.dvd

  exact (Normal.splits' α).of_dvd
    (map_ne_zero (minpoly.ne_zero hint))
    (map_dvd _ hf_dvd_min)

/-- Restatement of Corollary 3.10 with `GaloisField` notation: irreducible
`f ∈ 𝔽_p[x]` of positive degree `n` splits completely in `GaloisField p n`. -/
theorem Fq_irred_splits
    (f : (ZMod p)[X]) (hf : Irreducible f) (hn : f.natDegree ≠ 0) :
    (f.map (algebraMap (ZMod p) (GaloisField p f.natDegree))).Splits :=
  irred_splits_in_𝔽q p f hf hn

end Corollary_3_10

section Definition_3_16

variable (p : ℕ) [Fact p.Prime]

open Polynomial

/-- The `i`-th Conway coefficient of an order polynomial `f` from
Definition 3.16: take `(-1)^(deg f - i)·coeff_i(f)` and reduce to a
natural number in `[0, p)`. -/
noncomputable def conwayCoeff (f : (ZMod p)[X]) (i : ℕ) : ℕ :=
  ZMod.val ((-1 : ZMod p) ^ (f.natDegree - i) * f.coeff i)

/-- The strict lexicographic order on Conway coefficients used to compare two
order polynomials of the same degree, per Definition 3.16. -/
def conwayLT (f g : (ZMod p)[X]) : Prop :=
  ∃ k : ℕ, k < f.natDegree ∧
    conwayCoeff p f k < conwayCoeff p g k ∧
    ∀ j : ℕ, j < k → conwayCoeff p f j = conwayCoeff p g j

/-- Conway compatibility (Definition 3.16): for every proper divisor `m ∣ n`
and every root `α` of `fam m`, `f(α^(n/m)) = 0` holds in the algebraic
closure of `𝔽_p`. -/
def ConwayCompatible
    (fam : ∀ m : ℕ, 0 < m → (ZMod p)[X]) (n : ℕ) (f : (ZMod p)[X]) : Prop :=
  ∀ m : ℕ, ∀ (hm : 0 < m), m < n → m ∣ n →
    ∀ α : AlgebraicClosure (ZMod p),
      (((fam m hm).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot α) →
        ((f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot (α ^ (n / m)))

/-- A family `fam : ∀ n > 0, 𝔽_p[X]` is a Conway polynomial system if it
satisfies the recursive definition (Definition 3.16): the degree-one case is
`X - r` for the least primitive root `r`; each higher polynomial is primitive,
has the right degree, is compatible with smaller members, and is minimal under
the Conway lex order among such primitives. -/
structure IsConwayPolynomialSystem
    (fam : ∀ n : ℕ, 0 < n → (ZMod p)[X]) : Prop where
  degree_one : ∃ (r : ℕ), 0 < r ∧ r < p ∧
    orderOf ((r : ZMod p) : ZMod p) = p - 1 ∧
    (∀ s : ℕ, 0 < s → s < r → orderOf ((s : ZMod p) : ZMod p) ≠ p - 1) ∧
    fam 1 (by omega) = X - C (r : ZMod p)
  isPrimitive : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    (fam n hn).IsPrimitivePolynomial p
  hasDegree : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n → (fam n hn).natDegree = n
  compatible : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ConwayCompatible p (fun m hm => fam m hm) n (fam n hn)
  isLeast : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ∀ g : (ZMod p)[X],
      g.IsPrimitivePolynomial p → g.natDegree = n →
      ConwayCompatible p (fun m hm => fam m hm) n g →
      ¬ conwayLT p g (fam n hn)


end Definition_3_16

section Theorem_3_15

open Polynomial IntermediateField

/-- Auxiliary lemma for Theorem 3.15: for an integral element `α` of `E/F`,
the order of `AdjoinRoot.root (minpoly F α)` equals `orderOf α`, via the
ring isomorphism between `F[x]/(minpoly α)` and `F(α)`. -/
lemma orderOf_adjoinRoot_root_eq_orderOf (F : Type*) [Field F]
    (E : Type*) [Field E] [Algebra F E]
    (α : E) (hint : IsIntegral F α) :
    orderOf (AdjoinRoot.root (minpoly F α)) = orderOf α := by
  let e := adjoinRootEquivAdjoin F hint
  let incl : ↥(F⟮α⟯) →+* E := (IntermediateField.val (F⟮α⟯)).toRingHom
  let φ : AdjoinRoot (minpoly F α) →+* E := incl.comp e.toRingEquiv.toRingHom
  have hφ_inj : Function.Injective φ := by
    intro x y h; exact e.toRingEquiv.injective (Subtype.val_injective h)
  have hφ_root : φ (AdjoinRoot.root (minpoly F α)) = α := by
    show incl (e (AdjoinRoot.root (minpoly F α))) = α
    rw [adjoinRootEquivAdjoin_apply_root]; rfl
  conv_rhs => rw [← hφ_root]
  exact (orderOf_injective φ.toMonoidHom hφ_inj _).symm

/-- Theorem 3.15 (existence half): for every prime `p` and positive `n`,
there exists a primitive polynomial of degree `n` in `𝔽_p[x]`. The
construction takes the minimal polynomial of a generator of `(𝔽_{p^n})ˣ`. -/
theorem primitive_poly_exists (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ∃ f : (ZMod p)[X], f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : IsCyclic (GaloisField p n)ˣ := inferInstance

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  set α := (g : GaloisField p n) with hα
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  set f := minpoly (ZMod p) α with hf_def

  have hf_monic : f.Monic := minpoly.monic hint
  have hf_irred : Irreducible f := minpoly.irreducible hint

  have htop : (ZMod p)⟮α⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    by_cases hx : x = 0
    · rw [hx]; exact (ZMod p)⟮α⟯.zero_mem
    · obtain ⟨m, hm⟩ := hg (Units.mk0 x hx)
      have : x = α ^ m := by
        have h := congr_arg Units.val hm.symm
        simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h
        exact h
      rw [this]
      exact zpow_mem (mem_adjoin_simple_self (ZMod p) (E := GaloisField p n) α) m

  have hf_deg : f.natDegree = n := by
    have h1 := adjoin.finrank hint
    have h2 : Module.finrank (ZMod p) ↥(ZMod p)⟮α⟯ =
        Module.finrank (ZMod p) (GaloisField p n) := by
      rw [htop]
      exact (IntermediateField.topEquiv (F := ZMod p)
        (E := GaloisField p n)).toLinearEquiv.finrank_eq
    rw [GaloisField.finrank p hn.ne'] at h2
    linarith

  have hf_order : orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
    rw [hf_deg, orderOf_adjoinRoot_root_eq_orderOf (ZMod p) (GaloisField p n) α hint]

    have hord : orderOf α = orderOf g := by
      change orderOf ((Units.coeHom (GaloisField p n)) g) = orderOf g
      exact orderOf_injective (Units.coeHom _) Units.val_injective g
    rw [hord, orderOf_eq_card_of_forall_mem_zpowers hg]
    rw [Nat.card_units, GaloisField.card p n hn.ne']
  exact ⟨f, ⟨hf_monic, hf_irred, hf_order⟩, hf_deg⟩

/-- Generic counting lemma: if `f : A → B` has every fibre of cardinality `k`,
then `|A| = k · |B|`. Used in counting primitive polynomials in
Theorem 3.15. -/
lemma nat_card_eq_mul_of_const_fiber {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (k : ℕ)
    (hfib : ∀ b : B, Nat.card {a : A // f a = b} = k) :
    Nat.card A = k * Nat.card B := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype B := Fintype.ofFinite B
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp_rw [hfib]; simp [Finset.sum_const, smul_eq_mul, mul_comm]

/-- If `g` is a unit of `𝔽_{p^n}` of order `p^n - 1`, then `g` generates the
multiplicative group of `𝔽_{p^n}` and `𝔽_p(g) = 𝔽_{p^n}`. -/
lemma adjoin_top_of_unit_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    (ZMod p)⟮(g : GaloisField p n)⟯ = ⊤ := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n)
  rw [eq_top_iff]; intro x _
  by_cases hx : x = 0
  · rw [hx]; exact (ZMod p)⟮α⟯.zero_mem
  · have hord_u : orderOf g = Fintype.card (GaloisField p n)ˣ := by
      rw [hg, Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p n hn.ne']
    have hgen : Subgroup.zpowers g = ⊤ := by
      have := @Fintype.card_zpowers (GaloisField p n)ˣ _ _ g
      rw [hord_u] at this; apply Subgroup.eq_top_of_card_eq
      rw [← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card]; exact this
    obtain ⟨k, hk⟩ := show Units.mk0 x hx ∈ Subgroup.zpowers g by rw [hgen]; trivial
    have : x = α ^ k := by
      have h := congr_arg Units.val hk
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h; exact h.symm
    rw [this]
    exact zpow_mem (mem_adjoin_simple_self (ZMod p) (E := GaloisField p n) α) k

/-- If `g` is a generator of `(𝔽_{p^n})ˣ`, then its minimal polynomial over
`𝔽_p` is a primitive polynomial of degree `n` (cf. Theorem 3.15). -/
lemma generator_minpoly_is_prim (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    let f := minpoly (ZMod p) (g : GaloisField p n)
    f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n); set f := minpoly (ZMod p) α
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  have htop := adjoin_top_of_unit_generator p n hn g hg
  have hord_α : orderOf α = p ^ n - 1 := by
    change orderOf ((Units.coeHom _) g) = _
    rw [orderOf_injective (Units.coeHom _) Units.val_injective g, hg]
  have hf_deg : f.natDegree = n := by
    have h1 := adjoin.finrank hint
    have h2 : Module.finrank (ZMod p) ↥(ZMod p)⟮α⟯ = n := by
      rw [htop,
        (IntermediateField.topEquiv (F := ZMod p)
          (E := GaloisField p n)).toLinearEquiv.finrank_eq]
      exact GaloisField.finrank p hn.ne'
    linarith
  refine ⟨⟨minpoly.monic hint, minpoly.irreducible hint, ?_⟩, hf_deg⟩
  rw [hf_deg, orderOf_adjoinRoot_root_eq_orderOf (ZMod p) (GaloisField p n) α hint, hord_α]

/-- The set of primitive polynomials of degree `n` in `𝔽_p[x]` is finite: a
primitive polynomial of degree `n` is determined by its `n` lower coefficients
in `𝔽_p`, of which there are finitely many. -/
instance finite_primitivePolys (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    Finite {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} := by
  apply Finite.of_injective
    (fun (⟨f, ⟨hm, _, _⟩, _⟩ :
      {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n}) =>
      (fun (i : Fin n) => f.coeff i.val : Fin n → ZMod p))
  intro ⟨f, ⟨hfm, _, _⟩, hfn⟩ ⟨g, ⟨hgm, _, _⟩, hgn⟩ h
  simp only [Subtype.mk.injEq]; ext i
  by_cases hi : i < n
  · exact congr_fun h ⟨i, hi⟩
  · by_cases hi2 : i = n
    · have h1 : f.coeff i = 1 := by rw [hi2, ← hfn]; exact hfm.leadingCoeff
      have h2 : g.coeff i = 1 := by rw [hi2, ← hgn]; exact hgm.leadingCoeff
      rw [h1, h2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < i)]

/-- In a cyclic group `(𝔽_{p^n})ˣ` of order `p^n - 1`, the number of
generators is `φ(p^n - 1)` (Euler totient), the standard counting fact. -/
lemma card_generators_eq_totient (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    Nat.card {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} =
    Nat.totient (p ^ n - 1) := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
  have hcu : Fintype.card (GaloisField p n)ˣ = p ^ n - 1 := by
    rw [Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p n hn.ne']
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
      IsCyclic.card_orderOf_eq_totient (by rw [hcu])]

/-- The map from multiplicative generators of `𝔽_{p^n}` to primitive
polynomials of degree `n`, sending `g` to its minimal polynomial over `𝔽_p`. -/
noncomputable def minpoly_of_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1}) :
    {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} :=
  ⟨minpoly (ZMod p) (g.1 : GaloisField p n),
   generator_minpoly_is_prim p n hn g.1 g.2⟩

/-- Each primitive polynomial of degree `n` is the minimal polynomial of
exactly `n` generators of `(𝔽_{p^n})ˣ` (its `n` Galois conjugates). -/
theorem minpoly_fiber_card (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (f : {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n}) :
    Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} = n := by
  classical

  obtain ⟨hm, hirr, hord_root⟩ := f.2.1
  have hdeg := f.2.2
  have hfne : f.val ≠ 0 := hm.ne_zero
  haveI : Fact (Irreducible f.val) := ⟨hirr⟩

  haveI : Module.Finite (ZMod p) (AdjoinRoot f.val) := (AdjoinRoot.powerBasis hfne).finite
  haveI : Finite (AdjoinRoot f.val) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot f.val) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f.val) = n := by
    rw [(AdjoinRoot.powerBasis hfne).finrank, AdjoinRoot.powerBasis_dim]; exact hdeg
  have hcard : Fintype.card (AdjoinRoot f.val) = p ^ n := by
    rw [← FiniteField.pow_finrank_eq_card p (AdjoinRoot f.val), hfr]
  let e := GaloisField.algEquivGaloisFieldOfFintype p n hcard

  let α₀ : GaloisField p n := e (AdjoinRoot.root f.val)

  have hα₀_root : Polynomial.aeval α₀ f.val = 0 := by
    simp [α₀, aeval_algHom_apply]

  have hint : IsIntegral (ZMod p) α₀ := Algebra.IsIntegral.isIntegral α₀
  have hminpoly : minpoly (ZMod p) α₀ = f.val :=
    (minpoly.eq_of_irreducible_of_monic hirr hα₀_root hm).symm

  have hα₀_ord : orderOf α₀ = p ^ n - 1 := by
    show orderOf (e (AdjoinRoot.root f.val)) = p ^ n - 1
    have h_eq : orderOf (e (AdjoinRoot.root f.val)) = orderOf (AdjoinRoot.root f.val) :=
      MulEquiv.orderOf_eq e.toMulEquiv (AdjoinRoot.root f.val)
    rw [h_eq]; rwa [hdeg] at hord_root

  have hpn_pos : 0 < p ^ n - 1 := by
    have := Fact.out (self := ‹Fact p.Prime›); have : 1 < p ^ n := Nat.one_lt_pow hn.ne' this.one_lt
    omega
  have hα₀_ne : α₀ ≠ 0 := by intro h; rw [h, orderOf_zero] at hα₀_ord; omega

  let g₀ : (GaloisField p n)ˣ := Units.mk0 α₀ hα₀_ne
  have hg₀_val : (g₀ : GaloisField p n) = α₀ := rfl
  have hg₀_ord : orderOf g₀ = p ^ n - 1 := by
    rw [show orderOf g₀ = orderOf (g₀ : GaloisField p n) from
      (orderOf_injective (Units.coeHom _) Units.val_injective g₀).symm, hg₀_val, hα₀_ord]
  have htop : (ZMod p)⟮α₀⟯ = ⊤ := adjoin_top_of_unit_generator p n hn g₀ hg₀_ord

  let g₀_sub : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} := ⟨g₀, hg₀_ord⟩
  have hg₀_fib : minpoly_of_generator p n hn g₀_sub = f := Subtype.ext hminpoly

  have hGal_card : Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) = n := by
    rw [IsGalois.card_aut_eq_finrank]; exact GaloisField.finrank p hn.ne'

  have alg_inj : ∀ σ τ : GaloisField p n ≃ₐ[ZMod p] GaloisField p n,
      σ α₀ = τ α₀ → σ = τ := by
    intro σ τ h
    have hsubalg : Algebra.adjoin (ZMod p) ({α₀} : Set (GaloisField p n)) = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.isAlgebraic hint), htop]
      exact top_toSubalgebra
    ext y; exact DFunLike.congr_fun
      (AlgHom.ext_of_adjoin_eq_top hsubalg (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
        (fun z hz => by simp only [Set.mem_singleton_iff] at hz; subst hz; exact h)) y

  let fwd : (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) →
      {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
        minpoly_of_generator p n hn g = f} := fun σ =>
    ⟨⟨Units.mk0 (σ α₀) (by intro h; exact hα₀_ne (σ.injective (by rwa [map_zero]))),
      by rw [show orderOf (Units.mk0 (σ α₀) _) = orderOf (σ α₀) from
          (orderOf_injective (Units.coeHom _) Units.val_injective _).symm]
         exact (MulEquiv.orderOf_eq σ.toMulEquiv α₀).trans hα₀_ord⟩,
     Subtype.ext (show minpoly (ZMod p) (σ α₀) = f.val from by
       rw [show minpoly (ZMod p) (σ α₀) = minpoly (ZMod p) α₀ from by
         rw [Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]; exact ⟨σ, rfl⟩]
       exact hminpoly)⟩
  have hfwd_inj : Function.Injective fwd := by
    intro σ τ h
    have heq : (σ α₀ : GaloisField p n) = (τ α₀ : GaloisField p n) := by
      have := congr_arg (fun g => (g.val.val : GaloisField p n)) h
      exact this
    exact alg_inj σ τ heq

  let bwd : {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} →
      (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := fun g => by
    have hg_minpoly : minpoly (ZMod p) (g.val.val : GaloisField p n) = f.val :=
      congr_arg Subtype.val g.2
    have hg_orbit : (g.val.val : GaloisField p n) ∈
        MulAction.orbit (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) α₀ := by
      rw [← Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]
      rw [hg_minpoly, hminpoly]
    exact hg_orbit.choose
  have hbwd_spec : ∀ g, bwd g • α₀ = (g.val.val : GaloisField p n) := by
    intro g
    exact (by
      have hg_minpoly : minpoly (ZMod p) (g.val.val : GaloisField p n) = f.val :=
        congr_arg Subtype.val g.2
      have hg_orbit : (g.val.val : GaloisField p n) ∈
          MulAction.orbit (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) α₀ := by
        rw [← Normal.minpoly_eq_iff_mem_orbit (GaloisField p n)]
        rw [hg_minpoly, hminpoly]
      exact hg_orbit.choose_spec)
  have hbwd_inj : Function.Injective bwd := by
    intro g₁ g₂ h
    have h1 := hbwd_spec g₁
    have h2 := hbwd_spec g₂
    rw [h] at h1
    have : (g₁.val.val : GaloisField p n) = (g₂.val.val : GaloisField p n) := by
      rw [← h1, ← h2]
    have h_val1 : g₁.val.val = g₂.val.val := Units.ext this
    exact Subtype.ext (Subtype.ext h_val1)

  haveI : Finite (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := by
    exact Nat.finite_of_card_ne_zero (by rw [hGal_card]; omega)
  haveI : Finite {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} := by
    exact Finite.of_injective bwd hbwd_inj

  have h_le : Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} ≤ n := by
    calc Nat.card _ ≤ Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) :=
          Nat.card_le_card_of_injective bwd hbwd_inj
      _ = n := hGal_card
  have h_ge : n ≤ Nat.card {g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1} //
      minpoly_of_generator p n hn g = f} := by
    calc n = Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := hGal_card.symm
      _ ≤ Nat.card _ := Nat.card_le_card_of_injective fwd hfwd_inj
  omega

/-- Theorem 3.15 (counting half): the number of primitive polynomials of
degree `n` in `𝔽_p[x]` is `φ(p^n - 1) / n`. -/
theorem primitive_poly_count (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    Nat.card {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} =
    Nat.totient (p ^ n - 1) / n := by

  have hmul := nat_card_eq_mul_of_const_fiber (minpoly_of_generator p n hn) n
    (minpoly_fiber_card p n hn)
  rw [card_generators_eq_totient p n hn] at hmul

  rw [Nat.eq_div_iff_mul_eq_left (by omega) ⟨_, hmul⟩]
  linarith

end Theorem_3_15
