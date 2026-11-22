/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section

open MvPolynomial Finsupp

namespace HomogeneousPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- A multivariate polynomial $f$ is homogeneous of degree $d$ if every monomial
in $f$ has total degree $d$. Abbreviation for Mathlib's `MvPolynomial.IsHomogeneous`. -/
abbrev IsHomogeneousOfDegree (f : MvPolynomial σ R) (d : ℕ) : Prop :=
  f.IsHomogeneous d

/-- A polynomial $f$ is homogeneous if it is homogeneous of some degree
$d \in \mathbb{N}$. -/
def IsHomogeneous (f : MvPolynomial σ R) : Prop :=
  ∃ d : ℕ, f.IsHomogeneous d


/-- Homogeneity under scaling: if $f$ is homogeneous of degree $d$, then
$f(c x_1, \ldots, c x_n) = c^d \cdot f(x_1, \ldots, x_n)$ for every scalar
$c$. -/
theorem isHomogeneous_eval_smul (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsHomogeneous d)
    (c : R) (x : σ → R) :
    eval (fun i => c * x i) f = c ^ d * eval x f := by
  rw [f.as_sum, map_sum, map_sum, Finset.mul_sum]
  congr 1
  ext s
  simp only [eval_monomial]
  by_cases hs : coeff s f = 0
  · simp [hs]
  · have hdeg : s.degree = d := by
      rw [degree_eq_weight_one]; exact hf hs
    simp only [prod]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    rw [← hdeg, degree_apply, ← Finset.prod_pow_eq_pow_sum]
    ring


/-- The zero polynomial is homogeneous (of every degree, witnessed here by any
chosen $d$). -/
theorem isHomogeneous_zero (d : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) :=
  ⟨d, MvPolynomial.isHomogeneous_zero σ R d⟩

/-- A constant polynomial $C(r)$ is homogeneous of degree $0$. -/
theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) :=
  ⟨0, MvPolynomial.isHomogeneous_C σ r⟩

/-- Each variable $X_i$ is homogeneous of degree $1$. -/
theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) :=
  ⟨1, MvPolynomial.isHomogeneous_X R i⟩


/-- Decomposition into homogeneous components: every polynomial $f$ is the
sum of its homogeneous components $f = \sum_{i \le \deg f} f_i$. -/
theorem sum_homogeneousComponent (f : MvPolynomial σ R) :
    ∑ i ∈ Finset.range (f.totalDegree + 1), homogeneousComponent i f = f :=
  MvPolynomial.sum_homogeneousComponent f

end HomogeneousPolynomial

namespace HomogeneousIdealDef

variable (σ : Type*) (R : Type*) [CommSemiring R] [DecidableEq σ]


attribute [local instance] MvPolynomial.gradedAlgebra

/-- An ideal $I \subseteq R[X_1, \ldots, X_n]$ is homogeneous if every $f \in I$
has all of its homogeneous components in $I$. -/
abbrev IsHomogeneousIdeal (I : Ideal (MvPolynomial σ R)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ R)


end HomogeneousIdealDef

end

open scoped LinearAlgebra.Projectivization

namespace AffinePatch

variable {n : ℕ} (k : Type*) [Field k]

/-- Well-defined predicate on a projective point $p \in \mathbb{P}^n(k)$: "the
$i$-th coordinate of any representative of $p$ is nonzero". -/
def Projectivization.coordNeZero (i : Fin (n + 1)) : ℙ k (Fin (n + 1) → k) → Prop :=
  Projectivization.lift
    (fun v => (v : Fin (n + 1) → k) i ≠ 0)
    (by
      intro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      simp only at hab ⊢
      have heq : a i = t * b i := by
        have := congr_fun hab i; simp [Pi.smul_apply, smul_eq_mul] at this; exact this
      have ht : t ≠ 0 := by intro h; apply ha; rw [hab]; simp [h]
      exact propext ⟨fun hai hbi => hai (by rw [heq, hbi, mul_zero]),
                     fun hbi hai => hbi (by rwa [heq, mul_eq_zero, or_iff_right ht] at hai)⟩)

/-- The standard affine patch $U_i = \{[x_0 : \cdots : x_n] \in \mathbb{P}^n(k)
\mid x_i \neq 0\}$. -/
def affinePatch (i : Fin (n + 1)) : Set (ℙ k (Fin (n + 1) → k)) :=
  {p | Projectivization.coordNeZero k i p}

/-- Membership criterion in the patch $U_i$ in terms of an explicit
representative $v \neq 0$. -/
@[simp]
lemma mem_affinePatch_mk (i : Fin (n + 1)) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ affinePatch k i ↔ v i ≠ 0 := by
  simp [affinePatch, Projectivization.coordNeZero]

/-- A projective point $p$ lies in $U_i$ iff its canonical representative
`p.rep` has nonzero $i$-th coordinate. -/
lemma mem_affinePatch_iff_rep (i : Fin (n + 1)) (p : ℙ k (Fin (n + 1) → k)) :
    p ∈ affinePatch k i ↔ p.rep i ≠ 0 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [mem_affinePatch_mk]

/-- Inserting a $1$ at index $i$ produces a nonzero tuple. -/
lemma insertNth_one_ne_zero (i : Fin (n + 1)) (a : Fin n → k) :
    i.insertNth (α := fun _ => k) (1 : k) a ≠ 0 := by
  intro h
  have : i.insertNth (α := fun _ => k) (1 : k) a i = (0 : Fin (n + 1) → k) i := congr_fun h i
  simp [Fin.insertNth_apply_same] at this

/-- The canonical bijection $U_i \simeq \mathbb{A}^n(k)$ sending the projective
point $[x_0 : \cdots : x_n]$ with $x_i \neq 0$ to the affine point
$(x_0 / x_i, \ldots, \widehat{x_i / x_i}, \ldots, x_n / x_i)$. -/
noncomputable def affinePatchEquiv (i : Fin (n + 1)) : affinePatch k i ≃ (Fin n → k) where
  toFun := fun ⟨p, _⟩ => fun j => p.rep (i.succAbove j) / p.rep i
  invFun := fun a => ⟨Projectivization.mk k (i.insertNth (α := fun _ => k) 1 a)
    (insertNth_one_ne_zero k i a),
    by rw [mem_affinePatch_mk]; simp [Fin.insertNth_apply_same]⟩
  left_inv := by
    rintro ⟨p, hp⟩
    simp only [Subtype.mk.injEq]
    have hi : p.rep i ≠ 0 := (mem_affinePatch_iff_rep k i p).mp hp
    conv_rhs => rw [← Projectivization.mk_rep p]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(p.rep i)⁻¹, ?_⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi]
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  right_inv := by
    intro a
    funext j
    simp only
    set p := Projectivization.mk k (i.insertNth (α := fun _ => k) 1 a)
      (insertNth_one_ne_zero k i a)
    have hmk := Projectivization.mk_rep p
    rw [Projectivization.mk_eq_mk_iff] at hmk
    obtain ⟨c, hc⟩ := hmk
    have hsmul : ∀ l : Fin (n + 1),
        p.rep l = ↑c * (i.insertNth (α := fun _ => k) 1 a) l := by
      intro l
      have := congr_fun hc l
      simp only [Pi.smul_apply, Units.smul_def] at this
      exact this.symm
    have hrj : p.rep (i.succAbove j) = ↑c * a j := by
      rw [hsmul, Fin.insertNth_apply_succAbove]
    have hri : p.rep i = ↑c := by
      rw [hsmul, Fin.insertNth_apply_same, mul_one]
    rw [hrj, hri]
    exact mul_div_cancel_left₀ (a j) (Units.ne_zero c)

end AffinePatch

noncomputable section

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace ProjectiveClosure

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- Homogenization with respect to a new variable $X_0$: given
$f \in R[X_1, \ldots, X_n]$ of degree $d$, produce the homogeneous polynomial
$X_0^d f(X_1 / X_0, \ldots, X_n / X_0) \in R[X_0, X_1, \ldots, X_n]$. -/
def homogenize (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  let d := f.totalDegree
  f.support.sum fun m =>
    MvPolynomial.monomial
      (m.mapDomain Fin.succ + Finsupp.single 0 (d - (m.sum fun _ e => e)))
      (MvPolynomial.coeff m f)

/-- Unfolding lemma exposing the definition of `homogenize` as a sum over the
support of $f$. -/
lemma homogenize_def (f : MvPolynomial (Fin n) R) :
    homogenize f = f.support.sum fun m =>
      MvPolynomial.monomial
        (m.mapDomain Fin.succ + Finsupp.single 0 (f.totalDegree - (m.sum fun _ e => e)))
        (MvPolynomial.coeff m f) :=
  rfl


/-- Image of an ideal $I$ under homogenization, as a set of homogeneous
polynomials in $R[X_0, \ldots, X_n]$. -/
def homogenizeSet (I : Ideal (MvPolynomial (Fin n) R)) :
    Set (MvPolynomial (Fin (n + 1)) R) :=
  homogenize '' (I : Set (MvPolynomial (Fin n) R))

/-- Homogenization of the ideal $I$: the ideal of $R[X_0, \ldots, X_n]$
generated by all homogenizations of elements of $I$. -/
def homogenizeIdeal (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (homogenizeSet I)


/-- The homogenization of any element $f \in I$ belongs to the homogenized
ideal `homogenizeIdeal I`. -/
lemma homogenize_mem_homogenizeIdeal {I : Ideal (MvPolynomial (Fin n) R)}
    {f : MvPolynomial (Fin n) R} (hf : f ∈ I) :
    homogenize f ∈ homogenizeIdeal I :=
  Ideal.subset_span ⟨f, hf, rfl⟩

variable (k : Type*) [Field k]

/-- $f$ vanishes at the projective point $p$ if $f(p_{\mathrm{rep}}) = 0$
on (any) representative. -/
def projectiveVanishes (f : MvPolynomial (Fin (n + 1)) k)
    (p : ℙ k (Fin (n + 1) → k)) : Prop :=
  MvPolynomial.eval p.rep f = 0

/-- Projective zero locus of a set of polynomials:
$V_+(S) = \{ p \in \mathbb{P}^n(k) \mid f(p) = 0 \text{ for all } f \in S\}$. -/
def projectiveZeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {p | ∀ f ∈ S, projectiveVanishes k f p}


/-- The projective zero locus is order-reversing: $S \subseteq T$ implies
$V_+(T) \subseteq V_+(S)$. -/
lemma projectiveZeroLocus_anti {S T : Set (MvPolynomial (Fin (n + 1)) k)} (h : S ⊆ T) :
    projectiveZeroLocus k T ⊆ projectiveZeroLocus k S :=
  fun _ hp f hf => hp f (h hf)

/-- The projective closure of the affine variety $V(I)$: the zero locus of the
homogenized ideal `homogenizeIdeal I` inside $\mathbb{P}^n(k)$. -/
def projectiveClosure (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  projectiveZeroLocus k (homogenizeIdeal I : Set _)


/-- Projective closure of an arbitrary set $Z \subseteq \mathbb{A}^n(k)$:
defined as the projective closure of the affine vanishing ideal of $Z$. -/
def projectiveClosureOfSet (Z : Set (Fin n → k)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  projectiveClosure k (MvPolynomial.vanishingIdeal k Z)


end ProjectiveClosure

end

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace AffineParts

variable {n : ℕ} (k : Type*) [Field k]

/-- Dehomogenization with respect to the variable $X_i$: the ring
homomorphism $R[X_0, \ldots, X_n] \to R[X_0, \ldots, \widehat{X_i}, \ldots, X_n]$
which sends $X_i \mapsto 1$. -/
def dehomogenize (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) k →+* MvPolynomial (Fin n) k :=
  eval₂Hom C (i.insertNth (1 : MvPolynomial (Fin n) k) (fun l => X l))


/-- Projective zero locus restricted to homogeneous polynomials: a projective
point $p$ lies in $V_+(S)$ iff every homogeneous $f \in S$ vanishes at any
representative of $p$. -/
def projectiveZeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {p | ∀ f ∈ S, ∀ d, f.IsHomogeneous d → eval p.rep f = 0}

/-- Affine part of a projective set $V$ in the chart $U_i$: simply
$V \cap U_i$. -/
def affinePart (V : Set (ℙ k (Fin (n + 1) → k))) (i : Fin (n + 1)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  V ∩ AffinePatch.affinePatch k i

/-- Image of an ideal $I$ under dehomogenization at index $i$: the ideal of
$R[X_0, \ldots, \widehat{X_i}, \ldots, X_n]$ obtained from $I$ by setting
$X_i = 1$. -/
def dehomogenizedIdeal (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (i : Fin (n + 1)) :
    Ideal (MvPolynomial (Fin n) k) :=
  I.map (dehomogenize k i)


/-- Affine zero locus in the chart $U_i$: an affine point $a$ lies in the
locus iff every homogeneous $f \in S$ vanishes after dehomogenization at
$X_i$. -/
def affinePartZeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) (i : Fin (n + 1)) :
    Set (Fin n → k) :=
  {a | ∀ f ∈ S, ∀ d, f.IsHomogeneous d → eval a (dehomogenize k i f) = 0}


end AffineParts

end

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace ProjectiveVanishingIdeal

variable {n : ℕ} (k : Type*) [Field k]


attribute [local instance] MvPolynomial.gradedAlgebra

/-- Set of homogeneous polynomials vanishing on a projective subset $Z$. -/
def homogVanishingSet (Z : Set (ℙ k (Fin (n + 1) → k))) :
    Set (MvPolynomial (Fin (n + 1)) k) :=
  {f | (∃ d, f.IsHomogeneous d) ∧ ∀ p ∈ Z, eval p.rep f = 0}

/-- Projective vanishing ideal $I_+(Z) \subseteq k[X_0, \ldots, X_n]$: the
homogeneous ideal generated by all homogeneous polynomials vanishing on $Z$. -/
def projectiveVanishingIdeal (Z : Set (ℙ k (Fin (n + 1) → k))) :
    Ideal (MvPolynomial (Fin (n + 1)) k) :=
  Ideal.span (homogVanishingSet k Z)


end ProjectiveVanishingIdeal

end

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace ProjectiveVarietyDef

variable {n : ℕ} (k : Type*) [Field k]

/-- Definition 13.21 (projective algebraic set). The zero locus of a set $S$ of
polynomials in $\mathbb{P}^n(k)$, considering only the homogeneous elements
of $S$. -/
def ProjectiveAlgebraicSet (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {p | ∀ f ∈ S, ∀ d, f.IsHomogeneous d → eval p.rep f = 0}


/-- A subset $Z \subseteq \mathbb{P}^n(k)$ is *projective algebraic* if it
arises as the projective zero locus of some set $S$ of polynomials. -/
def IsProjectiveAlgebraicSubset (Z : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∃ S : Set (MvPolynomial (Fin (n + 1)) k), Z = ProjectiveAlgebraicSet k S


/-- A projective algebraic set $Z$ is *irreducible* if it is nonempty and
cannot be written as a union $Z = Z_1 \cup Z_2$ of two proper projective
algebraic subsets. -/
def IsIrreducibleProjectiveAlgebraicSet (Z : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  Z.Nonempty ∧
    ∀ Z₁ Z₂ : Set (ℙ k (Fin (n + 1) → k)),
      IsProjectiveAlgebraicSubset k Z₁ → IsProjectiveAlgebraicSubset k Z₂ →
      Z = Z₁ ∪ Z₂ → Z₁ = Z ∨ Z₂ = Z


/-- A *projective variety* is an irreducible projective algebraic subset of
$\mathbb{P}^n(k)$. -/
def IsProjectiveVariety (V : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  IsProjectiveAlgebraicSubset k V ∧ IsIrreducibleProjectiveAlgebraicSet k V


/-- A projective variety is irreducible. -/
lemma IsProjectiveVariety.isIrreducible
    {V : Set (ℙ k (Fin (n + 1) → k))} (hV : IsProjectiveVariety k V) :
    IsIrreducibleProjectiveAlgebraicSet k V :=
  hV.2

/-- A projective variety is nonempty. -/
lemma IsProjectiveVariety.nonempty
    {V : Set (ℙ k (Fin (n + 1) → k))} (hV : IsProjectiveVariety k V) :
    V.Nonempty :=
  hV.2.1

end ProjectiveVarietyDef

end

noncomputable section

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Theorem1323

variable {n : ℕ} (k : Type*) [Field k]

/-- Evaluating a single homogenized monomial at $(1, P_1, \ldots, P_n)$ yields
$c \prod_i P_i^{m_i}$, the corresponding affine monomial value. -/
lemma eval_single_homogenized_monomial (m : Fin n →₀ ℕ) (c : k) (d : ℕ)
    (P : Fin n → k) :
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P)
      (monomial (m.mapDomain Fin.succ + single 0 (d - m.sum fun _ e => e)) c) =
    c * m.prod (fun i e => P i ^ e) := by
  rw [eval_monomial, prod_add_index (by simp) (by intros; rw [pow_add]),
      prod_mapDomain_index (by simp) (by intros; rw [pow_add]),
      prod_single_index (by simp)]
  simp [Fin.insertNth_apply_same, one_pow]

/-- Key compatibility: evaluating the homogenization $F = \tilde f$ at
$(1, P_1, \ldots, P_n)$ recovers the affine evaluation $f(P)$. -/
theorem eval_homogenize_at_one_cons (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P)
      (ProjectiveClosure.homogenize f) =
    eval P f := by
  simp only [ProjectiveClosure.homogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  congr 1; ext m
  rw [eval_single_homogenized_monomial, eval_monomial]

/-- Composing dehomogenization-at-$X_0$ with affine evaluation at $P$ equals
projective evaluation at $(1, P)$. -/
lemma eval_comp_dehomogenize_eq (P : Fin n → k) :
    (eval P).comp (AffineParts.dehomogenize k (0 : Fin (n + 1))) =
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P) := by
  apply ringHom_ext
  · intro a; simp [AffineParts.dehomogenize]
  · intro j
    simp only [RingHom.comp_apply, AffineParts.dehomogenize, eval₂Hom_X']
    by_cases hj : j = (0 : Fin (n + 1))
    · subst hj; simp [Fin.insertNth_apply_same]
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj; simp

/-- Pointwise version of `eval_comp_dehomogenize_eq`. -/
lemma eval_dehomogenize_eq (g : MvPolynomial (Fin (n + 1)) k) (P : Fin n → k) :
    eval P (AffineParts.dehomogenize k (0 : Fin (n + 1)) g) =
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g := by
  rw [← RingHom.comp_apply, eval_comp_dehomogenize_eq]

/-- Dehomogenization of the homogenized monomial $X_0^e \cdot X_1^{m_1} \cdots
X_n^{m_n}$ at $X_0$ recovers the affine monomial $X_1^{m_1} \cdots X_n^{m_n}$. -/
lemma dehomogenize_monomial_mapDomain_succ (m : Fin n →₀ ℕ) (c : k) (e : ℕ) :
    AffineParts.dehomogenize k (0 : Fin (n + 1))
      (monomial (m.mapDomain Fin.succ + Finsupp.single 0 e) c) =
    monomial m c := by
  simp only [AffineParts.dehomogenize]
  rw [eval₂Hom_monomial,
      prod_add_index (by simp) (by intros; rw [pow_add]),
      prod_single_index (by simp),
      prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  simp only [Fin.insertNth_apply_same, one_pow, mul_one]
  rw [monomial_eq]; congr 1


/-- Evaluating $\widetilde{f|_{X_0 = 1}}$ at $(1, P)$ agrees with evaluating
$f$ at $(1, P)$: on the affine patch $U_0$, homogenize-after-dehomogenize is
the identity. -/
theorem eval_homogenize_dehomogenize_eq (f : MvPolynomial (Fin (n + 1)) k) (P : Fin n → k) :
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P)
      (ProjectiveClosure.homogenize (AffineParts.dehomogenize k 0 f)) =
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f := by
  rw [eval_homogenize_at_one_cons, eval_dehomogenize_eq]

/-- If $f \in I$, then $\widetilde{f|_{X_0 = 1}}$ lies in the homogenization
of the dehomogenized image of $I$. -/
lemma homogenize_dehomogenize_mem_homogenizeIdeal
    {I : Ideal (MvPolynomial (Fin (n + 1)) k)} {f : MvPolynomial (Fin (n + 1)) k}
    (hf : f ∈ I) :
    ProjectiveClosure.homogenize (AffineParts.dehomogenize k 0 f) ∈
      ProjectiveClosure.homogenizeIdeal (I.map (AffineParts.dehomogenize k 0)) :=
  ProjectiveClosure.homogenize_mem_homogenizeIdeal (Ideal.mem_map_of_mem _ hf)

/-- Theorem 13.23. Intersecting the projective closure with the affine patch
$U_0$ recovers the original affine variety $V(I)$: the projective vanishing
set of `homogenizeIdeal I` at points $(1, P)$ equals the affine vanishing
set of $I$. -/
theorem projective_closure_cap_affine_eq
    (I : Ideal (MvPolynomial (Fin n) k)) :
    {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0} =
    {P : Fin n → k | ∀ f ∈ I, eval P f = 0} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·
    intro hP f hf
    rw [← eval_homogenize_at_one_cons]
    exact hP _ (ProjectiveClosure.homogenize_mem_homogenizeIdeal hf)
  ·
    intro hP g hg

    have hgen : ∀ s ∈ ProjectiveClosure.homogenizeSet I,
        eval ((0 : Fin (n + 1)).insertNth (1 : k) P) s = 0 := by
      rintro _ ⟨f, hf, rfl⟩
      rw [eval_homogenize_at_one_cons]
      exact hP f hf

    have hker : ProjectiveClosure.homogenizeIdeal I ≤
        RingHom.ker (eval ((0 : Fin (n + 1)).insertNth (1 : k) P)) := by
      rw [ProjectiveClosure.homogenizeIdeal]
      exact Ideal.span_le.mpr fun s hs => hgen s hs
    exact hker hg


end Theorem1323

end

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace ProjectiveDimension

variable {n : ℕ} (k : Type*) [Field k]

/-- Affine $N$-space over $\overline{k}$: tuples $(x_1, \ldots, x_N) \in
\overline{k}^N$. -/
abbrev AffinePoint (N : ℕ) : Type _ := Fin N → AlgebraicClosure k

/-- Affine zero locus of a set $S$ over $\overline{k}$: the common
$\overline{k}$-vanishing set of $S \subseteq \overline{k}[X_1, \ldots, X_N]$. -/
def zeroLocus (N : ℕ) (S : Set (MvPolynomial (Fin N) (AlgebraicClosure k))) :
    Set (AffinePoint k N) :=
  {P | ∀ f ∈ S, MvPolynomial.eval P f = 0}

/-- Vanishing ideal of a set $V \subseteq \overline{k}^N$: the ideal of
polynomials over $\overline{k}$ that vanish on every point of $V$. -/
def vanishingIdeal' (N : ℕ) (V : Set (AffinePoint k N)) :
    Ideal (MvPolynomial (Fin N) (AlgebraicClosure k)) :=
  { carrier := {f | ∀ P ∈ V, MvPolynomial.eval P f = 0}
    add_mem' := fun {a b} ha hb P hP => by simp [ha P hP, hb P hP]
    zero_mem' := fun P _ => by simp
    smul_mem' := fun c f hf P hP => by simp [hf P hP] }

/-- Coordinate ring of $V \subseteq \overline{k}^N$: the quotient
$\overline{k}[X_1, \ldots, X_N] / I(V)$. -/
abbrev coordinateRing' (N : ℕ) (V : Set (AffinePoint k N)) :=
  MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ vanishingIdeal' k N V

/-- An affine algebraic set $V$ has dimension $d$ if the Krull dimension of
its coordinate ring equals $d$. -/
def HasAffineDimension (N : ℕ) (V : Set (AffinePoint k N)) (d : ℕ) : Prop :=
  Order.krullDim (PrimeSpectrum (coordinateRing' k N V)) = ↑(d : ℕ∞)

/-- Jacobian matrix at the point $P$: the $m \times N$ matrix whose
$(i, j)$-entry is $\partial f_i / \partial X_j \,(P)$. -/
def jacobianMatrix (N m : ℕ) (f : Fin m → MvPolynomial (Fin N) (AlgebraicClosure k))
    (P : AffinePoint k N) : Matrix (Fin m) (Fin N) (AlgebraicClosure k) :=
  fun i j => MvPolynomial.eval P (MvPolynomial.pderiv j (f i))

/-- Singular locus of the system $f$: those zeros of $f$ at which the rank of
the Jacobian is strictly less than the codimension threshold $r$. -/
def singularLocus' (N m r : ℕ) (f : Fin m → MvPolynomial (Fin N) (AlgebraicClosure k)) :
    Set (AffinePoint k N) :=
  { P | P ∈ zeroLocus k N (Set.range f) ∧ (jacobianMatrix k N m f P).rank < r }

/-- Base change of an affine variety $V \subseteq k^n$ to $\overline{k}^n$ via
the canonical algebra map $k \hookrightarrow \overline{k}$. -/
def affinePartBaseChange (V : Set (Fin n → k)) : Set (AffinePoint k n) :=
  Set.image (fun (p : Fin n → k) (i : Fin n) => algebraMap k (AlgebraicClosure k) (p i)) V


/-- Coefficient lift $k[X_1, \ldots, X_N] \to \overline{k}[X_1, \ldots, X_N]$
via the canonical algebra map. -/
def liftToAlgClosure (N : ℕ) :
    MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k) :=
  MvPolynomial.map (algebraMap k (AlgebraicClosure k))

/-- Generators of the affine piece in chart $U_i$ over $\overline{k}$:
dehomogenize each $f_j$ at index $i$, then lift coefficients to
$\overline{k}$. -/
def affinePartGenerators {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (i : Fin (n + 1)) : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k) :=
  fun j => liftToAlgClosure k n (AffineParts.dehomogenize k i (f j))

/-- Zero locus over $\overline{k}$ of the affine generators in chart $U_i$. -/
def affinePartZeroLocusAlgClosed {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (i : Fin (n + 1)) : Set (AffinePoint k n) :=
  zeroLocus k n (Set.range (affinePartGenerators k f i))

/-- Projective dimension of the variety cut out by $f$: every affine chart has
dimension $\le d$, and at least one chart realizes dimension $d$. -/
def HasProjectiveDimension {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (d : ℕ) : Prop :=

  (∀ (i : Fin (n + 1)) (d_i : ℕ),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d_i →
    d_i ≤ d) ∧

  (∃ (i : Fin (n + 1)),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d)

/-- An affine piece of dimension $d$ is *smooth* when its singular locus (rank
$< n - d$) is empty. -/
def IsAffinePartSmooth {m : ℕ} (g : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (d : ℕ) : Prop :=
  singularLocus' k n m (n - d) g = ∅

/-- A projective variety is *smooth* if each of its affine charts of
dimension $d_i$ is smooth. -/
def IsProjectiveSmooth {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ (i : Fin (n + 1)) (d_i : ℕ),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d_i →
    IsAffinePartSmooth k (affinePartGenerators k f i) d_i

end ProjectiveDimension

end

noncomputable section

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Theorem1324

variable {n : ℕ} (k : Type*) [Field k]

/-- Dehomogenization at any index $i$ is a surjective ring homomorphism
$k[X_0, \ldots, X_n] \twoheadrightarrow k[X_0, \ldots, \widehat{X_i}, \ldots,
X_n]$. -/
lemma dehomogenize_surjective (i : Fin (n + 1)) :
    Function.Surjective (AffineParts.dehomogenize k i) := by
  intro f
  use (rename i.succAbove : MvPolynomial (Fin n) k →ₐ[k] _) f
  have key : (AffineParts.dehomogenize k i).comp
      ((rename i.succAbove : MvPolynomial (Fin n) k →ₐ[k] _).toRingHom) =
      RingHom.id _ := by
    apply ringHom_ext
    · intro a; simp [AffineParts.dehomogenize]
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_X, AffineParts.dehomogenize, eval₂Hom_X', Fin.insertNth_apply_succAbove,
        RingHom.id_apply]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.id_apply] at this
  exact this


/-- Theorem 13.24. For any ideal $I \subseteq k[X_0, \ldots, X_n]$, the affine
piece $\{P \mid f(1, P) = 0 \,\forall f \in I\}$ equals the affine piece of
the projective closure of $I$ dehomogenized at $X_0$ and re-homogenized. -/
theorem projective_closure_of_affinePart_eq
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    {P : Fin n → k | ∀ f ∈ I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal
        (I.map (AffineParts.dehomogenize k 0)),
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·


    intro hP g hg

    have h13_23 := Theorem1323.projective_closure_cap_affine_eq k
      (I.map (AffineParts.dehomogenize k 0))
    have hP_affine : P ∈ {P : Fin n → k |
        ∀ f ∈ I.map (AffineParts.dehomogenize k 0), eval P f = 0} := by
      intro h hh

      have : I.map (AffineParts.dehomogenize k 0) ≤ RingHom.ker (eval P) := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        simp only [Ideal.mem_comap, RingHom.mem_ker]
        rw [Theorem1323.eval_dehomogenize_eq]
        exact hP f hf
      exact this hh
    exact (h13_23 ▸ hP_affine) g hg
  ·


    intro hP f hf
    rw [← Theorem1323.eval_homogenize_dehomogenize_eq k f P]
    exact hP _ (Theorem1323.homogenize_dehomogenize_mem_homogenizeIdeal k hf)

end Theorem1324

end

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Corollary1326

variable {n : ℕ} (k : Type*) [Field k]

/-- Functoriality: equal subsets have equal vanishing ideals. -/
lemma vanishingIdeal_eq_of_set_eq (S T : Set (Fin n → k)) (h : S = T) :
    vanishingIdeal k S = vanishingIdeal k T :=
  congrArg (vanishingIdeal k) h

/-- Ring isomorphism between coordinate rings induced by equality of varieties
$V = V'$. -/
def coordinateRingEquiv
    (V V' : Set (Fin n → k)) (hVV' : V = V') :
    (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) ≃+*
    (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
  Ideal.quotEquivOfEq (vanishingIdeal_eq_of_set_eq k V V' hVV')

/-- Equal varieties give coordinate rings with equal Krull dimension. -/
theorem krullDim_eq
    (V V' : Set (Fin n → k)) (hVV' : V = V') :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) =
    ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
  ringKrullDim_eq_of_ringEquiv (coordinateRingEquiv k V V' hVV')

/-- Equal irreducible varieties give isomorphic function fields. -/
def functionFieldEquiv
    (V V' : Set (Fin n → k)) (hVV' : V = V')
    [(vanishingIdeal k V).IsPrime] [(vanishingIdeal k V').IsPrime] :
    FractionRing (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) ≃+*
    FractionRing (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') := by
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) :=
    Ideal.Quotient.isDomain _
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
    Ideal.Quotient.isDomain _
  exact IsFractionRing.ringEquivOfRingEquiv (coordinateRingEquiv k V V' hVV')

/-- Coordinate-ring isomorphism between the affine part of the projective
closure of $V(I)$ and the affine variety $V(I)$ itself (Corollary 13.26). -/
def coordinateRingEquiv_of_projective_closure
    (I : Ideal (MvPolynomial (Fin n) k)) :
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ ProjectiveClosure.homogenizeIdeal I,
          eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) ≃+*
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k | ∀ f ∈ I, eval P f = 0}) :=
  coordinateRingEquiv k _ _
    (Theorem1323.projective_closure_cap_affine_eq k I)

/-- Dimension is preserved: the affine part of the projective closure of
$V(I)$ has the same Krull dimension as $V(I)$. -/
theorem krullDim_eq_of_projective_closure
    (I : Ideal (MvPolynomial (Fin n) k)) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ ProjectiveClosure.homogenizeIdeal I,
          eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) =
    ringKrullDim (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k | ∀ f ∈ I, eval P f = 0}) :=
  krullDim_eq k _ _ (Theorem1323.projective_closure_cap_affine_eq k I)

/-- The affine piece of a projective ideal $I$ over chart $U_0$ equals the
zero locus of its dehomogenization at $X_0$. -/
theorem affinePart_eq_dehomogenizedIdeal_zeroLocus
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    {P : Fin n → k | ∀ f ∈ I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0} := by
  have h1 := Theorem1324.projective_closure_of_affinePart_eq k I
  have h2 := Theorem1323.projective_closure_cap_affine_eq k
    (I.map (AffineParts.dehomogenize k 0))
  exact h1.trans h2

/-- Coordinate-ring isomorphism induced by `affinePart_eq_dehomogenizedIdeal_zeroLocus`. -/
def coordinateRingEquiv_of_affinePart
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+*
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
  coordinateRingEquiv k _ _
    (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

/-- Krull dimension agrees on the two presentations of the affine piece. -/
theorem krullDim_eq_of_affinePart
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) =
    ringKrullDim (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
  krullDim_eq k _ _ (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

/-- Function-field isomorphism for the two presentations of an irreducible
affine piece. -/
def functionFieldEquiv_of_affinePart
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    [(vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}).IsPrime]
    [(vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}).IsPrime] :
    FractionRing (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+*
    FractionRing (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
  functionFieldEquiv k _ _
    (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

/-- Part of Corollary 13.26: if the projective dimension is $d$, then every
chart's affine dimension is $\le d$. -/
theorem corollary_13_26_part2_dimension
    {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k) (d : ℕ)
    (hd : ProjectiveDimension.HasProjectiveDimension k f d)
    (i : Fin (n + 1)) :
    ∀ (d_i : ℕ),
      ProjectiveDimension.HasAffineDimension k n
        (ProjectiveDimension.affinePartZeroLocusAlgClosed k f i) d_i → d_i ≤ d :=
  fun d_i hdi => hd.1 i d_i hdi

/-- Corollary 13.26 (coordinate-ring compatibility). For any affine ideal
$I_1 \subseteq k[X_1, \ldots, X_n]$ and any projective ideal
$I_2 \subseteq k[X_0, \ldots, X_n]$, the affine pieces of $V_+(I_1)$ and
$V(I_2)|_{U_0}$ have coordinate rings isomorphic to those of $V(I_1)$ and the
dehomogenization of $I_2$ respectively. -/
theorem corollary_13_26
    (I₁ : Ideal (MvPolynomial (Fin n) k))
    (I₂ : Ideal (MvPolynomial (Fin (n + 1)) k)) :

    (Nonempty
      ((MvPolynomial (Fin n) k ⧸
        vanishingIdeal k {P : Fin n → k |
          ∀ g ∈ ProjectiveClosure.homogenizeIdeal I₁,
            eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) ≃+*
       (MvPolynomial (Fin n) k ⧸
        vanishingIdeal k {P : Fin n → k | ∀ f ∈ I₁, eval P f = 0}))) ∧

    (Nonempty
      ((MvPolynomial (Fin n) k ⧸
        vanishingIdeal k {P : Fin n → k |
          ∀ f ∈ I₂, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+*
       (MvPolynomial (Fin n) k ⧸
        vanishingIdeal k {P : Fin n → k |
          ∀ g ∈ I₂.map (AffineParts.dehomogenize k 0), eval P g = 0}))) :=
  ⟨⟨coordinateRingEquiv_of_projective_closure k I₁⟩,
   ⟨coordinateRingEquiv_of_affinePart k I₂⟩⟩

end Corollary1326

end
