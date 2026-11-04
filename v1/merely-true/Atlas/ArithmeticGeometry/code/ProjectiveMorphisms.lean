/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad

noncomputable section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A homogeneous representative of a projective regular function: a pair of homogeneous polynomials $(\text{num}, \text{den})$ of the same degree on $\mathbb{P}^n$, with $\text{den} \neq 0$, representing the rational function $\text{num}/\text{den}$. -/
structure HomogeneousRep (n : ℕ) (k : Type*) [Field k] where
  num : MvPolynomial (Fin (n + 1)) k
  den : MvPolynomial (Fin (n + 1)) k
  deg : ℕ
  num_homog : num.IsHomogeneous deg
  den_homog : den.IsHomogeneous deg
  den_ne_zero : den ≠ 0

/-- A homogeneous representative is defined at a projective point $P$ if its denominator does not vanish at $P$. -/
def HomogeneousRep.isDefinedAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : Prop :=
  eval P.rep r.den ≠ 0

/-- Evaluate a homogeneous representative $\text{num}/\text{den}$ at a projective point $P$. Well-defined when the denominator is nonzero. -/
noncomputable def HomogeneousRep.evalAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : k :=
  eval P.rep r.num / eval P.rep r.den

/-- Two homogeneous representatives are equivalent on a set $X$ iff $\text{num}_1 \cdot \text{den}_2 - \text{num}_2 \cdot \text{den}_1$ vanishes on $X$ (i.e., they define the same rational function on $X$). -/
def HomogeneousRep.equivOn (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ P ∈ X, eval P.rep (r₁.num * r₂.den - r₂.num * r₁.den) = 0

/-- Reflexivity: any homogeneous representative is equivalent to itself on $X$. -/
theorem HomogeneousRep.equivOn_refl (r : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) :
    r.equivOn k r X := by
  intro P _
  simp [sub_self]

/-- Symmetry of `equivOn`: if $r_1 \sim r_2$ on $X$ then $r_2 \sim r_1$ on $X$. -/
theorem HomogeneousRep.equivOn_symm (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k)))
    (h : r₁.equivOn k r₂ X) :
    r₂.equivOn k r₁ X := by
  intro P hP
  have hval := h P hP
  simp only [map_sub, map_mul] at hval ⊢
  have := neg_eq_zero.mpr hval
  rw [neg_sub] at this
  exact this

/-- Transitivity of `equivOn`, using primality of the vanishing ideal of $X$ (an irreducibility hypothesis) plus a nondegeneracy condition on $r_2$. -/
theorem HomogeneousRep.equivOn_trans
    {n' : ℕ} {k' : Type*} [Field k']
    {X : Set (ℙ k' (Fin (n' + 1) → k'))}
    (r₁ r₂ r₃ : HomogeneousRep n' k')
    (h₁₂ : r₁.equivOn k' r₂ X)
    (h₂₃ : r₂.equivOn k' r₃ X)
    (hirr : ∀ (p q : MvPolynomial (Fin (n' + 1)) k'),
      (∀ P ∈ X, eval P.rep (p * q) = 0) →
      (∀ P ∈ X, eval P.rep p = 0) ∨ (∀ P ∈ X, eval P.rep q = 0))
    (h₂_nondeg : ¬(∀ P ∈ X, eval P.rep r₂.num = 0) ∨
                  ¬(∀ P ∈ X, eval P.rep r₂.den = 0)) :
    r₁.equivOn k' r₃ X := by


  have hnum_vanish : ∀ P ∈ X,
      eval P.rep (r₂.num * (r₁.num * r₃.den - r₃.num * r₁.den)) = 0 := by
    intro P hP
    have h1 := h₁₂ P hP
    have h2 := h₂₃ P hP
    simp only [map_sub, map_mul] at h1 h2 ⊢
    linear_combination eval P.rep r₁.num * h2 + eval P.rep r₃.num * h1

  have hden_vanish : ∀ P ∈ X,
      eval P.rep (r₂.den * (r₁.num * r₃.den - r₃.num * r₁.den)) = 0 := by
    intro P hP
    have h1 := h₁₂ P hP
    have h2 := h₂₃ P hP
    simp only [map_sub, map_mul] at h1 h2 ⊢
    linear_combination eval P.rep r₃.den * h1 + eval P.rep r₁.den * h2

  have hnum_or := hirr r₂.num (r₁.num * r₃.den - r₃.num * r₁.den) hnum_vanish
  have hden_or := hirr r₂.den (r₁.num * r₃.den - r₃.num * r₁.den) hden_vanish

  rcases hnum_or with hnum_zero | hdone
  · rcases hden_or with hden_zero | hdone
    ·
      rcases h₂_nondeg with h | h
      · exact absurd hnum_zero h
      · exact absurd hden_zero h
    · exact hdone
  · exact hdone



/-- Two equivalent homogeneous representatives evaluate to the same value at any common point of definition. -/
theorem HomogeneousRep.evalAt_eq_of_equivOn
    (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k)))
    (P : ℙ k (Fin (n + 1) → k))
    (hPX : P ∈ X)
    (hequiv : r₁.equivOn k r₂ X)
    (h₁ : r₁.isDefinedAt k P)
    (h₂ : r₂.isDefinedAt k P) :
    r₁.evalAt k P = r₂.evalAt k P := by
  unfold evalAt isDefinedAt at *
  have hP := hequiv P hPX
  simp only [map_sub, map_mul] at hP
  rw [div_eq_div_iff h₁ h₂]
  exact sub_eq_zero.mp hP

/-- A projective rational function on a set $X \subseteq \mathbb{P}^n_k$: an equivalence class of homogeneous representatives, packaged as a maximal nonempty set of mutually equivalent `HomogeneousRep`s. -/
structure ProjectiveRatFun (n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (HomogeneousRep n k)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ r₁ ∈ reps, ∀ r₂ ∈ reps, HomogeneousRep.equivOn k r₁ r₂ X
  reps_maximal : ∀ r, (∃ r₀ ∈ reps, HomogeneousRep.equivOn k r r₀ X) → r ∈ reps


/-- A projective rational function is regular at a point $P \in X$ iff some representative is defined at $P$. -/
def ProjectiveRatFun.IsRegularAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ r.reps, rep.isDefinedAt k P

/-- The regular domain (locus of regularity) of a projective rational function: all points of $X$ where some representative is defined. -/
def ProjectiveRatFun.regularDomain
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ r.reps, rep.isDefinedAt k P}


/-- Unfolding lemma: $P$ is in the regular domain of $r$ iff $P \in X$ and $r$ is regular at $P$. -/
theorem ProjectiveRatFun.mem_regularDomain_iff
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k)) :
    P ∈ r.regularDomain k ↔ ∃ hP : P ∈ X, r.IsRegularAt k P hP := by
  simp only [regularDomain, Set.mem_sep_iff, IsRegularAt]
  constructor
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩

/-- Evaluate a projective rational function $r$ at a point $P$ in its regular domain by choosing any representative defined at $P$ and evaluating it. -/
noncomputable def ProjectiveRatFun.evalAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (hP : P ∈ r.regularDomain k) : k :=
  hP.2.choose.evalAt k P

/-- The value of $r$ at $P$ agrees with the value computed from any representative defined at $P$. -/
theorem ProjectiveRatFun.evalAt_eq_rep
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (hP : P ∈ r.regularDomain k)
    (rep : HomogeneousRep n k)
    (hrep : rep ∈ r.reps)
    (hdef : rep.isDefinedAt k P) :
    r.evalAt k P hP = rep.evalAt k P := by
  unfold evalAt
  apply HomogeneousRep.evalAt_eq_of_equivOn
  · exact hP.1
  · exact r.reps_equiv _ hP.2.choose_spec.1 _ hrep
  · exact hP.2.choose_spec.2
  · exact hdef

end ProjectiveRegularFunction

namespace ProjectiveRatMap

open MvPolynomial
open scoped LinearAlgebra.Projectivization
open ProjectiveRegularFunction

variable {m n : ℕ} (k : Type*) [Field k]

/-- A tuple representative of a rational map $X \dashrightarrow Y$ between projective varieties: an $(n+1)$-tuple of homogeneous polynomials of common degree, not all vanishing on $X$, whose evaluation lands in $Y$ (as a projective point). -/
structure RationalMapTupleRep (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  polys : Fin (n + 1) → MvPolynomial (Fin (m + 1)) k
  deg : ℕ
  polys_homog : ∀ i, (polys i).IsHomogeneous deg
  not_all_vanish : ∃ i, ∃ P ∈ X, eval P.rep (polys i) ≠ 0
  image_in_Y : ∀ P ∈ X,
    (∃ i, eval P.rep (polys i) ≠ 0) →
    ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ Y, eval Q.rep f = 0) →
    eval (fun j => eval P.rep (polys j)) f = 0

/-- A tuple representative is defined at $P$ iff at least one coordinate polynomial is nonzero at $P$. -/
def RationalMapTupleRep.isDefinedAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) : Prop :=
  ∃ i, eval P.rep (φ.polys i) ≠ 0

/-- The vector of values $(\varphi_0(P), \dots, \varphi_n(P))$ of a tuple representative at $P$. -/
noncomputable def RationalMapTupleRep.evalVec
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) :
    Fin (n + 1) → k :=
  fun i => eval P.rep (φ.polys i)

/-- Two tuple representatives are equivalent on $X$ iff $\varphi_i \psi_j - \varphi_j \psi_i$ vanishes on $X$ for all $i, j$ (i.e., they define the same projective point at every point of $X$). -/
def RationalMapTupleRep.equivOn
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ ψ : RationalMapTupleRep m n k X Y)
    : Prop :=
  ∀ i j, ∀ P ∈ X,
    eval P.rep (φ.polys i * ψ.polys j - φ.polys j * ψ.polys i) = 0

/-- Reflexivity of tuple equivalence. -/
theorem RationalMapTupleRep.equivOn_refl
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y) :
    φ.equivOn k φ := by
  intro i j P _
  simp only [map_sub, map_mul, sub_eq_zero]
  exact mul_comm _ _

/-- Symmetry of tuple equivalence. -/
theorem RationalMapTupleRep.equivOn_symm
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ ψ : RationalMapTupleRep m n k X Y)
    (h : φ.equivOn k ψ) :
    ψ.equivOn k φ := by
  intro i j P hP
  have hval := h i j P hP
  simp only [map_sub, map_mul] at hval ⊢
  have h1 : eval P.rep (φ.polys i) * eval P.rep (ψ.polys j) =
            eval P.rep (φ.polys j) * eval P.rep (ψ.polys i) := sub_eq_zero.mp hval
  have h2 : eval P.rep (ψ.polys i) * eval P.rep (φ.polys j) =
            eval P.rep (ψ.polys j) * eval P.rep (φ.polys i) := by
    rw [mul_comm (eval P.rep (ψ.polys i)), mul_comm (eval P.rep (ψ.polys j))]
    exact h1.symm
  exact sub_eq_zero.mpr h2

/-- Transitivity of tuple equivalence on $X$, using primality of the vanishing ideal plus a nondegeneracy hypothesis on $\psi$. -/
theorem RationalMapTupleRep.equivOn_trans
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ ψ χ : RationalMapTupleRep m n k X Y)
    (h₁ : φ.equivOn k ψ)
    (h₂ : ψ.equivOn k χ)
    (hirr : ∀ (p q : MvPolynomial (Fin (m + 1)) k),
      (∀ P ∈ X, eval P.rep (p * q) = 0) →
      (∀ P ∈ X, eval P.rep p = 0) ∨ (∀ P ∈ X, eval P.rep q = 0))
    (h₂_nondeg : ∃ a, ¬(∀ P ∈ X, eval P.rep (ψ.polys a) = 0)) :
    φ.equivOn k χ := by
  intro i j P hP


  obtain ⟨a, ha⟩ := h₂_nondeg

  have hkey : ∀ P ∈ X,
      eval P.rep (ψ.polys a * (φ.polys i * χ.polys j - φ.polys j * χ.polys i)) = 0 := by
    intro Q hQ
    have h1_ia := h₁ i a Q hQ
    have h1_ja := h₁ j a Q hQ
    have h2_ij := h₂ i j Q hQ
    simp only [map_sub, map_mul] at h1_ia h1_ja h2_ij ⊢
    linear_combination
      eval Q.rep (χ.polys j) * h1_ia -
      eval Q.rep (χ.polys i) * h1_ja +
      eval Q.rep (φ.polys a) * h2_ij

  have hor := hirr (ψ.polys a) (φ.polys i * χ.polys j - φ.polys j * χ.polys i) hkey
  rcases hor with habs | hdone
  · exact absurd habs ha
  · exact hdone P hP


/-- A projective rational map $X \dashrightarrow Y$: an equivalence class of `RationalMapTupleRep`s, packaged as a maximal nonempty equivalence class. -/
structure ProjectiveRationalMap (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (RationalMapTupleRep m n k X Y)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ φ₁ ∈ reps, ∀ φ₂ ∈ reps, RationalMapTupleRep.equivOn k φ₁ φ₂
  reps_maximal : ∀ φ, (∃ φ₀ ∈ reps, RationalMapTupleRep.equivOn k φ φ₀) → φ ∈ reps

/-- A projective rational map is regular at $P \in X$ iff some representative is defined at $P$. -/
def ProjectiveRationalMap.IsRegularAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y)
    (P : ℙ k (Fin (m + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ φ.reps, rep.isDefinedAt k P

/-- The regular domain of a projective rational map: the locus of points of $X$ where it is regular. -/
def ProjectiveRationalMap.regularDomain
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (m + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ φ.reps, rep.isDefinedAt k P}


/-- Unfolding lemma: $P$ is in the regular domain of $\varphi$ iff $P \in X$ and $\varphi$ is regular at $P$. -/
theorem ProjectiveRationalMap.mem_regularDomain_iff
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) :
    P ∈ φ.regularDomain k ↔ ∃ hP : P ∈ X, φ.IsRegularAt k P hP := by
  simp only [regularDomain, Set.mem_sep_iff, IsRegularAt]
  constructor
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩
  · rintro ⟨hPX, rep, hrep, hdef⟩
    exact ⟨hPX, rep, hrep, hdef⟩


/-- A projective rational map is a morphism iff it is regular at every point of its domain $X$. -/
def ProjectiveRationalMap.IsMorphism
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  ∀ (P : ℙ k (Fin (m + 1) → k)) (hP : P ∈ X), φ.IsRegularAt k P hP


/-- A projective morphism $X \to Y$: a projective rational map that is regular everywhere on $X$. -/
structure ProjectiveMorphism (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toRatMap : ProjectiveRationalMap m n k X Y
  is_morphism : toRatMap.IsMorphism k

/-- The image of a projective rational map $\varphi: X \dashrightarrow Y$: points $Q \in Y$ that arise as $\varphi(P)$ for some $P$ in the regular domain. -/
def ProjectiveRationalMap.image
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {Q ∈ Y | ∃ P ∈ X, ∃ rep ∈ φ.reps,
    rep.isDefinedAt k P ∧
    ∀ i j, rep.evalVec k P i * Q.rep j = rep.evalVec k P j * Q.rep i}


/-- $S$ is Zariski-dense in $Y$ iff any polynomial vanishing on $S$ also vanishes on $Y$ (i.e., $S$'s Zariski closure contains $Y$). -/
def IsZariskiDenseIn {n : ℕ} (k : Type*) [Field k]
    (S Y : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ S, MvPolynomial.eval Q.rep f = 0) →
    (∀ Q ∈ Y, MvPolynomial.eval Q.rep f = 0)

/-- A projective rational map $\varphi: X \dashrightarrow Y$ is dominant iff its image is Zariski-dense in $Y$. -/
def ProjectiveRationalMap.IsDominant
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  IsZariskiDenseIn k (φ.image k) Y

end ProjectiveRatMap

namespace ProjectiveThm1518

open MvPolynomial
open scoped LinearAlgebra.Projectivization
open ProjectiveRegularFunction
open ProjectiveRatMap

variable {m n : ℕ} (k : Type*) [Field k]

/-- Evaluation commutes with `bind₁`: evaluating $\text{bind}_1 f\, p$ at $v$ equals evaluating $p$ at the vector $i \mapsto \text{eval}\, v\, (f\, i)$. -/
lemma eval_bind₁ {k' : Type*} [CommSemiring k'] {σ τ : Type*}
    (v : τ → k') (f : σ → MvPolynomial τ k') (p : MvPolynomial σ k') :
    eval v (bind₁ f p) = eval (fun i => eval v (f i)) p := by
  have h := eval₂Hom_bind₁ (RingHom.id k') v f p
  simp only [eval, coe_eval₂Hom] at *
  convert h using 2

/-- If $p$ is homogeneous of degree $d_p$ and each $f_i$ is homogeneous of degree $d_f$, then $\text{bind}_1 f\, p$ is homogeneous of degree $d_f \cdot d_p$. -/
lemma bind₁_isHomogeneous {k' : Type*} [CommSemiring k'] {σ τ : Type*}
    {p : MvPolynomial σ k'} {dp : ℕ} (hp : p.IsHomogeneous dp)
    {f : σ → MvPolynomial τ k'} {df : ℕ} (hf : ∀ i, (f i).IsHomogeneous df) :
    (bind₁ f p).IsHomogeneous (df * dp) := by
  rw [← aeval_eq_bind₁]; unfold aeval
  exact hp.eval₂ _ _ (fun r => isHomogeneous_C _ _) hf




/-- Scaling lemma for homogeneous polynomials: if $p$ is homogeneous of degree $d$, then $p(c \cdot v) = c^d \cdot p(v)$. -/
lemma eval_scale_homog' {k' : Type*} [CommRing k'] {σ : Type*}
    (p : MvPolynomial σ k') (d : ℕ)
    (hp : p.IsHomogeneous d) (c : k') (v : σ → k') :
    eval (fun i => c * v i) p = c ^ d * eval v p := by
  rw [as_sum p, map_sum, map_sum, Finset.mul_sum]
  congr 1; ext s; simp only [eval_monomial]
  by_cases hcs : coeff s p = 0
  · simp [hcs]
  · simp_rw [mul_pow]; rw [Finsupp.prod_mul]
    have hprod : s.prod (fun _ e => c ^ e) = c ^ d := by
      unfold Finsupp.prod; rw [Finset.prod_pow_eq_pow_sum, ← hp hcs]
      congr 1; simp [Finsupp.weight, Finsupp.linearCombination, Finsupp.sum]
    rw [hprod]; ring








/-- A function-field homomorphism $k(Y) \to k(X)$ as data: a map on `ProjectiveRatFun` that is well-defined modulo equality of evaluations and that preserves the field structure (addition, multiplication, constants) in the pointwise evaluation sense. -/
structure ProjectiveFunctionFieldHom
    (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toFun : ProjectiveRatFun n k Y → ProjectiveRatFun m k X
  map_eq : ∀ (r₁ r₂ : ProjectiveRatFun n k Y),
    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k),
      r₁.evalAt k P hP₁ = r₂.evalAt k P hP₂) →
    toFun r₁ = toFun r₂
  map_mul_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ * r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ * (toFun r₂).evalAt k P hPθ₂
  map_add_eval : ∀ (r₁ r₂ : ProjectiveRatFun n k Y)
    (r₁r₂ : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP₁ : P ∈ r₁.regularDomain k) (hP₂ : P ∈ r₂.regularDomain k)
      (hP₁₂ : P ∈ r₁r₂.regularDomain k),
      r₁r₂.evalAt k P hP₁₂ = r₁.evalAt k P hP₁ + r₂.evalAt k P hP₂) →
    ∀ P ∈ X,
    ∀ (hPθ₁ : P ∈ (toFun r₁).regularDomain k)
      (hPθ₂ : P ∈ (toFun r₂).regularDomain k)
      (hPθ₁₂ : P ∈ (toFun r₁r₂).regularDomain k),
    (toFun r₁r₂).evalAt k P hPθ₁₂ =
      (toFun r₁).evalAt k P hPθ₁ + (toFun r₂).evalAt k P hPθ₂
  map_const_eval : ∀ (c : k) (const_c : ProjectiveRatFun n k Y),

    (∀ P ∈ Y, ∀ (hP : P ∈ const_c.regularDomain k),
      const_c.evalAt k P hP = c) →
    ∀ P ∈ X, ∀ (hP : P ∈ (toFun const_c).regularDomain k),
      (toFun const_c).evalAt k P hP = c

/-- The homogeneous representative for the $i$-th coordinate function $x_i/x_0$ on $\mathbb{P}^n$. -/
noncomputable def coordHomogRep (n : ℕ) (k : Type*) [Field k] (i : Fin (n + 1)) :
    ProjectiveRegularFunction.HomogeneousRep n k where
  num := MvPolynomial.X i
  den := MvPolynomial.X 0
  deg := 1
  num_homog := MvPolynomial.isHomogeneous_X _ _
  den_homog := MvPolynomial.isHomogeneous_X _ _
  den_ne_zero := MvPolynomial.X_ne_zero _



















end ProjectiveThm1518

end
