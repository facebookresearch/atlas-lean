/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz

variable (k : Type*) [Field k]

/-- Affine $n$-space over $k$, defined as $\overline{k}^n$, i.e. tuples in the algebraic
closure. -/
abbrev AffineSpace_k (n : ℕ) : Type _ := Fin n → AlgebraicClosure k

/-- The set of $L$-rational points in affine $n$-space: tuples all of whose coordinates lie
in the intermediate field $L \subseteq \overline{k}$. -/
def LRationalPoints (n : ℕ) (L : IntermediateField k (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  {P | ∀ i, P i ∈ L}


section GaloisCharacterization

variable [PerfectField k]

/-- The natural action of the absolute Galois group $\mathrm{Gal}(\overline{k}/k)$ on affine
$n$-space by coordinate-wise application. -/
noncomputable instance galoisActionAffineSpace (n : ℕ) :
    MulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AffineSpace_k k n) where
  smul σ P := fun i => σ (P i)
  one_smul P := by ext i; simp
  mul_smul σ τ P := by ext i; simp [AlgEquiv.mul_apply]

/-- The set of points in $\overline{k}^n$ fixed by every element of the Galois group fixing
the intermediate field $L$ (the Galois-theoretic characterization of $L$-rational points). -/
def galoisFixedPoints (n : ℕ) (L : IntermediateField k (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  {P | ∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
    σ ∈ L.fixingSubgroup → (fun i => σ (P i)) = P}


end GaloisCharacterization

/-- The algebraic set $V(S)$ in $\overline{k}^n$ cut out by a set $S$ of polynomials over
$\overline{k}$, i.e. the common zero locus. -/
def AlgebraicSet (n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (AffineSpace_k k n) :=
  {P | ∀ f ∈ S, MvPolynomial.eval P f = 0}


/-- The $L$-rational points of the algebraic set $V(S)$: zeros of $S$ with all coordinates
in the intermediate field $L$. -/
def AlgebraicSetLRational (n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (L : IntermediateField k (AlgebraicClosure k)) : Set (AffineSpace_k k n) :=
  AlgebraicSet k n S ∩ LRationalPoints k n L


/-- The hypersurface $V(f) = \{P : f(P) = 0\}$ cut out by a single polynomial $f$. -/
def AlgebraicSetSingleton (n : ℕ) (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  AlgebraicSet k n {f}


/-- For polynomials over $\overline{k}$, the ring-evaluation `MvPolynomial.eval` agrees with
the algebra-evaluation `MvPolynomial.aeval`. -/
lemma eval_eq_aeval_algebraicClosure {n : ℕ} (P : AffineSpace_k k n)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    MvPolynomial.eval P f = MvPolynomial.aeval P f := by
  unfold MvPolynomial.aeval MvPolynomial.eval
  simp [AlgHom.coe_mk]

/-- The algebraic set cut out by an ideal $I \subseteq \overline{k}[x_1, \ldots, x_n]$ is
the same as the Mathlib `zeroLocus` of $I$. -/
lemma algebraicSet_ideal_eq_zeroLocus {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    AlgebraicSet k n (I : Set _) =
      MvPolynomial.zeroLocus (AlgebraicClosure k) I := by
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, MvPolynomial.mem_zeroLocus_iff]
  exact forall₂_congr fun f _ => by rw [eval_eq_aeval_algebraicClosure]

/-- Weak Nullstellensatz: every proper ideal $I \subsetneq \overline{k}[x_1, \ldots, x_n]$
has a common zero in $\overline{k}^n$. -/
theorem weak_nullstellensatz {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hI : I ≠ ⊤) :
    Set.Nonempty (AlgebraicSet k n (I : Set _)) := by
  rw [algebraicSet_ideal_eq_zeroLocus]
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hvan : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      (MvPolynomial.zeroLocus (AlgebraicClosure k) I) = ⊤ := by
    rw [h, MvPolynomial.vanishingIdeal_empty]
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I] at hvan
  exact hI (Ideal.radical_eq_top.mp hvan)

namespace Definition1213

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The radical $\sqrt{I}$ of an ideal $I$ equals $\{x : R \mid \exists r > 0, x^r \in I\}$,
matching the textbook definition. -/
theorem radical_eq_setOf_pow_mem :
    (I.radical : Set R) = {x : R | ∃ r : ℕ, 0 < r ∧ x ^ r ∈ I} := by
  ext x
  simp only [SetLike.mem_coe, Ideal.mem_radical_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.succ_pos n, by rw [pow_succ]; exact I.mul_mem_right x hn⟩
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩


end Definition1213

namespace Lemma1214

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Lemma 12.14: the set $\{x : \exists n, x^n \in I\}$ is an ideal (namely $\sqrt{I}$). -/
theorem radical_is_ideal :
    ∃ J : Ideal R, (J : Set R) = {x : R | ∃ n : ℕ, x ^ n ∈ I} :=
  ⟨I.radical, rfl⟩


end Lemma1214

/-- A subset $V \subseteq \overline{k}^n$ is an algebraic subset if it equals $V(S)$ for
some set $S$ of polynomials. -/
def IsAlgebraicSubset (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)), V = AlgebraicSet k n S

/-- The zero set $V(S)$ is, trivially, an algebraic subset. -/
theorem algebraicSet_isAlgebraicSubset {n : ℕ}
    (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    IsAlgebraicSubset k n (AlgebraicSet k n S) :=
  ⟨S, rfl⟩

/-- An algebraic set $V$ is irreducible if it is nonempty and whenever $V = V_1 \cup V_2$
with each $V_i$ algebraic, one of the $V_i$ equals $V$. -/
def IsIrreducibleAlgebraicSet (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  V.Nonempty ∧
    ∀ V₁ V₂ : Set (AffineSpace_k k n),
      IsAlgebraicSubset k n V₁ → IsAlgebraicSubset k n V₂ →
      V = V₁ ∪ V₂ → V₁ = V ∨ V₂ = V

/-- An irreducible algebraic set is nonempty by definition. -/
theorem IsIrreducibleAlgebraicSet.nonempty {n : ℕ} {V : Set (AffineSpace_k k n)}
    (h : IsIrreducibleAlgebraicSet k n V) : V.Nonempty :=
  h.1


section NoetherianRing

/-- A ring is Noetherian iff every ideal is finitely generated. -/
theorem isNoetherianRing_iff_every_ideal_fg (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff_ideal_fg R

/-- A ring is Noetherian iff every ascending chain of ideals stabilizes. -/
theorem isNoetherianRing_iff_ideal_acc (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔
      ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
  rw [isNoetherianRing_iff]
  exact (monotone_stabilizes_iff_noetherian (R := R) (M := R)).symm

/-- Combining the previous two: every ideal is finitely generated iff every ascending chain
stabilizes. -/
theorem noetherian_fg_iff_acc (R : Type*) [CommRing R] :
    (∀ I : Ideal R, I.FG) ↔
      ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
  rw [← isNoetherianRing_iff_every_ideal_fg, isNoetherianRing_iff_ideal_acc]

end NoetherianRing

section HilbertBasis

/-- Hilbert basis theorem: if $R$ is Noetherian, then $R[X]$ is Noetherian. -/
theorem hilbert_basis_theorem (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (Polynomial R) :=
  Polynomial.isNoetherianRing

end HilbertBasis

section IdealOfAlgebraicSet

open MvPolynomial

variable {k} {σ : Type*}

/-- The vanishing ideal $I(Z)$ of a subset $Z \subseteq k^\sigma$: polynomials in $k[x_\sigma]$
that vanish on every point of $Z$. -/
def idealOfAlgebraicSet (Z : Set (σ → k)) : Ideal (MvPolynomial σ k) where
  carrier := {f : MvPolynomial σ k | ∀ P ∈ Z, MvPolynomial.eval P f = 0}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {p q} hp hq x hx => by
    rw [map_add, hp x hx, hq x hx, add_zero]
  smul_mem' := fun r p hp x hx => by
    rw [smul_eq_mul, map_mul, hp x hx, mul_zero]

/-- Membership in $I(Z)$ unfolds to vanishing of $f$ at every point of $Z$. -/
@[simp]
theorem mem_idealOfAlgebraicSet_iff {Z : Set (σ → k)} {f : MvPolynomial σ k} :
    f ∈ idealOfAlgebraicSet Z ↔ ∀ P ∈ Z, MvPolynomial.eval P f = 0 :=
  Iff.rfl

/-- The textbook vanishing ideal `idealOfAlgebraicSet` matches Mathlib's
`MvPolynomial.vanishingIdeal`. -/
theorem idealOfAlgebraicSet_eq_vanishingIdeal (Z : Set (σ → k)) :
    idealOfAlgebraicSet Z = MvPolynomial.vanishingIdeal k Z := by
  ext f
  simp [mem_idealOfAlgebraicSet_iff, MvPolynomial.mem_vanishingIdeal_iff,
    MvPolynomial.aeval_eq_eval]

/-- Antitone: $Y \subseteq Z$ implies $I(Z) \subseteq I(Y)$. -/
theorem idealOfAlgebraicSet_anti_mono {Y Z : Set (σ → k)} (h : Y ⊆ Z) :
    idealOfAlgebraicSet Z ≤ idealOfAlgebraicSet Y :=
  fun _ hf P hP => hf P (h hP)

/-- $I(Y \cup Z) = I(Y) \cap I(Z)$. -/
theorem idealOfAlgebraicSet_union (Y Z : Set (σ → k)) :
    idealOfAlgebraicSet (Y ∪ Z) = idealOfAlgebraicSet Y ⊓ idealOfAlgebraicSet Z := by
  ext f
  simp only [mem_idealOfAlgebraicSet_iff, Ideal.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩
  · rintro ⟨hY, hZ⟩ P (hP | hP)
    · exact hY P hP
    · exact hZ P hP

end IdealOfAlgebraicSet

/-- Hilbert's Nullstellensatz: for any ideal $I$ in $\overline{k}[x_1, \ldots, x_n]$,
$I(V(I)) = \sqrt{I}$. -/
theorem hilbert_nullstellensatz {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I.radical := by
  rw [idealOfAlgebraicSet_eq_vanishingIdeal, algebraicSet_ideal_eq_zeroLocus,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

section Corollary1217

open MvPolynomial

variable {n : ℕ}

/-- Evaluation at a point $P$ is a surjective ring homomorphism
$\overline{k}[x_1, \ldots, x_n] \to \overline{k}$. -/
lemma eval_surjective_algebraicClosure (P : Fin n → AlgebraicClosure k) :
    Function.Surjective (MvPolynomial.eval P) :=
  fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩

/-- The kernel of evaluation at $P$ equals the vanishing ideal of the singleton $\{P\}$. -/
lemma ker_eval_eq_vanishingIdeal_singleton (P : Fin n → AlgebraicClosure k) :
    RingHom.ker (MvPolynomial.eval P) =
      MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by
  ext f
  simp [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval]

/-- The vanishing ideal $I(\{P\})$ of a single point in $\overline{k}^n$ is maximal. -/
theorem vanishingIdeal_singleton_isMaximal (P : Fin n → AlgebraicClosure k) :
    (MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      ({P} : Set (Fin n → AlgebraicClosure k))).IsMaximal := by
  rw [← ker_eval_eq_vanishingIdeal_singleton k P]
  exact RingHom.ker_isMaximal_of_surjective _ (eval_surjective_algebraicClosure k P)

/-- Every maximal ideal of $\overline{k}[x_1, \ldots, x_n]$ has the form $I(\{P\})$ for some
$P \in \overline{k}^n$ (one direction of Corollary 12.17). -/
theorem maximal_ideal_eq_vanishingIdeal_singleton
    (m : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hm : m.IsMaximal) :
    ∃ P : Fin n → AlgebraicClosure k,
      m = MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by

  have hZ_nonempty : Set.Nonempty (MvPolynomial.zeroLocus (AlgebraicClosure k) m) := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
        (MvPolynomial.zeroLocus (AlgebraicClosure k) m) = ⊤ := by
      rw [h, MvPolynomial.vanishingIdeal_empty]
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at this
    exact hm.ne_top (Ideal.radical_eq_top.mp this)

  obtain ⟨P, hP⟩ := hZ_nonempty
  use P

  have h1 : m ≤ MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      (MvPolynomial.zeroLocus (AlgebraicClosure k) m) :=
    MvPolynomial.le_vanishingIdeal_zeroLocus m

  have h2 : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      (MvPolynomial.zeroLocus (AlgebraicClosure k) m) ≤
      MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} :=
    MvPolynomial.vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hP)

  haveI : (MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      ({P} : Set (Fin n → AlgebraicClosure k))).IsMaximal :=
    vanishingIdeal_singleton_isMaximal k P

  exact hm.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) (le_trans h1 h2)

/-- Corollary 12.17: an ideal of $\overline{k}[x_1, \ldots, x_n]$ is maximal iff it is the
vanishing ideal of a single point. -/
theorem corollary_12_17
    {m : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))} :
    m.IsMaximal ↔
      ∃ P : Fin n → AlgebraicClosure k,
        m = MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by
  constructor
  · exact maximal_ideal_eq_vanishingIdeal_singleton k m
  · rintro ⟨P, rfl⟩
    exact vanishingIdeal_singleton_isMaximal k P

end Corollary1217

section AffineCoordinateRings

open MvPolynomial

variable {k}

/-- The ideal $I_k(Z) \subseteq k[x_1, \ldots, x_n]$ of polynomials over $k$ vanishing on
$Z$, obtained by pulling back $I(Z)$ along the scalar extension map. -/
noncomputable def idealOverK {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.comap (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
    (idealOfAlgebraicSet Z)

/-- $f \in I_k(Z)$ iff its image in $\overline{k}[x_1, \ldots, x_n]$ vanishes on $Z$. -/
theorem mem_idealOverK_iff {n : ℕ} {Z : Set (Fin n → AlgebraicClosure k)}
    {f : MvPolynomial (Fin n) k} :
    f ∈ idealOverK Z ↔
      MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈ idealOfAlgebraicSet Z := by
  rfl

/-- A subset $Z \subseteq \overline{k}^n$ is *defined over* $k$ if its vanishing ideal
$I(Z)$ is the extension to $\overline{k}$ of $I_k(Z)$. -/
def IsDefinedOver {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) : Prop :=
  idealOfAlgebraicSet Z =
    Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
      (idealOverK Z)

/-- The affine coordinate ring $k[Z] = k[x_1, \ldots, x_n] / I_k(Z)$ over the base field. -/
noncomputable def AffineCoordinateRing {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :=
  MvPolynomial (Fin n) k ⧸ idealOverK Z

/-- The affine coordinate ring $\overline{k}[Z] = \overline{k}[x_1, \ldots, x_n] / I(Z)$ over
the algebraic closure. -/
def AffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :=
  MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet Z

/-- The affine coordinate ring $k[Z]$ inherits a commutative ring structure from the quotient. -/
noncomputable instance instCommRingAffineCoordinateRing {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    CommRing (AffineCoordinateRing Z) :=
  Ideal.Quotient.commRing (idealOverK Z)

/-- The affine coordinate ring $\overline{k}[Z]$ inherits a commutative ring structure
from the quotient. -/
noncomputable instance instCommRingAffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    CommRing (AffineCoordinateRingBar Z) :=
  Ideal.Quotient.commRing (idealOfAlgebraicSet Z)

end AffineCoordinateRings

section Theorem1221

open MvPolynomial

/-- Closure-like idempotence: $V(I(V(S))) = V(S)$ for any set of polynomials $S$. -/
theorem algebraicSet_idealOfAlgebraicSet_eq {n : ℕ}
    (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    AlgebraicSet k n ((idealOfAlgebraicSet (AlgebraicSet k n S)) : Set _) =
    AlgebraicSet k n S := by
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, mem_idealOfAlgebraicSet_iff, SetLike.mem_coe]
  exact ⟨fun hP f hfS => hP f (fun Q hQ => hQ f hfS), fun hP f hf => hf P hP⟩

/-- For an algebraic subset $V$, $V(I(V)) = V$. -/
theorem algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAlgebraicSubset k n V) :
    AlgebraicSet k n ((idealOfAlgebraicSet V) : Set _) = V := by
  obtain ⟨S, rfl⟩ := hV
  exact algebraicSet_idealOfAlgebraicSet_eq k S

/-- Theorem 12.21: an algebraic subset $V$ is irreducible iff $I(V)$ is a prime ideal. -/
theorem isIrreducibleAlgebraicSet_iff_isPrime {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAlgebraicSubset k n V) :
    IsIrreducibleAlgebraicSet k n V ↔ (idealOfAlgebraicSet V).IsPrime := by
  constructor
  ·
    intro hirr
    apply Ideal.IsPrime.mk
    ·
      intro h
      have h1 : (1 : MvPolynomial (Fin n) (AlgebraicClosure k)) ∈ idealOfAlgebraicSet V := by
        rw [h]; exact Submodule.mem_top
      obtain ⟨P, hP⟩ := hirr.1
      have := h1 P hP; simp at this
    ·
      intro f g hfg

      set V₁ := V ∩ {P | MvPolynomial.eval P f = 0}
      set V₂ := V ∩ {P | MvPolynomial.eval P g = 0}

      have hdecomp : V = V₁ ∪ V₂ := by
        ext P; simp only [V₁, V₂, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro hP
          have := hfg P hP; rw [map_mul] at this
          rcases mul_eq_zero.mp this with h | h
          · exact Or.inl ⟨hP, h⟩
          · exact Or.inr ⟨hP, h⟩
        · rintro (⟨hP, -⟩ | ⟨hP, -⟩) <;> exact hP

      have hAlg1 : IsAlgebraicSubset k n V₁ := by
        obtain ⟨S, rfl⟩ := hV
        exact ⟨S ∪ {f}, by
          ext P; simp only [V₁, AlgebraicSet, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_union, Set.mem_singleton_iff]
          exact ⟨fun ⟨hS, hf⟩ g => by rintro (hg | rfl) <;> [exact hS g hg; exact hf],
                 fun h => ⟨fun g hg => h g (.inl hg), h f (.inr rfl)⟩⟩⟩

      have hAlg2 : IsAlgebraicSubset k n V₂ := by
        obtain ⟨S, rfl⟩ := hV
        exact ⟨S ∪ {g}, by
          ext P; simp only [V₂, AlgebraicSet, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_union, Set.mem_singleton_iff]
          exact ⟨fun ⟨hS, hg⟩ p => by rintro (hp | rfl) <;> [exact hS p hp; exact hg],
                 fun h => ⟨fun p hp => h p (.inl hp), h g (.inr rfl)⟩⟩⟩

      rcases hirr.2 V₁ V₂ hAlg1 hAlg2 hdecomp with h | h
      ·
        left; rw [mem_idealOfAlgebraicSet_iff]; intro P hP
        exact (h.symm ▸ hP : P ∈ V₁).2
      ·
        right; rw [mem_idealOfAlgebraicSet_iff]; intro P hP
        exact (h.symm ▸ hP : P ∈ V₂).2
  ·
    intro hprime
    constructor
    ·
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hprime.ne_top; ext f; simp only [Submodule.mem_top, iff_true]
      rw [mem_idealOfAlgebraicSet_iff]; intro P hP
      simp [hempty] at hP
    ·
      intro V₁ V₂ hV₁ hV₂ hunion

      have hIV : idealOfAlgebraicSet V = idealOfAlgebraicSet V₁ ⊓ idealOfAlgebraicSet V₂ := by
        rw [hunion, idealOfAlgebraicSet_union]
      have hmul : idealOfAlgebraicSet V₁ * idealOfAlgebraicSet V₂ ≤ idealOfAlgebraicSet V :=
        hIV ▸ Ideal.mul_le_inf

      rw [hprime.mul_le] at hmul

      have hle1 : idealOfAlgebraicSet V ≤ idealOfAlgebraicSet V₁ :=
        idealOfAlgebraicSet_anti_mono (hunion ▸ Set.subset_union_left)
      have hle2 : idealOfAlgebraicSet V ≤ idealOfAlgebraicSet V₂ :=
        idealOfAlgebraicSet_anti_mono (hunion ▸ Set.subset_union_right)

      rcases hmul with h | h
      · left
        have heq : idealOfAlgebraicSet V₁ = idealOfAlgebraicSet V := le_antisymm h hle1
        rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV₁,
            ← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV]
        congr 1; exact_mod_cast heq
      · right
        have heq : idealOfAlgebraicSet V₂ = idealOfAlgebraicSet V := le_antisymm h hle2
        rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV₂,
            ← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV]
        congr 1; exact_mod_cast heq

end Theorem1221

section Corollary1218

open MvPolynomial

variable {n : ℕ}

/-- The vanishing ideal $I(V)$ of any subset $V$ is always a radical ideal. -/
theorem idealOfAlgebraicSet_isRadical
    (V : Set (AffineSpace_k k n)) :
    (idealOfAlgebraicSet V).IsRadical := by
  rw [idealOfAlgebraicSet_eq_vanishingIdeal]
  have hgc := @MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection (AlgebraicClosure k)
    (AlgebraicClosure k) _ _ _ (Fin n)
  rw [Ideal.IsRadical]
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
      (k := AlgebraicClosure k) (K := AlgebraicClosure k)
      (MvPolynomial.vanishingIdeal (AlgebraicClosure k) V)]
  rw [hgc.u_l_u_eq_u V]

/-- If $I$ is radical, then $I(V(I)) = I$ (consequence of the Nullstellensatz). -/
theorem idealOfAlgebraicSet_algebraicSet_of_isRadical
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hI : I.IsRadical) :
    idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I := by
  rw [hilbert_nullstellensatz, hI.radical]

/-- Corollary 12.18: the Nullstellensatz bijection between radical ideals of
$\overline{k}[x_1, \ldots, x_n]$ and algebraic subsets of $\overline{k}^n$. -/
noncomputable def radicalIdealAlgebraicSetEquiv :
    {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)) // I.IsRadical} ≃
    {V : Set (AffineSpace_k k n) // IsAlgebraicSubset k n V} where
  toFun I :=
    let S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)) := I.1
    ⟨AlgebraicSet k n S, S, rfl⟩
  invFun V := ⟨idealOfAlgebraicSet V.1, idealOfAlgebraicSet_isRadical k V.1⟩
  left_inv := fun ⟨I, hI⟩ => by
    simp only
    ext1
    exact idealOfAlgebraicSet_algebraicSet_of_isRadical k I hI
  right_inv := fun ⟨V, hV⟩ => by
    simp only
    ext1
    exact algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV


end Corollary1218
