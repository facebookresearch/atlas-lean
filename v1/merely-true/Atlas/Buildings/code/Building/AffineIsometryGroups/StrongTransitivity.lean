/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.LatticesValuations
import Atlas.Buildings.code.GeometricAlgebra.BilinearForms
import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.SphericalBuilding.IsometryGroups
import Atlas.Buildings.code.SphericalBuilding.Oriflamme

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace AffineIsometryBuilding

open DVRContext


variable (C : DVRContext)

/-- A primitive lattice $\Lambda$ over $\mathfrak{o}$ on which the
bilinear form $B$ is alternating: $B(v, v) = 0$ for every $v$. -/
structure PrimitiveLatticeAlternating extends DVRContext.PrimitiveLattice C where
  form_alternating : ∀ v : Fin C.n → C.k, form v v = 0

/-- The dual of an $\mathfrak{o}$-lattice $\Lambda$ with respect to $B$:
$\Lambda^\# = \{v : B(v, w) \in \mathfrak{m} \text{ for all } w \in \Lambda\}$. -/
def dualLattice (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Set (Fin C.n → C.k) :=
  { v | ∀ w ∈ Λ.carrier, C.isInMaxIdeal (B v w) }

/-- $\Lambda_1 \subseteq \Lambda_2$ as sets of vectors in $k^n$. -/
def latticeContained (Λ₁ Λ₂ : OLattice C) : Prop :=
  ∀ v ∈ Λ₁.carrier, v ∈ Λ₂.carrier

/-- The bilinear form $B$ takes values in the maximal ideal on $\Lambda$:
$B(v, w) \in \mathfrak{m}$ for all $v, w \in \Lambda$. -/
def formValuesInMaxIdeal (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∀ v ∈ Λ.carrier, ∀ w ∈ Λ.carrier, C.isInMaxIdeal (B v w)

/-- A lattice $\Lambda$ is a vertex of the affine alternating-form
building if there exists a sublattice $\Lambda_0 \subseteq \Lambda$ such
that $B$ is integral on $\Lambda_0$, takes values in $\mathfrak{m}$ on
$\Lambda$, and the uniformizer multiplied by any element of $\Lambda$
lands in $\Lambda_0$ (so $\Lambda / \Lambda_0$ has bounded denominator). -/
def IsAffineAlternatingVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ₀ Λ ∧

    formValuesInMaxIdeal C B Λ ∧


    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧


    (∀ v ∈ Λ.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier)

/-- Incidence relation for the affine alternating-form building: two
lattices $\Lambda_1, \Lambda_2$ are incident if there is a common
$\Lambda_0$ on which $B$ is integral, the uniformizer maps either
$\Lambda_i$ into $\Lambda_0$, and one of $\Lambda_1, \Lambda_2$ is
contained in the other. -/
def AffineAlternatingIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    latticeContained C Λ₀ Λ₁ ∧
    (∀ v ∈ Λ₁.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    latticeContained C Λ₀ Λ₂ ∧
    (∀ v ∈ Λ₂.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    (latticeContained C Λ₁ Λ₂ ∨ latticeContained C Λ₂ Λ₁)

/-- The affine alternating-form building: a simplicial complex of
$\mathfrak{o}$-lattices in $k^n$ whose vertices satisfy
`IsAffineAlternatingVertex`, whose simplices are pairwise incident, and
whose face set is downward closed under nonempty subsets. -/
structure AffineAlternatingComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ, IsAffineAlternatingVertex C B Λ
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    AffineAlternatingIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices

/-- A symplectic frame for an alternating form $B$: $m$ pairs of isotropic
lines indexed by $\mathrm{Fin}\,m \times \mathrm{Bool}$ such that within
each pair $(i, \mathrm{true}), (i, \mathrm{false})$ the pairing
$B(\ell_{i,\mathrm{true}}, \ell_{i,\mathrm{false}})$ is a unit, and lines
with different indices are orthogonal. -/
structure FrameAlternating (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) where
  lines : Fin m × Bool → Fin C.n → C.k
  lines_isotropic : ∀ ib, B (lines ib) (lines ib) = 0
  lines_pairing : ∀ i : Fin m, C.isUnitInO (B (lines (i, true)) (lines (i, false)))
  lines_orthogonal : ∀ i j : Fin m, i ≠ j → ∀ s t : Bool,
    B (lines (i, s)) (lines (j, t)) = 0

/-- A lattice $\Lambda$ lies in the apartment of a symplectic frame $F$
if it admits a description as $\mathfrak{o}$-span of the frame lines
scaled by nonzero scalars (one per frame line). -/
def IsInAlternatingApartment (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) (F : FrameAlternating C B m) (Λ : OLattice C) : Prop :=
  ∃ (scalars : Fin m × Bool → C.𝔬),

    (∀ ib, scalars ib ≠ 0) ∧

    Λ.carrier = { v | ∃ c : Fin m × Bool → C.𝔬,
      v = fun idx => ∑ ib : Fin m × Bool,
        C.embed (c ib * scalars ib) * F.lines ib idx }


/-- A lattice $\Lambda$ is a vertex of the double oriflamme building (type
$\tilde D_n$) of $B$ if it admits a sublattice $\Lambda_0$ satisfying the
same containment / integrality / uniformizer conditions as in the
alternating case, plus a "doubling" condition certifying that $\Lambda$
is one of the two lattices arising in an oriflamme split. -/
def IsDoubleOriflammeVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) (_halfDim : ℕ) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ₀ Λ ∧

    formValuesInMaxIdeal C B Λ ∧

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    (∀ v ∈ Λ.carrier, C.oscal C.uniformizer v ∈ Λ₀.carrier) ∧

    (¬ (∀ v ∈ Λ.carrier, v ∈ Λ₀.carrier) ∨
      ∃ v ∈ Λ.carrier, ∃ w ∈ Λ.carrier,
        ¬ ∃ (r : C.𝔬) (u : Fin C.n → C.k),
          u ∈ Λ₀.carrier ∧ (fun i => v i - C.embed r * w i) = u)

/-- Incidence relation for the double oriflamme building: either the
underlying alternating-form incidence, or an oriflamme incidence where
$\Lambda_1, \Lambda_2$ share a common $\Lambda_0$ and differ by a single
direction $d \in \Lambda_1 \setminus \Lambda_2$. -/
def DoubleOriflammeIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=

  AffineAlternatingIncidence C B Λ₁ Λ₂ ∨


  (∃ (Λ₀ : OLattice C),
    latticeContained C Λ₀ Λ₁ ∧
    latticeContained C Λ₀ Λ₂ ∧


    Λ₁.carrier ≠ Λ₂.carrier ∧


    ∃ d : Fin C.n → C.k,
      d ∈ Λ₁.carrier ∧ d ∉ Λ₂.carrier ∧
      (∀ v ∈ Λ₁.carrier, ∃ w ∈ Λ₂.carrier, ∃ r : C.𝔬,
        v = fun i => w i + C.embed r * d i))

/-- The double oriflamme building of $B$ (type $\tilde D_n$): a
simplicial complex of $\mathfrak{o}$-lattices whose vertices are
`IsDoubleOriflammeVertex`, simplices are pairwise oriflamme-incident,
and faces are closed under nonempty subsets. -/
structure DoubleOriflammeComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ,
    IsDoubleOriflammeVertex C B Λ halfDim
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    DoubleOriflammeIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- A lattice $\Lambda$ is a vertex of the single oriflamme building
(type $\tilde B_n$) of $B$ if there is a superlattice $\Lambda_0 \supseteq
\Lambda$ such that the uniformizer maps $\Lambda_0$ into $\Lambda$, $B$
is integral on $\Lambda_0$, every non-divisible element of $\Lambda_0$
has a unit pairing with some other element, and $B$ takes values in
$\mathfrak{m}$ on $\Lambda$. -/
def IsSingleOriflammeVertex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ : OLattice C) : Prop :=
  ∃ (Λ₀ : OLattice C),

    latticeContained C Λ Λ₀ ∧

    (∀ v ∈ Λ₀.carrier, C.oscal C.uniformizer v ∈ Λ.carrier) ∧

    (∀ v ∈ Λ₀.carrier, ∀ w ∈ Λ₀.carrier, C.isInO (B v w)) ∧

    (∀ v ∈ Λ₀.carrier,
      (¬ ∃ w ∈ Λ₀.carrier, v = C.oscal C.uniformizer w) →
      ∃ w ∈ Λ₀.carrier, C.isUnitInO (B v w)) ∧

    formValuesInMaxIdeal C B Λ

/-- Incidence in the single oriflamme building: either the alternating
incidence relation, or both lattices are integral for $B$ and differ by
exactly one direction $d \in \Lambda_1 \setminus \Lambda_2$. -/
def SingleOriflammeIncidence (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (Λ₁ Λ₂ : OLattice C) : Prop :=

  AffineAlternatingIncidence C B Λ₁ Λ₂ ∨

  (
   (∀ v ∈ Λ₁.carrier, ∀ w ∈ Λ₁.carrier, C.isInO (B v w)) ∧
   (∀ v ∈ Λ₂.carrier, ∀ w ∈ Λ₂.carrier, C.isInO (B v w)) ∧

   Λ₁.carrier ≠ Λ₂.carrier ∧
   ∃ d : Fin C.n → C.k,
     d ∈ Λ₁.carrier ∧ d ∉ Λ₂.carrier ∧
     (∀ v ∈ Λ₁.carrier, ∃ w ∈ Λ₂.carrier, ∃ r : C.𝔬,
       v = fun i => w i + C.embed r * d i))

/-- The single oriflamme building of $B$ (type $\tilde B_n$): a
simplicial complex of lattices whose vertices are
`IsSingleOriflammeVertex`, simplices are pairwise single-oriflamme
incident, and faces are downward closed under nonempty subsets. -/
structure SingleOriflammeComplex (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) where
  simplices : Set (Finset (OLattice C))
  vertex_condition : ∀ σ ∈ simplices, ∀ Λ ∈ σ,
    IsSingleOriflammeVertex C B Λ
  pairwise_incident : ∀ σ ∈ simplices, ∀ Λ₁ ∈ σ, ∀ Λ₂ ∈ σ,
    SingleOriflammeIncidence C B Λ₁ Λ₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (OLattice C),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- The alternating-form simplicial complex is a thick building: any two
simplices lie in a common apartment described by some symplectic frame,
and every panel is contained in at least three distinct chambers. -/
def AlternatingIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : AffineAlternatingComplex C B) : Prop :=

  (∀ σ₁ ∈ X.simplices, ∀ σ₂ ∈ X.simplices,
    ∃ (m : ℕ) (F : FrameAlternating C B m),
      (∀ Λ ∈ σ₁, IsInAlternatingApartment C B m F Λ) ∧
      (∀ Λ ∈ σ₂, IsInAlternatingApartment C B m F Λ)) ∧

  (∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃)

/-- Thickness for the double oriflamme building: every panel is contained
in at least three pairwise-distinct chambers. -/
def DoubleOriflammeIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) (X : DoubleOriflammeComplex C B halfDim) : Prop :=

  ∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃

/-- Thickness for the single oriflamme building: every panel is contained
in at least three pairwise-distinct chambers. -/
def SingleOriflammeIsThickBuilding
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : SingleOriflammeComplex C B) : Prop :=

  ∀ panel ∈ X.simplices,
    ∃ C₁ C₂ C₃ : Finset (OLattice C),
      C₁ ∈ X.simplices ∧ C₂ ∈ X.simplices ∧ C₃ ∈ X.simplices ∧
      panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃


/-- An element $g \in GL_n(k)$ is an isometry of the bilinear form $B$ if
$B(gv, gw) = B(v, w)$ for all $v, w \in k^n$. -/
def IsIsometry (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (g : GL (Fin C.n) C.k) : Prop :=
  ∀ v w : Fin C.n → C.k, B (fun i => ∑ j, g.val i j * v j) (fun i => ∑ j, g.val i j * w j) = B v w

/-- The isometry group of $B$ as a subset of $GL_n(k)$. -/
def IsometryGroupSet (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k) : Set C.GL_n_k :=
  { g | IsIsometry C B g }

/-- The image $g \cdot \Lambda$ of a lattice $\Lambda$ under
$g \in GL_n(k)$, as a set of vectors. -/
def GLImageLatticeCarrier (g : C.GL_n_k) (Λ : OLattice C) :
    Set (Fin C.n → C.k) :=
  { w | ∃ v ∈ Λ.carrier, w = fun i => ∑ j, g.val i j * v j }

/-- $g \in GL_n(k)$ maps simplex $\sigma_1$ to simplex $\sigma_2$ if for
every lattice $\Lambda \in \sigma_1$ there is some $\Lambda' \in \sigma_2$
with $g \cdot \Lambda = \Lambda'$ as sets. -/
def GLMapsSimplex (g : C.GL_n_k)
    (σ₁ σ₂ : Finset (OLattice C)) : Prop :=
  ∀ Λ ∈ σ₁, ∃ Λ' ∈ σ₂, GLImageLatticeCarrier C g Λ = Λ'.carrier

/-- $g \in GL_n(k)$ maps the apartment of frame $F_1$ to that of $F_2$ if
every lattice in the $F_1$-apartment has its $g$-image in the
$F_2$-apartment. -/
def GLMapsAlternatingApartment
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (m : ℕ) (g : C.GL_n_k)
    (F₁ F₂ : FrameAlternating C B m) : Prop :=
  ∀ Λ : OLattice C,
    IsInAlternatingApartment C B m F₁ Λ →
    ∃ Λ' : OLattice C,
      GLImageLatticeCarrier C g Λ = Λ'.carrier ∧
      IsInAlternatingApartment C B m F₂ Λ'

/-- Strong transitivity for the alternating-form building: the isometry
group acts transitively on pairs (apartment, simplex inside that
apartment). -/
def StrongTransitivityAlternating
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : AffineAlternatingComplex C B)
    (m : ℕ) : Prop :=
  ∀ (F₁ F₂ : FrameAlternating C B m)
    (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    (∀ Λ ∈ σ₁, IsInAlternatingApartment C B m F₁ Λ) →
    (∀ Λ ∈ σ₂, IsInAlternatingApartment C B m F₂ Λ) →
    ∃ g ∈ IsometryGroupSet C B,

      GLMapsAlternatingApartment C B m g F₁ F₂

/-- Strong transitivity for the double oriflamme building: the isometry
group acts transitively on simplices of the complex. -/
def StrongTransitivityDoubleOriflamme
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (halfDim : ℕ) (X : DoubleOriflammeComplex C B halfDim) : Prop :=
  ∀ (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    ∃ g ∈ IsometryGroupSet C B, GLMapsSimplex C g σ₁ σ₂

/-- Strong transitivity for the single oriflamme building: the isometry
group acts transitively on simplices of the complex. -/
def StrongTransitivitySingleOriflamme
    (B : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k)
    (X : SingleOriflammeComplex C B) : Prop :=
  ∀ (σ₁ : Finset (OLattice C)), σ₁ ∈ X.simplices →
    ∀ (σ₂ : Finset (OLattice C)), σ₂ ∈ X.simplices →
    ∃ g ∈ IsometryGroupSet C B, GLMapsSimplex C g σ₁ σ₂

end AffineIsometryBuilding
