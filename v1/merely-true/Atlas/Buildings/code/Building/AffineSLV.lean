/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Valuation.LatticesValuations
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.Affine

set_option linter.unusedSectionVars false

namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- Two $\mathfrak{o}$-lattices $\Lambda, \Lambda'$ in $V = k^n$ are homothetic if
$\Lambda' = c \Lambda$ for some $c \in k^\times$. -/
def IsHomothetic (Λ Λ' : DVRContext.OLattice C) : Prop :=
  DVRContext.OLattice.IsHomothetic C Λ Λ'

/-- The scaled lattice $\pi \Lambda = \{\pi v : v \in \Lambda\}$ obtained by
scaling $\Lambda$ by the uniformizer $\pi$. -/
def πLattice (hπ : C.embed C.uniformizer ≠ 0)
    (Λ : DVRContext.OLattice C) : DVRContext.OLattice C where
  carrier := {v | ∃ w ∈ Λ.carrier, v = C.oscal C.uniformizer w}
  zero_mem := ⟨0, Λ.zero_mem, by funext i; simp [DVRContext.oscal]⟩
  add_mem := by
    intro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
    exact ⟨wx + wy, Λ.add_mem hwx hwy, by
      funext i; simp only [Pi.add_apply, hx, hy, DVRContext.oscal]; ring⟩
  smul_mem := by
    intro r x ⟨w, hw, hx⟩
    exact ⟨C.oscal r w, Λ.smul_mem r hw, by
      funext i; simp only [hx, DVRContext.oscal]; ring⟩
  spans_V := by
    intro v
    obtain ⟨m, cs, vs, hvs, hv⟩ := Λ.spans_V v
    refine ⟨m, fun j => cs j * (C.embed C.uniformizer)⁻¹,
            fun j => C.oscal C.uniformizer (vs j), ?_, ?_⟩
    · intro j; exact ⟨vs j, hvs j, rfl⟩
    · rw [hv]; congr 1; funext j; funext i
      simp only [Pi.smul_apply, DVRContext.oscal, smul_eq_mul]
      rw [mul_assoc, ← mul_assoc (C.embed C.uniformizer)⁻¹,
          inv_mul_cancel₀ hπ, one_mul]
  closed_under_o_combination := by
    intro coeffs vectors hcoeffs hvecs
    have hwit : ∀ i, ∃ w ∈ Λ.carrier, vectors i = C.oscal C.uniformizer w := hvecs
    choose ws hws_mem hws_eq using hwit
    have hsum : ∑ i, coeffs i • vectors i =
        C.oscal C.uniformizer (∑ i, coeffs i • ws i) := by
      simp only [hws_eq]; funext j
      simp only [DVRContext.oscal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [hsum]
    exact ⟨∑ i, coeffs i • ws i,
           Λ.closed_under_o_combination coeffs ws hcoeffs hws_mem, rfl⟩

/-- The scaled lattice $\pi \Lambda$ is homothetic to $\Lambda$ with scaling
factor $\pi$. -/
theorem πLattice_homothetic (hπ : C.embed C.uniformizer ≠ 0)
    (Λ : DVRContext.OLattice C) :
    IsHomothetic C (πLattice C hπ Λ) Λ :=
  ⟨C.embed C.uniformizer, hπ, rfl⟩

/-- Incidence of $\mathfrak{o}$-lattices: $y \subseteq x$ and
$\pi x \subseteq y$. This makes $x/y$ an $\mathfrak{o}/\mathfrak{m}$-vector
space, encoding the simplicial relation in the Bruhat-Tits building. -/
def OLattice.IsIncident (x y : DVRContext.OLattice C) : Prop :=
  y.carrier ⊆ x.carrier ∧ ∀ v ∈ x.carrier, C.oscal C.uniformizer v ∈ y.carrier

/-- Symmetry of incidence at the level of lattices (up to scaling by $\pi$): if
$x \supseteq y \supseteq \pi x$, then $y \supseteq \pi x \supseteq \pi y$. -/
theorem OLattice.incident_symm_lattice
    (hπ : C.embed C.uniformizer ≠ 0)
    (x y : DVRContext.OLattice C) (h : OLattice.IsIncident C x y) :
    OLattice.IsIncident C y (πLattice C hπ x) := by
  obtain ⟨hyx, hπxy⟩ := h
  exact ⟨fun v ⟨w, hw, hv⟩ => hv ▸ hπxy w hw,
         fun v hv => ⟨v, hyx hv, rfl⟩⟩

/-- Incidence relation on homothety classes: two classes $[\Lambda], [\Lambda']$
are incident if they are equal or have representatives $x \in [\Lambda]$,
$y \in [\Lambda']$ that are incident in the lattice sense. -/
def IncidenceRel (ξ η : DVRContext.HomothetyClass C) : Prop :=
  ξ = η ∨
  ∃ x y : DVRContext.OLattice C,
    Quot.mk _ x = ξ ∧ Quot.mk _ y = η ∧ OLattice.IsIncident C x y

/-- A simplex of the Bruhat-Tits building of $SL_V$ is a finite set of pairwise
incident homothety classes of $\mathfrak{o}$-lattices in $V$. -/
structure Simplex where
  vertices : Finset (DVRContext.HomothetyClass C)
  mutually_incident : ∀ ξ ∈ vertices, ∀ η ∈ vertices, IncidenceRel C ξ η

/-- A line in $V = k^n$ is a one-dimensional subspace, represented here by a
nonzero generator. -/
structure Line where
  generator : Fin C.n → C.k
  generator_ne_zero : generator ≠ 0

/-- A frame in $V = k^n$ is an ordered family of $n$ lines that spans $V$
and is linearly independent: a decomposition $V = L_1 \oplus \cdots \oplus
L_n$ into lines. -/
structure Frame where
  lines : Fin C.n → Line C
  spans : ∀ v : Fin C.n → C.k,
    ∃ coeffs : Fin C.n → C.k,
      v = fun i => ∑ j, coeffs j * (lines j).generator i
  independent : ∀ coeffs : Fin C.n → C.k,
    (fun i => ∑ j : Fin C.n, coeffs j * (lines j).generator i) = 0 →
    ∀ j, coeffs j = 0

/-- A lattice $\Lambda$ is decomposable with respect to a frame
$F = (L_1, \ldots, L_n)$ if $\Lambda = \bigoplus_j s_j \mathfrak{o} v_j$ for
some scalars $s_j \in k^\times$ and chosen generators $v_j$ of the lines. -/
def IsDecomposableWrtFrame (F : Frame C) (Λ : DVRContext.OLattice C) : Prop :=
  ∃ scales : Fin C.n → C.k,
    (∀ j, scales j ≠ 0) ∧
    Λ.carrier = {v | ∃ c : Fin C.n → C.𝔬,
      v = fun i => ∑ j, C.embed (c j) * scales j * (F.lines j).generator i}

/-- The apartment $A_F$ associated to a frame $F$: the set of simplices all of
whose vertices are classes of frame-decomposable lattices. -/
def Apartment (F : Frame C) : Set (Simplex C) :=
  {σ | ∀ ξ ∈ σ.vertices,
    ∃ Λ : DVRContext.OLattice C,
      Quot.mk _ Λ = ξ ∧ IsDecomposableWrtFrame C F Λ}

/-- A periodic flag of $\mathfrak{o}$-lattices: a $\mathbb{Z}$-indexed ascending
chain $\cdots \subset \Lambda_i \subset \Lambda_{i+1} \subset \cdots$ in
$V = k^n$, periodic with period $n$ up to scaling by $\pi$, with
one-dimensional consecutive quotients. -/
structure PeriodicFlag where
  lattice : ℤ → DVRContext.OLattice C
  ascending : ∀ i : ℤ, (lattice i).carrier ⊆ (lattice (i + 1)).carrier
  periodic : ∀ i : ℤ,
    (lattice (i + C.n)).carrier =
      {v | ∃ w ∈ (lattice i).carrier, v = C.oscal C.uniformizer w}
  quotient_annihilated : ∀ i : ℤ,
    ∀ v ∈ (lattice (i + 1)).carrier,
      C.oscal C.uniformizer v ∈ (lattice i).carrier
  quotient_one_dim : ∀ i : ℤ,
    ∃ w ∈ (lattice (i + 1)).carrier,
      w ∉ (lattice i).carrier ∧
      ∀ v ∈ (lattice (i + 1)).carrier, ∃ r : C.𝔬,
        (fun j => v j - C.embed r * w j) ∈ (lattice i).carrier

/-- The vertices of a maximal simplex extracted from a periodic flag: take the
homothety classes of $\Lambda_0, \ldots, \Lambda_{n-1}$. -/
def PeriodicFlag.toVertices (pf : PeriodicFlag C) :
    Fin C.n → DVRContext.HomothetyClass C :=
  fun j => Quot.mk _ (pf.lattice (j : ℤ))

/-- A simplex is maximal (a chamber) if it has exactly $n$ vertices and cannot be
extended: any further vertex fails to be incident to at least one vertex of
$\sigma$. -/
def Simplex.IsMaximal (σ : Simplex C) : Prop :=
  σ.vertices.card = C.n ∧
  ∀ ξ : DVRContext.HomothetyClass C,
    ξ ∉ σ.vertices →
    ∃ η ∈ σ.vertices, ¬ IncidenceRel C ξ η

end AffineBuildingSLV


namespace AffineBuildingSLVAxioms

set_option linter.unusedVariables false

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- The Coxeter matrix of the affine type $\tilde A_{n-1}$ on $\mathbb{Z}/n$
generators: label $1$ on the diagonal, $3$ on edges of the cyclic Dynkin
diagram, and $2$ elsewhere. -/
def CoxeterMatrixAffineA (n : ℕ) (i j : ZMod n) : ℕ :=
  if i = j then 1
  else if i = j + 1 ∨ j = i + 1 then 3
  else 2

/-- A lattice $\Lambda'$ is a valid replacement for the $i$-th lattice of a
periodic flag $\mathit{pf}$ if it lies between
$\mathit{pf}_{i-1}$ and $\mathit{pf}_{i+1}$. -/
def IsValidReplacement (pf : AffineBuildingSLV.PeriodicFlag C)
    (i : Fin C.n) (Λ' : DVRContext.OLattice C) : Prop :=
  (pf.lattice ((i : ℤ) - 1)).carrier ⊆ Λ'.carrier ∧
  Λ'.carrier ⊆ (pf.lattice ((i : ℤ) + 1)).carrier

/-- The transposition $(i\ i+1)$ swapping the $i$-th and $(i+1)$-th vertices,
representing reflection in the facet opposite vertex $i$ of a chamber. -/
def FacetReflection (n : ℕ) (i : Fin n) : Fin n → Fin n :=
  fun j => if j = i then (if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else j)
           else if h : j.val = i.val + 1 then ⟨i.val, i.isLt⟩
           else j

/-- The vertex label of $\Lambda$ relative to a base lattice: a class in
$\mathbb{Z}/n$ encoding the "level" of $\Lambda$ in the lattice chain. -/
def VertexLabel (_base Λ : DVRContext.OLattice C) (inv_factor_sum : ℕ) : ZMod C.n :=
  (inv_factor_sum : ZMod C.n)

/-- Abstract strong-transitivity statement: given that any two maximal simplices
share a common apartment, and that apartment isomorphisms fixing a common
chamber can be extended, any chamber $\tau$ can be mapped into the reference
apartment $A_{F_0}$ by an isomorphism that fixes a chosen chamber $\sigma$. -/
theorem strong_transitivity

    (common_apt : ∀ (σ τ : AffineBuildingSLV.Simplex C),
      σ.IsMaximal C → τ.IsMaximal C →
      ∃ F, σ ∈ AffineBuildingSLV.Apartment C F ∧
           τ ∈ AffineBuildingSLV.Apartment C F)


    (apt_iso : ∀ (F₁ F₂ : AffineBuildingSLV.Frame C)
      (σ : AffineBuildingSLV.Simplex C),
      σ ∈ AffineBuildingSLV.Apartment C F₁ →
      σ ∈ AffineBuildingSLV.Apartment C F₂ →
      ∃ φ : AffineBuildingSLV.Simplex C → AffineBuildingSLV.Simplex C,
        (∀ τ ∈ AffineBuildingSLV.Apartment C F₁,
          φ τ ∈ AffineBuildingSLV.Apartment C F₂) ∧ φ σ = σ)
    (σ : AffineBuildingSLV.Simplex C) (hσ : σ.IsMaximal C)
    (F₀ : AffineBuildingSLV.Frame C) (hσF₀ : σ ∈ AffineBuildingSLV.Apartment C F₀)
    (τ : AffineBuildingSLV.Simplex C) (hτ : τ.IsMaximal C) :
    ∃ φ : AffineBuildingSLV.Simplex C → AffineBuildingSLV.Simplex C,
      φ τ ∈ AffineBuildingSLV.Apartment C F₀ ∧ φ σ = σ := by

  obtain ⟨F, hσF, hτF⟩ := common_apt σ τ hσ hτ

  obtain ⟨φ, hφ_mem, hφ_fix⟩ := apt_iso F F₀ σ hσF hσF₀

  exact ⟨φ, hφ_mem τ hτF, hφ_fix⟩


/-- A matrix over $\mathfrak{o}$ is upper-triangular modulo $\mathfrak{m}$ if
every strictly below-diagonal entry is a multiple of the uniformizer $\pi$. -/
def IsUpperTriangularModM (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, i.val > j.val →
    ∃ h : C.𝔬, g i j = C.uniformizer * h

/-- A matrix over $\mathfrak{o}$ is congruent to the identity modulo
$\mathfrak{m}$ if each entry equals the corresponding entry of the
identity matrix modulo $\pi$. -/
def IsCongruentToIdentityModM (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, ∃ h : C.𝔬,
    g i j - (if i = j then 1 else 0) = C.uniformizer * h

/-- A matrix $g$ stabilises the standard periodic flag $(\Lambda_i)_i$ if its
linear action preserves each $\Lambda_i$ setwise. -/
def StabilizesStandardFlag
    (g : Fin C.n → Fin C.n → C.𝔬)
    (pf : AffineBuildingSLV.PeriodicFlag C) : Prop :=
  ∀ i : Fin C.n, ∀ v ∈ (pf.lattice (i : ℤ)).carrier,
    (fun j => ∑ l, C.embed (g j l) * v l) ∈ (pf.lattice (i : ℤ)).carrier

/-- The identification of the Iwahori subgroup with the stabiliser of the
standard periodic flag: a pair of mutual implications between "upper
triangular mod $\pi$" and "stabilises the flag". -/
structure IwahoriIdentification (pf : AffineBuildingSLV.PeriodicFlag C) where
  stabilizer_implies_upper_tri :
    ∀ g : Fin C.n → Fin C.n → C.𝔬,
      StabilizesStandardFlag C g pf → IsUpperTriangularModM C g
  upper_tri_implies_stabilizer :
    ∀ g : Fin C.n → Fin C.n → C.𝔬,
      IsUpperTriangularModM C g → StabilizesStandardFlag C g pf

/-- The Iwahori subgroup as a subset of $M_n(\mathfrak{o})$: matrices that are
upper triangular modulo $\mathfrak{m}$. -/
def IwahoriSubgroup : Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | IsUpperTriangularModM C g}

/-- A matrix congruent to the identity mod $\mathfrak{m}$ is, in particular,
upper-triangular mod $\mathfrak{m}$. -/
theorem congruent_to_identity_is_upper_tri
    (g : Fin C.n → Fin C.n → C.𝔬)
    (hg : IsCongruentToIdentityModM C g) :
    IsUpperTriangularModM C g := by
  intro i j hij
  obtain ⟨h, hh⟩ := hg i j
  have hne : i ≠ j := Fin.ne_of_gt hij
  simp only [if_neg hne] at hh
  rw [sub_zero] at hh
  exact ⟨h, hh⟩

/-- The carrier of the $i$-th standard lattice in the standard periodic flag,
parametrising vectors whose first $i$ coordinates are in $\pi^{-1}
\mathfrak{o}$ and the remaining ones in $\mathfrak{o}$. -/
def StandardLatticeCarrier (i : Fin C.n) : Set (Fin C.n → C.k) :=
  {v | ∀ j : Fin C.n,
    if j.val < i.val then C.isInO (C.embed C.uniformizer * v j)
    else C.isInO (v j)}


/-- Abstract topology lemma: a set $B$ that equals one cell of an open-cell
partition is closed, since its complement is the open union of the other
cells. -/
theorem open_plus_decomp_implies_closed
    {α : Type*} [TopologicalSpace α]
    (B : Set α) (_hopen : IsOpen B)
    (hdecomp : ∃ (I : Type*) (cells : I → Set α),
      (∀ i, IsOpen (cells i)) ∧
      Set.univ = ⋃ i, cells i ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      ∃ i₀, cells i₀ = B) :
    IsClosed B := by
  obtain ⟨I, cells, hcells_open, hcover, hdisj, i₀, hi₀⟩ := hdecomp
  rw [← isOpen_compl_iff]
  have hBc : Bᶜ = ⋃ (i : {i // i ≠ i₀}), cells i.1 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hxB
      have hx_univ : x ∈ Set.univ := Set.mem_univ x
      rw [hcover] at hx_univ
      simp only [Set.mem_iUnion] at hx_univ
      obtain ⟨i, hi⟩ := hx_univ
      have hne : i ≠ i₀ := fun heq => hxB (hi₀ ▸ heq ▸ hi)
      exact ⟨⟨i, hne⟩, hi⟩
    · intro ⟨⟨i, hne⟩, hxi⟩ hxB
      rw [← hi₀] at hxB
      exact Set.disjoint_left.mp (hdisj i i₀ hne) hxi hxB
  rw [hBc]
  exact isOpen_iUnion (fun ⟨i, _⟩ => hcells_open i)

/-- Abstract topology lemma: a closed subset of a compact set is compact. -/
theorem closed_in_compact_is_compact
    {α : Type*} [TopologicalSpace α]
    (B K : Set α)
    (hB_closed : IsClosed B)
    (hBK : B ⊆ K)
    (hK_compact : IsCompact K) :
    IsCompact B :=
  hK_compact.of_isClosed_subset hB_closed hBK

end AffineBuildingSLVAxioms
