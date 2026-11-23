/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.Labels
import Atlas.Buildings.code.Building.RetractionDef
import Atlas.Buildings.code.Building.ApartmentsCoxeter

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

namespace Building

/-- A **group action on a building**: a group $G$ acting on the vertex set $V$ that respects
the simplicial structure (faces map to faces) and the apartment system (apartments map to
apartments), plus the usual group action axioms. This packages the geometric "type II" action
of a group on a building used to build a BN-pair from a strongly transitive action. -/
structure GroupAction (G : Type*) [Group G] (b : Building V) where
  smul : G → V → V
  smul_one : ∀ v, smul 1 v = v
  smul_mul : ∀ (g₁ g₂ : G) (v : V), smul (g₁ * g₂) v = smul g₁ (smul g₂ v)
  smul_face : ∀ (g : G) (s : Finset V),
    s ∈ b.toChamberComplex.toSimplicialComplex.faces →
    s.image (smul g) ∈ b.toChamberComplex.toSimplicialComplex.faces
  smul_apartment : ∀ (g : G) (A : SimplicialComplex V),
    A ∈ b.apartmentSystem.apartments →
    ∃ A' ∈ b.apartmentSystem.apartments,
      A'.faces = { s | ∃ t ∈ A.faces, s = t.image (smul g) }

namespace GroupAction

variable {G : Type*} [Group G] {b : Building V} (act : GroupAction G b)

/-- The action of $g \in G$ on a finite face $s$: the image of $s$ under $v \mapsto g \cdot v$. -/
def smulFace (g : G) (s : Finset V) : Finset V :=
  s.image (act.smul g)

/-- The action of $g \in G$ on a set of faces $F$: image of $F$ under `smulFace g`. -/
def smulFaces (g : G) (F : Set (Finset V)) : Set (Finset V) :=
  { s | ∃ t ∈ F, s = act.smulFace g t }

/-- Compatibility with multiplication: $(g_1 g_2) \cdot s = g_1 \cdot (g_2 \cdot s)$ on faces. -/
lemma smulFace_mul (g₁ g₂ : G) (s : Finset V) :
    act.smulFace (g₁ * g₂) s = act.smulFace g₁ (act.smulFace g₂ s) := by
  simp only [smulFace]
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hv⟩
    exact ⟨act.smul g₂ w, ⟨w, hw, rfl⟩, by rw [← act.smul_mul]; exact hv⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, hv⟩
    exact ⟨u, hu, by rw [act.smul_mul]; exact hv⟩

/-- Identity acts trivially on faces: $1 \cdot s = s$. -/
lemma smulFace_one (s : Finset V) :
    act.smulFace 1 s = s := by
  simp only [smulFace]
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hv⟩; rw [act.smul_one] at hv; rw [← hv]; exact hw
  · intro hv; exact ⟨v, hv, act.smul_one v⟩

/-- Compatibility with multiplication on sets of faces: $(g_1 g_2) \cdot F = g_1 \cdot (g_2 \cdot F)$. -/
lemma smulFaces_mul (g₁ g₂ : G) (F : Set (Finset V)) :
    act.smulFaces (g₁ * g₂) F = act.smulFaces g₁ (act.smulFaces g₂ F) := by
  ext s; simp only [smulFaces, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨act.smulFace g₂ t, ⟨t, ht, rfl⟩, smulFace_mul act g₁ g₂ t⟩
  · rintro ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (smulFace_mul act g₁ g₂ t).symm⟩

/-- Identity acts trivially on sets of faces: $1 \cdot F = F$. -/
lemma smulFaces_one (F : Set (Finset V)) :
    act.smulFaces 1 F = F := by
  ext s; simp only [smulFaces, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩; rwa [smulFace_one]
  · intro hs; exact ⟨s, hs, (smulFace_one act s).symm⟩

/-- The action is **type-preserving** with respect to a labelling $\lambda : \text{faces} \to L$
if every $g \in G$ sends each face to one with the same label. This is the property that
forces the BN-pair built from the action to have its $\pi$-projection well-defined. -/
def IsTypePreserving {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ (g : G) (s : Finset V),
    s ∈ b.toChamberComplex.toSimplicialComplex.faces →
    lab.labelMap (act.smulFace g s) = lab.labelMap s

/-- The action is **strongly transitive**: for any two pairs $(A_1, C_1)$, $(A_2, C_2)$ of
an apartment together with one of its chambers, some $g \in G$ sends $A_1 \to A_2$ and
$C_1 \to C_2$. This is the geometric hypothesis used to build a BN-pair from the action. -/
def IsStronglyTransitive : Prop :=
  ∀ (A₁ A₂ : SimplicialComplex V) (C₁ C₂ : Finset V),
    A₁ ∈ b.apartmentSystem.apartments →
    A₂ ∈ b.apartmentSystem.apartments →
    A₁.IsMaximal C₁ → A₂.IsMaximal C₂ →
    ∃ g : G,
      act.smulFaces g A₁.faces = A₂.faces ∧
      act.smulFace g C₁ = C₂

/-- The **chamber stabilizer** $\mathrm{Stab}_G(C_0) = \{g \in G : g \cdot C_0 = C_0\}$,
the subgroup that fixes the chamber $C_0$ setwise. This will become the Borel subgroup $B$. -/
def chamberStabilizer (C₀ : Finset V) : Subgroup G where
  carrier := { g | act.smulFace g C₀ = C₀ }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFace_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFace_one act C₀
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFace a⁻¹ (act.smulFace a C₀) = C₀ := by
      rw [← smulFace_mul]; simp [smulFace_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **apartment stabilizer** $\mathrm{Stab}_G(A_0)$: the subgroup of $G$ that maps the
apartment $A_0$ to itself setwise. This will become the subgroup $N$ of the BN-pair. -/
def apartmentStabilizer (A₀ : SimplicialComplex V) : Subgroup G where
  carrier := { g | act.smulFaces g A₀.faces = A₀.faces }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFaces_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFaces_one act A₀.faces
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFaces a⁻¹ (act.smulFaces a A₀.faces) = A₀.faces := by
      rw [← smulFaces_mul]; simp [smulFaces_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **torus** $T = \mathrm{Stab}_G(C_0) \cap \mathrm{Stab}_G(A_0)$: the subgroup fixing
both the base chamber and the base apartment. This will become the torus $T = B \cap N$. -/
def torus (C₀ : Finset V) (A₀ : SimplicialComplex V) : Subgroup G :=
  act.chamberStabilizer C₀ ⊓ act.apartmentStabilizer A₀

/-- The **face stabilizer** of an arbitrary face $F$: $\mathrm{Stab}_G(F) = \{g \in G :
g \cdot F = F\}$. Specializes to `chamberStabilizer` when $F$ is a chamber. -/
def faceStabilizer (F : Finset V) : Subgroup G where
  carrier := { g | act.smulFace g F = F }
  mul_mem' := by
    intro a c ha hc; simp only [Set.mem_setOf_eq] at *
    rw [smulFace_mul, hc, ha]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact smulFace_one act F
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    have h1 : act.smulFace a⁻¹ (act.smulFace a F) = F := by
      rw [← smulFace_mul]; simp [smulFace_one, inv_mul_cancel]
    rwa [ha] at h1

/-- The **geometric standard parabolic** $P_{S'}$ as the stabilizer of the subface of $C_0$
spanned by the vertices whose label lies in $S' \subseteq L$. Matches the algebraic
$P_{S'} = BW_{S'}B$ under the BN-pair built from the action. -/
def standardParabolic {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (C₀ : Finset V) (S' : Finset L) : Subgroup G :=
  act.faceStabilizer (C₀.filter (fun v => lab.labelMap {v} ⊆ S'))

/-- Predicate: $g$ and $w$ land in the same Bruhat double coset $BwB$ as measured by the
retraction $\rho$ onto the base apartment; specifically, $\rho(g \cdot C_0) = w \cdot C_0$
in the apartment. -/
def bruhatCosetFromRetraction
    (ρ : BuildingRetraction b) (C₀ : Finset V) (g w : G) : Prop :=
  (act.smulFace g C₀).image ρ.map = act.smulFace w C₀

end GroupAction

end Building

/-- **The data needed to build a BN-pair from a strongly transitive action on a building.**
Packages: a `GroupAction` of $G$ on the building $b$, a chosen base apartment $A_0$ with
chamber $C_0$, a bijection $\varphi : \text{chambers of } A_0 \to W$ with $\varphi(C_0) = 1$
that intertwines the $N$-action with left multiplication, and the Bruhat-style hypothesis
$G = B \cdot N \cdot B$. From this data one extracts the strict BN-pair $(B, N, T, \pi)$. -/
structure BNPairFromBuildingData
    {V : Type*} [DecidableEq V]
    (G : Type*) [Group G]
    (b : Building V)
    (ct : Building.CoxeterTypeOfBuilding b) where
  act : Building.GroupAction G b
  A₀ : SimplicialComplex V
  hA₀ : A₀ ∈ b.apartmentSystem.apartments
  C₀ : Finset V
  hC₀_max_A₀ : A₀.IsMaximal C₀
  φ : Finset V → ct.matrix.Group
  φ_inj : ∀ C, A₀.IsMaximal C → ∀ D, A₀.IsMaximal D → φ C = φ D → C = D
  φ_surj : ∀ w : ct.matrix.Group, ∃ C, A₀.IsMaximal C ∧ φ C = w
  φ_base : φ C₀ = 1
  strongly_transitive : act.IsStronglyTransitive
  smul_preserves_apt_max : ∀ (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (C : Finset V) (_ : A₀.IsMaximal C),
    A₀.IsMaximal (act.smulFace n C)
  φ_equivariant : ∀ (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (C : Finset V) (_ : A₀.IsMaximal C),
    φ (act.smulFace n C) = φ (act.smulFace n C₀) * φ C
  bruhat_decomp : ∀ g : G, ∃ (b₁ : G) (_ : act.smulFace b₁ C₀ = C₀)
    (n : G) (_ : act.smulFaces n A₀.faces = A₀.faces)
    (b₂ : G) (_ : act.smulFace b₂ C₀ = C₀),
    g = b₁ * n * b₂

namespace BNPairFromBuildingData

variable {V : Type*} [DecidableEq V]
  {G : Type*} [Group G]
  {b : Building V}
  {ct : Building.CoxeterTypeOfBuilding b}
  (data : BNPairFromBuildingData G b ct)

/-- The **Borel subgroup** $B$: the stabilizer of the base chamber $C_0$. -/
def B : Subgroup G := data.act.chamberStabilizer data.C₀

/-- The **subgroup $N$**: the stabilizer of the base apartment $A_0$. -/
def N : Subgroup G := data.act.apartmentStabilizer data.A₀

/-- The **torus** $T$: stabilizer of both $C_0$ and $A_0$, i.e. $T = B \cap N$. -/
def T : Subgroup G := data.act.torus data.C₀ data.A₀

/-- Definitional unfolding: $T = B \cap N$. -/
lemma T_eq_inf : data.T = data.B ⊓ data.N := rfl

/-- The underlying function of the projection $\pi : N \to W$: send $n \in N$ to
$\varphi(n \cdot C_0)$, i.e. the chamber of $A_0$ that $n$ maps $C_0$ to, read off as a
Weyl group element via $\varphi$. -/
def πFun (n : data.N) : ct.matrix.Group :=
  data.φ (data.act.smulFace (n : G) data.C₀)

/-- Multiplicativity of $\pi$: $\pi(n_1 n_2) = \pi(n_1) \pi(n_2)$, using the equivariance of
$\varphi$ under the $N$-action on the chambers of $A_0$. -/
lemma πFun_mul (n₁ n₂ : data.N) :
    data.πFun (n₁ * n₂) = data.πFun n₁ * data.πFun n₂ := by
  simp only [πFun]

  have hmul : data.act.smulFace ((n₁ : G) * (n₂ : G)) data.C₀ =
    data.act.smulFace (n₁ : G) (data.act.smulFace (n₂ : G) data.C₀) :=
    data.act.smulFace_mul _ _ _
  rw [show ((n₁ * n₂ : data.N) : G) = (n₁ : G) * (n₂ : G) from rfl]
  rw [hmul]

  have hn₂ : data.act.smulFaces (n₂ : G) data.A₀.faces = data.A₀.faces := n₂.2
  have hmax₂ : data.A₀.IsMaximal (data.act.smulFace (n₂ : G) data.C₀) :=
    data.smul_preserves_apt_max _ hn₂ _ data.hC₀_max_A₀

  exact data.φ_equivariant (n₁ : G) n₁.2 _ hmax₂

/-- The Weyl projection $\pi : N \to W$ as a group homomorphism, packaging `πFun` with its
multiplicativity and unit-preservation. -/
def π : data.N →* ct.matrix.Group where
  toFun := data.πFun
  map_one' := by
    simp only [πFun]
    rw [show ((1 : data.N) : G) = (1 : G) from rfl]
    rw [data.act.smulFace_one]
    exact data.φ_base
  map_mul' := data.πFun_mul

/-- Surjectivity of $\pi$: every $w \in W$ is realized by some $n \in N$. Uses strong
transitivity of $G$ on apartment-chamber pairs to find an element moving $C_0$ to the
chamber corresponding to $w$ in $A_0$. -/
lemma π_surj : Function.Surjective data.π := by
  intro w

  obtain ⟨Cw, hCw_max, hCw_φ⟩ := data.φ_surj w

  obtain ⟨g, hg_apt, hg_ch⟩ := data.strongly_transitive data.A₀ data.A₀ data.C₀ Cw
    data.hA₀ data.hA₀ data.hC₀_max_A₀ hCw_max

  have hgN : g ∈ data.N := hg_apt

  exact ⟨⟨g, hgN⟩, by simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun, hg_ch, hCw_φ]⟩

/-- **Kernel of $\pi$ equals $T$.** $\pi(n) = 1$ iff $n$ fixes $C_0$ (forwards: $\varphi$ is
injective on chambers, so $n \cdot C_0 = C_0$; backwards: $T = B \cap N$ fixes $C_0$ and
$\varphi(C_0) = 1$). -/
lemma π_ker (n : data.N) : data.π n = 1 ↔ (n : G) ∈ data.T := by
  constructor
  · intro h

    have h1 : data.φ (data.act.smulFace (n : G) data.C₀) = data.φ data.C₀ := by
      simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun] at h
      rw [h, data.φ_base]

    have hn : data.act.smulFaces (n : G) data.A₀.faces = data.A₀.faces := n.2
    have hmax : data.A₀.IsMaximal (data.act.smulFace (n : G) data.C₀) :=
      data.smul_preserves_apt_max _ hn _ data.hC₀_max_A₀

    have h2 : data.act.smulFace (n : G) data.C₀ = data.C₀ :=
      data.φ_inj _ hmax _ data.hC₀_max_A₀ h1

    show (n : G) ∈ data.act.chamberStabilizer data.C₀ ⊓ data.act.apartmentStabilizer data.A₀
    exact ⟨h2, n.2⟩
  · intro h

    obtain ⟨hB, _⟩ := h
    simp only [π, MonoidHom.coe_mk, OneHom.coe_mk, πFun]

    rw [hB, data.φ_base]

/-- $B$ and $N$ generate $G$: a direct consequence of the Bruhat-style decomposition
$G = B \cdot N \cdot B$ supplied by `bruhat_decomp`. -/
lemma generates : Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, hg⟩ := data.bruhat_decomp g
  rw [hg]
  have hb₁_mem : b₁ ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_left _ hb₁)
  have hn_mem : n ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_right _ hn)
  have hb₂_mem : b₂ ∈ Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) :=
    Subgroup.subset_closure (Set.mem_union_left _ hb₂)
  exact mul_mem (mul_mem hb₁_mem hn_mem) hb₂_mem

/-- **The strict BN-pair built from the building data.** Bundles $B$, $N$, $T = B \cap N$,
the surjective homomorphism $\pi : N \to W$ with kernel $T$, and the generation property
$\langle B, N \rangle = G$, producing a `BNPair G ct.matrix`. -/
def toBNPair : BNPair G ct.matrix where
  B := data.B
  N := data.N
  T := data.T
  T_eq := data.T_eq_inf
  π := data.π
  π_surj := data.π_surj
  π_ker := data.π_ker
  generates := data.generates

end BNPairFromBuildingData
