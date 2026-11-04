/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

set_option linter.unusedSectionVars false

namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A subspace $W \le V$ is **totally isotropic** for the bilinear form $B$ if $B(v,w) = 0$
for all $v, w \in W$. -/
def IsotropicSubspace (B : LinearMap.BilinForm k V) (W : Submodule k V) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0


/-- An **isotropic flag** for $B$: a strictly increasing chain
$W_1 \subsetneq W_2 \subsetneq \cdots \subsetneq W_{\text{len}}$ of totally isotropic subspaces. -/
structure IsotropicFlag (B : LinearMap.BilinForm k V) where
  len : ℕ
  chain : Fin len → Submodule k V
  chain_strictMono : StrictMono chain
  chain_isotropic : ∀ i, IsotropicSubspace B (chain i)


/-- An **isotropic flag complex**: an abstract simplicial complex whose simplices are finite
chains of totally isotropic subspaces of $(V, B)$, closed under nonempty subsets. -/
structure IsotropicFlagComplex (B : LinearMap.BilinForm k V) where
  simplices : Set (Finset (Submodule k V))
  simplex_isotropic : ∀ σ ∈ simplices, ∀ W ∈ σ, IsotropicSubspace B W
  simplex_chain : ∀ σ ∈ simplices, ∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (Submodule k V),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- A **hyperbolic pair** $(e, e')$ for $B$: two isotropic vectors with $B(e, e') = 1$,
spanning a hyperbolic plane. -/
structure HyperbolicPair (B : LinearMap.BilinForm k V) where
  e  : V
  e' : V
  pairing      : B e e' = 1
  e_isotropic  : B e e = 0
  e'_isotropic : B e' e' = 0

/-- A **hyperbolic frame** of rank $n$ for $B$: $n$ pairwise-orthogonal hyperbolic pairs
$\{(e_i, e_i')\}_{i < n}$ giving a Witt decomposition of an isotropic-rich subspace. -/
structure HyperbolicFrame (B : LinearMap.BilinForm k V) (n : ℕ) where
  pairs : Fin n → HyperbolicPair B
  orthogonal_ee : ∀ i j, i ≠ j → B (pairs i).e (pairs j).e = 0
  orthogonal_ee' : ∀ i j, i ≠ j → B (pairs i).e (pairs j).e' = 0
  orthogonal_e'e' : ∀ i j, i ≠ j → B (pairs i).e' (pairs j).e' = 0


/-- An **apartment** of rank $n$ in the isometry building: a hyperbolic frame together with
the set of simplices it carries. -/
structure Apartment (B : LinearMap.BilinForm k V) (n : ℕ) where
  frame : HyperbolicFrame B n
  simplices : Set (Finset (Submodule k V))


/-- The data of a **building** structure on the isotropic flag complex of $(V,B)$: a family of
apartments satisfying the common-apartment and apartment-exchange axioms (B1 and B2). -/
structure IsBuilding (B : LinearMap.BilinForm k V) (n : ℕ) where
  complex : IsotropicFlagComplex B
  apartments : Set (Apartment B n)
  apartment_subcomplex : ∀ A ∈ apartments, A.simplices ⊆ complex.simplices
  common_apartment : ∀ σ₁ ∈ complex.simplices, ∀ σ₂ ∈ complex.simplices,
    ∃ A ∈ apartments, σ₁ ∈ A.simplices ∧ σ₂ ∈ A.simplices
  apartment_exchange : ∀ A₁ ∈ apartments, ∀ A₂ ∈ apartments,
    ∀ C ∈ A₁.simplices, C ∈ A₂.simplices →
    ∃ f : Finset (Submodule k V) → Finset (Submodule k V),
      Function.Bijective f ∧
      (∀ σ ∈ A₁.simplices, f σ ∈ A₂.simplices) ∧
      (∀ σ ∈ A₁.simplices ∩ A₂.simplices, f σ = σ)


/-- A building is **thick** if every panel (codim-$1$ face of a chamber) is contained in at
least three distinct chambers. -/
def IsThick (B : LinearMap.BilinForm k V) (n : ℕ)
    (bldg : IsBuilding B n) : Prop :=
  ∀ panel ∈ bldg.complex.simplices,
    ∀ C₀ ∈ bldg.complex.simplices,
      panel ⊆ C₀ → panel.card + 1 = C₀.card →
      ∃ C₁ C₂ C₃ : Finset (Submodule k V),
        C₁ ∈ bldg.complex.simplices ∧ C₂ ∈ bldg.complex.simplices ∧
        C₃ ∈ bldg.complex.simplices ∧
        panel ⊆ C₁ ∧ panel ⊆ C₂ ∧ panel ⊆ C₃ ∧
        C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃


/-- A building is **strongly transitive** under the isometry group if for any two apartments
$A_1, A_2$ and chambers $C_1 \in A_1$, $C_2 \in A_2$ there is an isometry of $(V,B)$ sending
$A_1$ to $A_2$ and $C_1$ to $C_2$. -/
def StronglyTransitive (B : LinearMap.BilinForm k V) (n : ℕ)
    (bldg : IsBuilding B n) : Prop :=
  ∀ (A₁ A₂ : Apartment B n) (C₁ C₂ : Finset (Submodule k V)),
    A₁ ∈ bldg.apartments → A₂ ∈ bldg.apartments →
    C₁ ∈ A₁.simplices → C₂ ∈ A₂.simplices →
    ∃ g : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂) ∧
      (Finset.image (Submodule.map g.toLinearMap) C₁ = C₂) ∧
      (∀ σ ∈ A₁.simplices,
        Finset.image (Submodule.map g.toLinearMap) σ ∈ A₂.simplices)


/-- A **(B,N)-pair** in the isometry group of $(V,B)$: data of a Borel-type subgroup
stabilising a maximal isotropic flag, a frame-stabiliser playing the role of $N$, and a torus
$T = B \cap N$, satisfying the standard compatibility properties. -/
structure IsometryBNPair (B : LinearMap.BilinForm k V) (n : ℕ) where
  borel : Subgroup (V ≃ₗ[k] V)
  maxFlag : IsotropicFlag B
  borel_isometry : ∀ g ∈ borel, ∀ v₁ v₂ : V,
    B ((g : V ≃ₗ[k] V) v₁) ((g : V ≃ₗ[k] V) v₂) = B v₁ v₂
  borel_stabilizes : ∀ g ∈ borel, ∀ i,
    (maxFlag.chain i).map (g : V ≃ₗ[k] V).toLinearMap = maxFlag.chain i
  frameStab : Subgroup (V ≃ₗ[k] V)
  frame : HyperbolicFrame B n
  frameStab_isometry : ∀ g ∈ frameStab, ∀ v₁ v₂ : V,
    B ((g : V ≃ₗ[k] V) v₁) ((g : V ≃ₗ[k] V) v₂) = B v₁ v₂
  frameStab_permutes : ∀ g ∈ frameStab,
    ∀ i : Fin n, ∃ j : Fin n,
      (g : V ≃ₗ[k] V) (frame.pairs i).e = (frame.pairs j).e ∨
      (g : V ≃ₗ[k] V) (frame.pairs i).e = (frame.pairs j).e'
  frameStab_permutes_e' : ∀ g ∈ frameStab,
    ∀ i : Fin n, ∃ j : Fin n,
      (g : V ≃ₗ[k] V) (frame.pairs i).e' = (frame.pairs j).e ∨
      (g : V ≃ₗ[k] V) (frame.pairs i).e' = (frame.pairs j).e'
  torus : Subgroup (V ≃ₗ[k] V)
  torus_eq : (torus : Set (V ≃ₗ[k] V)) = (borel : Set (V ≃ₗ[k] V)) ∩ (frameStab : Set (V ≃ₗ[k] V))


/-- The Coxeter matrix $M$ is of type $C_n$: diagonal entries are $1$, consecutive simple
reflections satisfy $m_{i,i+1} = 3$ except the last pair which has $m_{n-2, n-1} = 4$, and all
non-adjacent pairs commute ($m_{ij} = 2$). -/
def TypeCn (n : ℕ) (M : CoxeterMatrix (Fin n)) : Prop :=


  (∀ i : Fin n, M i i = 1) ∧
  (∀ i j : Fin n, i ≠ j → (

    (i.val + 1 = j.val ∧ j.val < n - 1 → M i j = 3) ∧

    (i.val + 1 = j.val ∧ j.val = n - 1 ∧ 1 < n → M i j = 4) ∧

    (i.val + 1 < j.val ∨ j.val + 1 < i.val → M i j = 2)))

end IsometryBuilding
