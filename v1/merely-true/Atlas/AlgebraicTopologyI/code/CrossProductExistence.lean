/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.ModelChains

open Finset BigOperators

namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The singular chain cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)` as a bilinear map, defined on generators
by applying the universal model cross product to each pair of simplices and
extending freely. This is the underlying construction for Theorem 6.2. -/
noncomputable def crossProductMap (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y)) :=
  FreeAbelianGroup.lift (fun (σ : SingularSimplex p X) =>
    FreeAbelianGroup.lift (fun (τ : SingularSimplex q Y) =>
      crossFromModelChain (universalCross p q) σ τ))






open ContinuousMap unitInterval

/-- A chain homotopy between the singular-chain maps induced by two
continuous maps `f0, f1 : X → Y`: a sequence of homomorphisms
`hom n : S_n(X) → S_{n+1}(Y)` satisfying the chain-homotopy identity
`d ∘ hom + hom ∘ d = f1_* - f0_*`. This is the chain-level homotopy
witnessing Theorem 6.1 / Proposition 5.11. -/
structure SingularChainHomotopy {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f0 f1 : C(X, Y)) where
  hom : ∀ (n : ℕ), SingularChains n X →+ SingularChains (n + 1) Y
  chain_htpy : ∀ (n : ℕ) (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) Y (hom (n + 1) s) + hom n (boundaryMap n X s) =
      SingularChains.map f1 s - SingularChains.map f0 s

/-- The bottom inclusion `X → X × I` given by `x ↦ (x, 0)`. -/
noncomputable def inclusion0 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨0, unitInterval.zero_mem⟩)

/-- The top inclusion `X → X × I` given by `x ↦ (x, 1)`. -/
noncomputable def inclusion1 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨1, unitInterval.one_mem⟩)

/-- A natural chain homotopy between the singular-chain maps induced by the
two inclusions `inclusion0, inclusion1 : X → X × I`. The data consists of
homomorphisms `S_n(X) → S_{n+1}(X × I)` satisfying the chain-homotopy
identity and a naturality square in `X`. This is the universal ingredient
used to build chain homotopies from continuous homotopies in Theorem 6.1. -/
structure NaturalChainHomotopyInclusions where
  hom : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
    SingularChains n X →+ SingularChains (n + 1) (X × ↥I)
  chain_htpy : ∀ (X : Type) [TopologicalSpace X] (n : ℕ)
    (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) (X × ↥I) (hom X (n + 1) s) + hom X n (boundaryMap n X s) =
      SingularChains.map (inclusion1 X) s - SingularChains.map (inclusion0 X) s
  naturality : ∀ (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (n : ℕ) (s : SingularChains n X'),
    SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I)) (hom X' n s) =
      hom X n (SingularChains.map g s)

/-- Functoriality of the singular-chain map: the chain map induced by a
composition of continuous maps is the composition of the induced chain
maps. -/
lemma SingularChains.map_comp {n : ℕ} {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(X, Y)) (s : SingularChains n X) :
    SingularChains.map (f.comp g) s = SingularChains.map f (SingularChains.map g s) := by
  show (FreeAbelianGroup.map (SingularSimplex.map (f.comp g))) s =
    (FreeAbelianGroup.map (SingularSimplex.map f)) ((FreeAbelianGroup.map (SingularSimplex.map g)) s)
  rw [← FreeAbelianGroup.map_comp_apply]
  congr 1

/-- The singular boundary map commutes with the chain map induced by a
continuous map; equivalently, `SingularChains.map f` is a chain map. -/
lemma boundaryMap_map_comm {n : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : SingularChains (n + 1) X) :
    boundaryMap n Y (SingularChains.map f s) =
      SingularChains.map f (boundaryMap n X s) := by


  have h_eq : (boundaryMap n Y).comp (SingularChains.map f) =
      (SingularChains.map f).comp (boundaryMap n X) := by
    apply FreeAbelianGroup.lift_ext
    intro sigma

    show (boundaryMap n Y) (FreeAbelianGroup.of (SingularSimplex.map f sigma)) =
      (SingularChains.map f) ((boundaryMap n X) (FreeAbelianGroup.of sigma))

    unfold boundaryMap SingularChains.map SingularSimplex.map SingularSimplex.face
    erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, map_sum]
    congr 1
    ext i : 1
    erw [map_zsmul, FreeAbelianGroup.map_of_apply]
    simp only [ContinuousMap.comp_assoc]
    rfl
  exact DFunLike.congr_fun h_eq s

/-- The fundamental singular `1`-simplex `ι₁ : Δ¹ → I` given on barycentric
coordinates `(t₀, t₁)` by `(t₀, t₁) ↦ t₁`. -/
noncomputable def iotaSimplex : SingularSimplex 1 ↥I where
  toFun t := ⟨t.1 1, by
    obtain ⟨hnn, hsum⟩ := t.2
    constructor
    · exact hnn 1
    · have h0 := hnn 0
      have : t.1 0 + t.1 1 = 1 := by
        have := hsum
        simp [Fin.sum_univ_two] at this
        exact this
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val

/-- The `0`-th face of `iotaSimplex` is the constant simplex at `1`. -/
lemma iotaSimplex_face0 :
    SingularSimplex.face 0 iotaSimplex = constSimplex ⟨1, unitInterval.one_mem⟩ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  obtain ⟨_, hsum⟩ := t.2
  rw [Fin.sum_univ_one] at hsum
  simpa using hsum

/-- The `1`-st face of `iotaSimplex` is the constant simplex at `0`. -/
lemma iotaSimplex_face1 :
    SingularSimplex.face 1 iotaSimplex = constSimplex ⟨0, unitInterval.zero_mem⟩ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  simp

/-- The boundary of the fundamental `1`-simplex `ι₁` on `I` is
`c₁⁰ - c₀⁰`, the difference of the constant `0`-simplices at the endpoints. -/
lemma boundary_iota :
    boundaryMap 0 ↥I (FreeAbelianGroup.of iotaSimplex) =
      constChain ⟨1, unitInterval.one_mem⟩ - constChain ⟨0, unitInterval.zero_mem⟩ := by
  unfold boundaryMap
  erw [FreeAbelianGroup.lift_apply_of]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    iotaSimplex_face0, iotaSimplex_face1, constChain]
  abel

/-- The right-product-inclusion at the endpoint `1 ∈ I` agrees with
`inclusion1`. -/
lemma inclusionLeft_one_eq_inclusion1 (X : Type) [TopologicalSpace X] :
    inclusionLeft (Y := ↥I) ⟨1, unitInterval.one_mem⟩ = inclusion1 X := by
  apply ContinuousMap.ext; intro x; rfl

/-- The right-product-inclusion at the endpoint `0 ∈ I` agrees with
`inclusion0`. -/
lemma inclusionLeft_zero_eq_inclusion0 (X : Type) [TopologicalSpace X] :
    inclusionLeft (Y := ↥I) ⟨0, unitInterval.zero_mem⟩ = inclusion0 X := by
  apply ContinuousMap.ext; intro x; rfl



end

end AlgebraicTopologyI
