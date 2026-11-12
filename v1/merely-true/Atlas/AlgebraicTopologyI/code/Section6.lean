/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.Section5
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval

open Finset BigOperators

namespace AlgebraicTopologyI

/-- Inserting a zero in the `i`-th coordinate of a point of the standard `(n+1)`-simplex
yields a point of the standard `(n+2)`-simplex: this is the `i`-th face inclusion at the
level of barycentric coordinates. -/
lemma faceMap_mem_stdSimplex (n : ℕ) (i : Fin (n + 2))
    (t : Fin (n + 1) → ℝ) (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
    Fin.insertNth i (0 : ℝ) t ∈ stdSimplex ℝ (Fin (n + 2)) := by
  obtain ⟨hnn, hsum⟩ := ht
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · simp [h, Fin.insertNth_apply_same]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simp [Fin.insertNth_apply_succAbove, hnn]
  · rw [Fin.sum_univ_succAbove _ i]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hsum]

/-- The continuous `i`-th face inclusion `Δⁿ ↪ Δⁿ⁺¹` that sends the barycentric
coordinates `t` to the tuple with `0` inserted in position `i`. -/
noncomputable def faceInclusion (n : ℕ) (i : Fin (n + 2)) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin (n + 2)))) where
  toFun t := ⟨Fin.insertNth i 0 t.1, faceMap_mem_stdSimplex n i t.1 t.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.finInsertNth i continuous_const continuous_subtype_val

/-- The `i`-th face of a singular `(n+1)`-simplex `σ`, obtained by precomposing with the
`i`-th face inclusion of the standard simplex. -/
noncomputable def SingularSimplex.face {n : ℕ} {X : Type*} [TopologicalSpace X]
    (i : Fin (n + 2)) (σ : SingularSimplex (n + 1) X) : SingularSimplex n X :=
  σ.comp (faceInclusion n i)

/-- The singular boundary map `d : S_{n+1}(X) → S_n(X)` defined on generators by the
alternating sum `∑_i (-1)^i σ ∘ d^i` of face restrictions. -/
noncomputable def boundaryMap (n : ℕ) (X : Type*) [TopologicalSpace X] :
    SingularChains (n + 1) X →+ SingularChains n X :=
  FreeAbelianGroup.lift (fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i σ))

/-- Pushforward of a singular `n`-simplex along a continuous map `f : X → Y`, namely
`f ∘ σ`. -/
noncomputable def SingularSimplex.map {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (σ : SingularSimplex n X) : SingularSimplex n Y :=
  f.comp σ

/-- The induced map on singular chains `f_* : S_n(X) → S_n(Y)`, extending the
pushforward of simplices linearly. -/
noncomputable def SingularChains.map {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : SingularChains n X →+ SingularChains n Y :=
  FreeAbelianGroup.map (SingularSimplex.map f)

/-- The slice inclusion `j_x : Y → X × Y`, `y ↦ (x, y)`. -/
noncomputable def inclusionRight {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) : C(Y, X × Y) :=
  ContinuousMap.prodMk (ContinuousMap.const Y x) (ContinuousMap.id Y)

/-- The slice inclusion `i_y : X → X × Y`, `x ↦ (x, y)`. -/
noncomputable def inclusionLeft {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) : C(X, X × Y) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y)

/-- The constant `0`-simplex `c_x^0 : Δ^0 → X` at the point `x`. -/
noncomputable def constSimplex {X : Type*} [TopologicalSpace X] (x : X) :
    SingularSimplex 0 X :=
  ContinuousMap.const _ x

/-- The constant `0`-chain at `x`, namely the generator of `S_0(X)` corresponding to the
constant simplex `c_x^0`. -/
noncomputable def constChain {X : Type*} [TopologicalSpace X] (x : X) :
    SingularChains 0 X :=
  FreeAbelianGroup.of (constSimplex x)

/-- Trivial reindexing isomorphism `S_n(X) → S_m(X)` along an equality `n = m`. Used to
identify chains living in defeq-but-not-syntactically-equal degrees. -/
noncomputable def SingularChains.castIdx {n m : ℕ} (h : n = m) {X : Type*}
    [TopologicalSpace X] : SingularChains n X →+ SingularChains m X :=
  h ▸ AddMonoidHom.id _

/-- (Theorem 6.2) Bundle of data and axioms for the singular cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)`: it is natural in both arguments, bilinear,
satisfies the Leibniz rule `d(a × b) = (da) × b + (-1)^p a × db`, and is normalized so
that `c_x^0 × b = (j_x)_* b` and `a × c_y^0 = (i_y)_* a`. -/
structure CrossProduct where
  crossMap : ∀ (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y))
  naturality : ∀ (p q : ℕ) (X X' Y Y' : Type)
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y'))
    (a : SingularChains p X) (b : SingularChains q Y),
    (crossMap p q X' Y') (SingularChains.map f a) (SingularChains.map g b) =
      SingularChains.map (ContinuousMap.prodMap f g) ((crossMap p q X Y) a b)
  leibniz : ∀ (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularChains (p + 1) X) (b : SingularChains (q + 1) Y),
    let ab := (crossMap (p + 1) (q + 1) X Y) a b
    let ab' := SingularChains.castIdx (show (p + 1) + (q + 1) = (p + q + 1) + 1 by omega) ab
    let dab := boundaryMap (p + q + 1) (X × Y) ab'
    let da_b := SingularChains.castIdx (show p + (q + 1) = p + q + 1 by rfl)
                  ((crossMap p (q + 1) X Y) (boundaryMap p X a) b)
    let a_db := SingularChains.castIdx (show (p + 1) + q = p + q + 1 by omega)
                  ((crossMap (p + 1) q X Y) a (boundaryMap q Y b))
    dab = da_b + (-1 : ℤ) ^ (p + 1) • a_db
  normalization_left : ∀ (q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (b : SingularChains q Y),
    SingularChains.castIdx (show 0 + q = q by omega)
      ((crossMap 0 q X Y) (constChain x) b) =
      SingularChains.map (inclusionRight x) b
  normalization_right : ∀ (p : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (a : SingularChains p X),
    (crossMap p 0 X Y) a (constChain y) =
      SingularChains.map (inclusionLeft y) a

end AlgebraicTopologyI
