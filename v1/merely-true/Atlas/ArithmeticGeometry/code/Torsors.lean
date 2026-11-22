/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.AddTorsor.Defs

/-- A `G`-torsor (principal homogeneous space) is a type `T` equipped with a free and transitive
action of the additive commutative group `G`. This is packaged as a `Mixin`-style class over
`AddTorsor G T`. -/
class IsTorsor (G : Type*) (T : Type*) [AddCommGroup G] extends AddTorsor G T


/-- Every additive commutative group `G` is a torsor over itself, with action given by addition. -/
instance IsTorsor.self (G : Type*) [AddCommGroup G] : IsTorsor G G := ⟨⟩


/-- Choosing a base point $t_0 \in T$ of a $G$-torsor $T$ yields an equivalence $G \simeq T$
sending $g \mapsto g +_v t_0$. -/
noncomputable def IsTorsor.equivOfBasePoint {G : Type*} {T : Type*} [AddCommGroup G]
    [IsTorsor G T] (t₀ : T) : G ≃ T :=
  Equiv.vaddConst t₀
