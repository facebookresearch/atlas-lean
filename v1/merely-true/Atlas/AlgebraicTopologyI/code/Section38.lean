/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section17
import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section34
import Atlas.AlgebraicTopologyI.code.Section37
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear

noncomputable section

open Metric Set

namespace BorsukUlam

/-- The unit sphere in `EuclideanSpace ℝ (Fin (n+1))` is connected whenever `n ≥ 1`,
i.e. for spheres of dimension at least one. -/
lemma sphere_isConnected (n : ℕ) (hn : 1 ≤ n) :
    IsConnected (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  isConnected_sphere (by
    apply Module.lt_rank_of_lt_finrank
    rw [finrank_euclideanSpace_fin]
    omega) 0 (by norm_num)

/-- The `k`-th singular cohomology of real projective `n`-space `ℝPⁿ` with coefficients in
`𝔽₂ = ZMod 2`, packaged as a plain `Type`. Used to set up the Borsuk–Ulam proof via the
mod-2 cohomology ring of `ℝPⁿ`. -/
def F2CohomRPn (n k : ℕ) : Type :=
  (SingularCohomology.singularCohomology (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n))
    (ModuleCat.of (ZMod 2) (ZMod 2)) k : Type)

/-- The additive commutative group structure on `F2CohomRPn n k` inherited from its
`ModuleCat` representation. -/
@[reducible] def F2CohomRPn.instAddCommGroup (n k : ℕ) : AddCommGroup (F2CohomRPn n k) :=
  ModuleCat.isAddCommGroup
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)
attribute [instance] F2CohomRPn.instAddCommGroup


/-- The `ZMod 2`-module structure on `F2CohomRPn n k`, inherited from the underlying
`ModuleCat` object. -/
noncomputable instance F2CohomRPn.instModule (n k : ℕ) : Module (ZMod 2) (F2CohomRPn n k) :=
  ModuleCat.isModule
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)

/-- Every module over the field `ZMod 2` is free, so in particular
`H^k(ℝPⁿ; 𝔽₂)` is a free `𝔽₂`-module for `1 ≤ n` and `k ≤ n`. -/
theorem F2CohomRPn.instFree (n k : ℕ) (_hn : n ≥ 1) (_hk : k ≤ n) :
    Module.Free (ZMod 2) (F2CohomRPn n k) :=
  Module.Free.of_divisionRing (ZMod 2) (F2CohomRPn n k)














/-- Functoriality of mod-2 cohomology: a continuous map `f : ℝPⁿ¹ → ℝPⁿ²` induces an
additive pullback `f* : H^k(ℝPⁿ²; 𝔽₂) → H^k(ℝPⁿ¹; 𝔽₂)`. -/
noncomputable def F2CohomRPn.cohomologyPullback
    {n₁ n₂ : ℕ}
    (f : C(RealProjectiveSpace.RPn n₁, RealProjectiveSpace.RPn n₂))
    (k : ℕ) : F2CohomRPn n₂ k →+ F2CohomRPn n₁ k :=
  (SingularCohomology.singularCohomologyMap (ZMod 2)
    (TopCat.ofHom f) k).hom.toAddMonoidHom

/-- An antipodal-preserving continuous map `g : Sᵐ → Sᵐ⁻¹` descends to the quotient by the
antipodal action to yield a continuous map `ℝPᵐ → ℝPᵐ⁻¹`. Defined for `m ≥ 2`. -/
noncomputable def F2CohomRPn.descendedMap : (m : ℕ) → (hm : m ≥ 2) →
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) →
    (hg : ∀ x, g (-x) = -g x) →
    C(RealProjectiveSpace.RPn m, RealProjectiveSpace.RPn (m - 1))
  | n + 2, _, g, hg =>
    ⟨Quotient.lift
      (fun x : RealProjectiveSpace.Sphere (n + 2) =>
        @Quotient.mk' (RealProjectiveSpace.Sphere (n + 1))
          (RealProjectiveSpace.antipodalSetoid (n + 1)) (g x))
      (fun a b hab => by
        rcases hab with hab | hab
        · congr 1; exact Subtype.ext hab
        · apply Quotient.sound
          show (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = ↑(g b) ∨
               (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = -↑(g b)
          right
          have heq : a = -b := Subtype.ext hab
          have := hg b; rw [← heq] at this
          exact congrArg Subtype.val this),
      (continuous_quotient_mk' (s := RealProjectiveSpace.antipodalSetoid (n + 1))).comp
        g.continuous |>.quotient_lift _⟩
  | 0, hm, _, _ => absurd hm (by omega)
  | 1, hm, _, _ => absurd hm (by omega)

/-- The cohomology pullback `H^k(ℝPᵐ⁻¹; 𝔽₂) → H^k(ℝPᵐ; 𝔽₂)` induced by an odd map
`g : Sᵐ → Sᵐ⁻¹` via its descent `ℝPᵐ → ℝPᵐ⁻¹`. -/
noncomputable def F2CohomRPn.pullback (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (k : ℕ) : F2CohomRPn (m - 1) k →+ F2CohomRPn m k :=
  F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) k


















end BorsukUlam

open Manifold CategoryTheory

namespace PoincareDuality

variable (R : Type) [CommRing R]






/-- Reduced singular homology `\widetilde H_q(X; R)`: in degree zero it is the kernel of
the augmentation `H_0(X; R) → R`, and in higher degrees it agrees with the usual
singular homology. -/
def ReducedSingularHomology
    (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (q : ℕ) : Type :=
  match q with
  | 0 => ↥(LinearMap.ker (augmentationH0 R (TopCat.of X)).hom)
  | n + 1 => (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1) : Type)


/-- The additive commutative group structure on reduced singular homology, inherited
from the augmentation kernel (degree 0) or from singular homology (higher degrees). -/
instance ReducedSingularHomology.instAddCommGroup
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    AddCommGroup (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.addCommGroup _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isAddCommGroup

/-- The `R`-module structure on reduced singular homology. -/
instance ReducedSingularHomology.instModule
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    Module R (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.module _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isModule

/-- Convenient abbreviation for the unit sphere `Sⁿ ⊂ ℝⁿ⁺¹` viewed as a subtype. -/
abbrev SphereType (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)























/-- Perfect pairings are preserved under post-composition on the right by a linear
equivalence: if `p : M × N → R` is a perfect pairing and `e : N' ≃ N`, then
`p.compl₂ e` is also a perfect pairing. -/
theorem isPerfPair_compl₂ {R M N N' : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R N] [Module R N']
    (p : M →ₗ[R] N →ₗ[R] R) (e : N' ≃ₗ[R] N)
    [hp : p.IsPerfPair] : (p.compl₂ e.toLinearMap).IsPerfPair where
  bijective_left := by
    have hbij : Function.Bijective p := hp.bijective_left
    have heq : ⇑(p.compl₂ e.toLinearMap) = (fun f : N →ₗ[R] R => f.comp e.toLinearMap) ∘ p := by
      ext m n'; simp [LinearMap.compl₂_apply]
    rw [heq]
    apply Function.Bijective.comp
    · constructor
      · intro f g h
        ext n
        have := LinearMap.ext_iff.mp h (e.symm n)
        simp at this
        exact this
      · intro f
        exact ⟨f.comp e.symm.toLinearMap, by ext n'; simp⟩
    · exact hbij
  bijective_right := by
    have hbij : Function.Bijective p.flip := hp.bijective_right
    have heq : ⇑((p.compl₂ e.toLinearMap).flip) = p.flip ∘ e := by
      ext n' m; simp [LinearMap.flip_apply, LinearMap.compl₂_apply]
    rw [heq]
    exact hbij.comp e.bijective






















end PoincareDuality

namespace AlexanderDuality

open PoincareDuality





end AlexanderDuality

open CategoryTheory AlgebraicTopology Limits TopCat

namespace AlgebraicTopologyI

/-- A knot is a topological embedding `S¹ ↪ S³`. -/
def IsKnot (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : Prop :=
  Topology.IsEmbedding f

/-- The complement `S³ \ f(S¹)` of a knot `f : S¹ ↪ S³`, packaged as a topological
space. -/
def knotComplement (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : TopCat.{0} :=
  TopCat.of { x : (𝕊 3 : TopCat.{0}) | x ∉ Set.range f }

/-- A space `X` is a homology circle if its singular homology agrees with that of the
circle `S¹` in every degree and over every commutative ring `R`. -/
def IsHomologyCircle (X : TopCat.{0}) : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    Nonempty (SingularCohomology.singularHomologyModule R X n ≅
              SingularCohomology.singularHomologyModule R (𝕊 1 : TopCat.{0}) n)



end AlgebraicTopologyI

end
