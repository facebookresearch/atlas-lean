/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.TangentSpaces

noncomputable section

open Matrix MvPolynomial

namespace SingularPoints

variable {k : Type*} [Field k]

/-- A point $P$ on the algebraic set $V(f_1, \dots, f_m)$ of expected dimension $d$ is nonsingular if the Jacobian matrix at $P$ has rank $n - d$. -/
def IsNonsingularPoint (k : Type*) [Field k] (n m d : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : AffineSpace_k k n) : Prop :=
  P ∈ AlgebraicSet k n (Set.range f) ∧
    (TangentSpaces.jacobianMatrix n m f P).rank = n - d

/-- A singular point on $V(f_1, \dots, f_m)$ is one where the Jacobian fails to achieve the expected rank $n - d$. -/
def IsSingularPoint (k : Type*) [Field k] (n m d : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : AffineSpace_k k n) : Prop :=
  P ∈ AlgebraicSet k n (Set.range f) ∧
    (TangentSpaces.jacobianMatrix n m f P).rank ≠ n - d

/-- A variety is smooth (of dimension $d$) if every point of $V(f_1, \dots, f_m)$ is nonsingular, i.e. the Jacobian has rank $n - d$ everywhere. -/
def IsSmoothVariety (k : Type*) [Field k] (n m d : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) : Prop :=
  ∀ P : AffineSpace_k k n,
    P ∈ AlgebraicSet k n (Set.range f) →
      (TangentSpaces.jacobianMatrix n m f P).rank = n - d

/-- Intrinsic nonsingularity: a point $P \in V$ is nonsingular relative to chosen generators $f_i$ of the ideal of $V$ when the Jacobian has rank $n - d$. -/
def IsNonsingularPointIntrinsic (k : Type*) [Field k] (n m d : ℕ)
    (V : Set (AffineSpace_k k n))
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (_hVar : IsAffineVariety k n V)
    (_hgen : Ideal.span (Set.range f) = idealOfAlgebraicSet V)
    (_hdim : HasDimension k n V d)
    (P : AffineSpace_k k n) : Prop :=
  P ∈ V ∧ (TangentSpaces.jacobianMatrix n m f P).rank = n - d

/-- Intrinsic singularity: a point $P \in V$ is singular when the Jacobian of a chosen generating set of $I(V)$ has rank different from $n - d$. -/
def IsSingularPointIntrinsic (k : Type*) [Field k] (n m d : ℕ)
    (V : Set (AffineSpace_k k n))
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (_hVar : IsAffineVariety k n V)
    (_hgen : Ideal.span (Set.range f) = idealOfAlgebraicSet V)
    (_hdim : HasDimension k n V d)
    (P : AffineSpace_k k n) : Prop :=
  P ∈ V ∧ (TangentSpaces.jacobianMatrix n m f P).rank ≠ n - d

/-- An intrinsic notion of smoothness: every point of $V$ is nonsingular with respect to a chosen generating set of the ideal $I(V)$. -/
def IsSmoothVarietyIntrinsic (k : Type*) [Field k] (n m d : ℕ)
    (V : Set (AffineSpace_k k n))
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (_hVar : IsAffineVariety k n V)
    (_hgen : Ideal.span (Set.range f) = idealOfAlgebraicSet V)
    (_hdim : HasDimension k n V d) : Prop :=
  ∀ P : AffineSpace_k k n, P ∈ V →
    (TangentSpaces.jacobianMatrix n m f P).rank = n - d


end SingularPoints
