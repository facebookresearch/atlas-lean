/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.ConvexAcyclicity
import Atlas.AlgebraicTopologyI.code.Section8

namespace AlgebraicTopologyI

noncomputable section

open scoped Topology

/-- The model space for the Eilenberg–Zilber construction in bidegree $(p,q)$: the
product $\Delta^p \times \Delta^q$ of two standard simplices, which serves as the
universal example used in acyclic models. -/
abbrev StdSimplexProd (p q : ℕ) : Type :=
  ↥(stdSimplex ℝ (Fin (p + 1))) × ↥(stdSimplex ℝ (Fin (q + 1)))

/-- A distinguished basepoint of the standard $n$-simplex (the vertex $e_0$),
used as a base for inclusions of one factor into a product. -/
def stdSimplexBasepoint (n : ℕ) : ↥(stdSimplex ℝ (Fin (n + 1))) :=
  ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩

/-- The universal (tautological) singular $n$-simplex: the identity map
$\Delta^n \to \Delta^n$. Every singular $n$-simplex $\sigma : \Delta^n \to X$ is the
pushforward of this universal one along $\sigma$. -/
def universalSimplex (n : ℕ) : SingularSimplex n (↥(stdSimplex ℝ (Fin (n + 1)))) :=
  ContinuousMap.id _

/-- The universal singular $n$-chain on $\Delta^n$: the generator of the free abelian
group corresponding to the universal simplex. -/
def universalChain (n : ℕ) : SingularChains n (↥(stdSimplex ℝ (Fin (n + 1)))) :=
  FreeAbelianGroup.of (universalSimplex n)

/-- Given a chain $c$ in the product of model simplices $\Delta^p \times \Delta^q$ and a
pair of singular simplices $\sigma : \Delta^p \to X$, $\tau : \Delta^q \to Y$, push the
model chain forward along $\sigma \times \tau$ to produce a chain in $X \times Y$.
This is the basic naturality of the cross product built from a model chain. -/
noncomputable def crossFromModelChain {p q : ℕ}
    {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (c : SingularChains (p + q) (StdSimplexProd p q))
    (σ : SingularSimplex p X) (τ : SingularSimplex q Y) :
    SingularChains (p + q) (X × Y) :=
  SingularChains.map (ContinuousMap.prodMap σ τ) c

/-- The Leibniz target used in the inductive construction of the universal cross product:
given chains realising the cross product in bidegrees $(p, q+1)$ and $(p+1, q)$, this
assembles the right-hand side of the Leibniz rule
$d(x \times y) = dx \times y + (-1)^p\, x \times dy$
in the next bidegree $(p+1, q+1)$. -/
noncomputable def leibnizTarget {p q : ℕ}
    (c_left : SingularChains (p + (q + 1)) (StdSimplexProd p (q + 1)))
    (c_right : SingularChains ((p + 1) + q) (StdSimplexProd (p + 1) q)) :
    SingularChains (p + q + 1) (StdSimplexProd (p + 1) (q + 1)) :=
  let dι_left := boundaryMap p (↥(stdSimplex ℝ (Fin (p + 2)))) (universalChain (p + 1))
  let ι_right := universalSimplex (q + 1)
  let term1 : SingularChains (p + (q + 1)) (StdSimplexProd (p + 1) (q + 1)) :=
    FreeAbelianGroup.lift (fun σ => crossFromModelChain c_left σ ι_right) dι_left
  let ι_left := universalSimplex (p + 1)
  let dι_right := boundaryMap q (↥(stdSimplex ℝ (Fin (q + 2)))) (universalChain (q + 1))
  let term2 : SingularChains ((p + 1) + q) (StdSimplexProd (p + 1) (q + 1)) :=
    FreeAbelianGroup.lift (fun τ => crossFromModelChain c_right ι_left τ) dι_right
  SingularChains.castIdx (by omega : p + (q + 1) = p + q + 1) term1 +
    (-1 : ℤ) ^ (p + 1) •
      SingularChains.castIdx (by omega : (p + 1) + q = p + q + 1) term2

open Classical in
/-- The universal cross product chain in bidegree $(p, q)$: a singular $(p+q)$-chain on
$\Delta^p \times \Delta^q$ recursively built so that it satisfies the Leibniz rule with
respect to the boundary. It serves as the model chain from which the Eilenberg–Zilber
map is obtained by naturality, via the acyclicity of products of standard simplices. -/
noncomputable def universalCross (p q : ℕ) :
    SingularChains (p + q) (StdSimplexProd p q) :=
  match p, q with
  | 0, q =>
    SingularChains.castIdx (by omega : q = 0 + q)
      (SingularChains.map (inclusionRight (stdSimplexBasepoint 0))
        (universalChain q))
  | p + 1, 0 =>
    SingularChains.castIdx (by omega : p + 1 = (p + 1) + 0)
      (SingularChains.map (inclusionLeft (stdSimplexBasepoint 0))
        (universalChain (p + 1)))
  | p + 1, q + 1 =>
    let target := leibnizTarget (universalCross p (q + 1)) (universalCross (p + 1) q)
    if hcycle : boundaryMap (p + q) (StdSimplexProd (p + 1) (q + 1)) target = 0 then
      SingularChains.castIdx (by omega : (p + q) + 2 = (p + 1) + (q + 1))
        (stdSimplex_prod_acyclic (p + 1) (q + 1) (p + q) target hcycle).choose
    else
      0
termination_by p + q

/-- A bidegree-graded family of model chains: a choice, for each pair $(p,q)$, of a
singular $(p+q)$-chain on the product $\Delta^p \times \Delta^q$. This packages the data
of a candidate Eilenberg–Zilber cross product at the level of model spaces. -/
structure ModelChainSystem where
  chains : (p q : ℕ) → SingularChains (p + q) (StdSimplexProd p q)

end

end AlgebraicTopologyI
