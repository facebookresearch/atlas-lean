/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.HamiltonianVectorFields

set_option autoImplicit false

open DifferentialFormSpace


/-- A Hamiltonian diffeomorphism of $(M, \omega)$: data of a Hamiltonian $H$, its Hamiltonian
vector field $X_H$, and the time-1 flow of $X_H$. -/
structure HamiltonianDiffeomorphism
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  H : Ω 0
  hv : HamiltonianVectorField S H
  flow : HamiltonianFlow S H hv

/-- The time-1 map $\varphi^1_{X_H}: M \to M$ of the Hamiltonian flow. -/
noncomputable def HamiltonianDiffeomorphism.φ
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (f : HamiltonianDiffeomorphism S) : DFSMorphism Ω VF Ω VF :=
  f.flow.ρ_t 1

/-- A Hamiltonian diffeomorphism is symplectic: $\varphi^* \omega = \omega$. -/
theorem HamiltonianDiffeomorphism.preserves_symplectic
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (f : HamiltonianDiffeomorphism S) :
    f.φ.pullback S.ω = S.ω :=
  hamiltonian_flow_preserves_symplectic_form S f.H f.hv f.flow 1


/-- The fixed-point set $\mathrm{Fix}(\varphi)$ of a Hamiltonian diffeomorphism, exposed as a
finite indexing type with evaluation $\mathrm{ev}_x(g) = g(x)$ satisfying $\mathrm{ev}_x(\varphi^* g)
= \mathrm{ev}_x(g)$. -/
class HasFixedPoints
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S) where
  FixedPoint : Type
  [fintype : Fintype FixedPoint]
  eval : FixedPoint → Ω 0 → ℝ
  eval_pullback_eq : ∀ (x : FixedPoint) (g : Ω 0),
    eval x (f.φ.pullback g) = eval x g

/-- Nondegeneracy of fixed points: the evaluation map on $\mathrm{Fix}(\varphi)$ is injective,
i.e. distinct fixed points are separated by smooth functions. -/
class IsNondegenerate
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    extends HasFixedPoints S f where
  eval_injective : Function.Injective eval


/-- A graded cohomology theory $H^k(M, \mathbb{R})$ taking finite-dimensional real values. -/
class HasCohomology
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  H : ℕ → Type*
  H_addCommGroup : ∀ k, AddCommGroup (H k)
  H_module : ∀ k, Module ℝ (H k)
  H_finiteDimensional : ∀ k, FiniteDimensional ℝ (H k)

/-- The $i$-th Betti number $b_i(M) = \dim_\mathbb{R} H^i(M, \mathbb{R})$. -/
noncomputable def HasCohomology.betti
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (hC : @HasCohomology Ω VF inst) (i : ℕ) : ℕ :=
  @Module.finrank ℝ (hC.H i) _ (hC.H_addCommGroup i).toAddCommMonoid (hC.H_module i)

/-- Betti-number data for a manifold of dimension `manifoldDim`: total Betti number
$\sum_{i=0}^{\dim M} b_i(M)$ packaged with the cohomology groups. -/
class HasBettiNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomology Ω VF inst where
  manifoldDim : ℕ
  totalBetti : ℕ
  totalBetti_eq : totalBetti = (Finset.range (manifoldDim + 1)).sum
    (fun i => @Module.finrank ℝ (H i) _ (H_addCommGroup i).toAddCommMonoid (H_module i))


/-- The $i$-th Betti number $b_i(M) = \dim_\mathbb{R} H^i(M, \mathbb{R})$ recovered from the
Betti-number data. -/
noncomputable def HasBettiNumbers.betti
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (hB : @HasBettiNumbers Ω VF inst) (i : ℕ) : ℕ :=
  @Module.finrank ℝ (hB.H i) _ (hB.H_addCommGroup i).toAddCommMonoid (hB.H_module i)


/-- The symplectic action functional $\mathcal{A}_H: \mathcal{L}M \to \mathbb{R}$ on a loop space,
whose critical points correspond to 1-periodic orbits of the Hamiltonian flow (and hence to fixed
points of $\varphi$). -/
structure ActionFunctional
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S) where
  LoopSpace : Type
  action : LoopSpace → ℝ
  CriticalPoint : Type
  critToLoop : CriticalPoint → LoopSpace
  critEval : CriticalPoint → Ω 0 → ℝ
  crit_is_periodic : ∀ (c : CriticalPoint) (g : Ω 0),
    critEval c (f.φ.pullback g) = critEval c g
  critEval_injective : Function.Injective critEval

/-- Bijection between critical points of the action functional and fixed points of $\varphi$:
$\mathrm{Crit}(\mathcal{A}_H) \cong \mathrm{Fix}(\varphi)$. -/
structure ActionFunctionalWithBijection
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    [hnd : IsNondegenerate S f]
    extends ActionFunctional S f where
  critToFix : CriticalPoint → hnd.FixedPoint
  critToFix_eval : ∀ (c : CriticalPoint) (g : Ω 0),
    hnd.eval (critToFix c) g = critEval c g
  fixToCrit : hnd.FixedPoint → CriticalPoint
  fixToCrit_eval : ∀ (x : hnd.FixedPoint) (g : Ω 0),
    critEval (fixToCrit x) g = hnd.eval x g


/-- The Floer chain complex $(CF_*, \partial)$ generated by 1-periodic orbits, with differential
$\partial^2 = 0$ and total rank equal to $\#\mathrm{Fix}(\varphi)$. -/
structure FloerComplex
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    [hnd : IsNondegenerate S f] where
  CF : ℤ → Type
  [instAddCommGroup : ∀ i, AddCommGroup (CF i)]
  differential : ∀ i, CF i →+ CF (i + 1)
  d_squared : ∀ (i : ℤ) (x : CF i),
    differential (i + 1) (differential i x) = 0
  totalRank : ℕ
  totalRank_eq_card : totalRank = @Fintype.card _ hnd.fintype

/-- The graded and total ranks $\dim HF^i$ and $\sum_i \dim HF^i$ of Floer homology. -/
class HasFloerHomologyRank
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    [hnd : IsNondegenerate S f] where
  floerRank : ℕ → ℕ
  totalFloerRank : ℕ



/-- Graded ranks of the Floer complex: $\dim CF^i$, summing to the total rank and vanishing
above the manifold dimension. -/
structure FloerComplexGradedRank
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    {f : HamiltonianDiffeomorphism S}
    [hnd : IsNondegenerate S f]
    [hbetti : @HasBettiNumbers Ω VF inst]
    (FC : FloerComplex S f) where
  rankCF : ℕ → ℕ
  rankCF_sum : (Finset.range (hbetti.manifoldDim + 1)).sum rankCF = FC.totalRank
  rankCF_vanish : ∀ i, hbetti.manifoldDim < i → rankCF i = 0


/-- A compact Lagrangian submanifold $L \hookrightarrow (M, \omega)$: the pullback of $\omega$ to
$L$ vanishes, $\iota^* \omega = 0$. -/
structure CompactLagrangian
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M) where
  Ω_L : ℕ → Type*
  VF_L : Type*
  [inst_L : DifferentialFormSpace Ω_L VF_L]
  inclusion : DFSMorphism Ω_L VF_L Ω_M VF_M
  lagrangian : inclusion.pullback S.ω = 0

attribute [instance] CompactLagrangian.inst_L

/-- Data for the Lagrangian Arnold conjecture: cohomology of $L$, dimension, total Betti number
$\sum_i b_i(L) \ge 2$, and the intersection number $\# (L \cap \psi(L))$. -/
class HasLagrangianIntersectionData
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S)
    (ψ : HamiltonianDiffeomorphism S) where
  numIntersections : ℕ
  H_L : ℕ → Type*
  H_L_addCommGroup : ∀ k, AddCommGroup (H_L k)
  H_L_module : ∀ k, Module ℝ (H_L k)
  H_L_finiteDimensional : ∀ k, FiniteDimensional ℝ (H_L k)
  lagrangianDim : ℕ
  totalBettiL : ℕ
  totalBettiL_eq : totalBettiL = (Finset.range (lagrangianDim + 1)).sum
    (fun i => @Module.finrank ℝ (H_L i) _ (H_L_addCommGroup i).toAddCommMonoid (H_L_module i))
  betti_ge_two : totalBettiL ≥ 2


/-- Transverse intersection of $L$ and $\psi(L)$: the intersection points are non-degenerate, in
the sense that a 1-form vanishing on both tangent spaces vanishes identically. -/
class IsTransverseIntersection
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S)
    (ψ : HamiltonianDiffeomorphism S) : Prop where
  jointly_spanning : ∀ (α : Ω_M 1),
    L.inclusion.pullback α = (0 : L.Ω_L 1) →
    L.inclusion.pullback (ψ.φ.pullback α) = (0 : L.Ω_L 1) →
    α = 0

/-- Relative spin condition on $L \subset M$: existence of a closed 2-form $\beta$ on $M$ whose
pullback to $L$ is exact, used to orient moduli spaces in Lagrangian Floer theory. -/
class IsRelativelySpin
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S) : Prop where
  spin_lift : ∃ (β : Ω_M 2),
    inst_M.d β = 0 ∧
    ∃ (γ : L.Ω_L 1), L.inclusion.pullback β = L.inst_L.d γ

/-- $H^1$-injectivity hypothesis: every closed 1-form on $L$ lifts to a closed 1-form on $M$ up
to an exact form, ensuring the inclusion $H^1(M) \to H^1(L)$ is surjective on representatives. -/
class HasH1Injectivity
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S) : Prop where
  h1_surjective : ∀ (α : L.Ω_L 1),
    L.inst_L.d α = 0 →
    ∃ (β : Ω_M 1), inst_M.d β = 0 ∧
      ∃ (γ : L.Ω_L 0), L.inclusion.pullback β = α + L.inst_L.d γ
