/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AdvancedKahler

set_option autoImplicit false

open DifferentialFormSpace


/-- A Kähler manifold with Hodge number data, additionally tracking the integral
$\int_M \omega^n$ of the top power of the Kähler form. -/
class HasKahlerHodgeNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasHodgeNumbers Ω VF inst where
  omega_n_integral : ℝ














/-- A cohomology theory equipped with the Hard Lefschetz pairing $Q(n,k)$ on $H^k$,
biadditive in both arguments and ℝ-linear in the left. -/
class HasHardLefschetzPairing
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomologyWithLefschetz Ω VF inst where
  Q : ∀ (_n k : ℕ), H k → H k → ℝ
  Q_add_left : ∀ (n k : ℕ) (α₁ α₂ β : H k),
    Q n k (@HAdd.hAdd _ _ _ (@instHAdd _ (H_addCommGroup k).toAddCommMonoid.toAdd) α₁ α₂) β =
    Q n k α₁ β + Q n k α₂ β
  Q_add_right : ∀ (n k : ℕ) (α β₁ β₂ : H k),
    Q n k α (@HAdd.hAdd _ _ _ (@instHAdd _ (H_addCommGroup k).toAddCommMonoid.toAdd) β₁ β₂) =
    Q n k α β₁ + Q n k α β₂
  Q_smul_left : ∀ (n k : ℕ) (r : ℝ) (α β : H k),
    Q n k (@HSMul.hSMul ℝ _ _ (@instHSMul _ _ (H_module k).toSMul) r α) β =
    r * Q n k α β


/-- The Lefschetz decomposition of cohomology: every class $\alpha \in H^k$ decomposes as
$\alpha = \sum_r L^r \alpha_{k-2r}^{\text{prim}}$, where the primitive components are
characterized by $L^{n-(k-2r)+1} \alpha_{k-2r}^{\text{prim}} = 0$. -/
class HasLefschetzDecomposition
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomologyWithLefschetz Ω VF inst where
  prim_component : ∀ (_n k r : ℕ),
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ) (H k) (H (k - 2 * r))
      (H_addCommGroup k).toAddCommMonoid (H_addCommGroup (k - 2 * r)).toAddCommMonoid
      (H_module k) (H_module (k - 2 * r))
  prim_component_is_primitive : ∀ (n k r : ℕ) (_hkn : k ≤ n) (_hr : 2 * r ≤ k)
    (α : H k),
    L_map (k - 2 * r) (n - (k - 2 * r) + 1) (prim_component n k r α) =
      @OfNat.ofNat _ 0 (@Zero.toOfNat0 _
        (H_addCommGroup ((k - 2 * r) + 2 * (n - (k - 2 * r) + 1))).toZero)
  reconstruct : ∀ (_n k : ℕ), H k → H k
  reconstruct_eq : ∀ (n k : ℕ) (_hkn : k ≤ n) (α : H k),
    reconstruct n k α = α
  prim_component_injective : ∀ (n k : ℕ) (_hkn : k ≤ n) (α : H k),
    (∀ r, 2 * r ≤ k → prim_component n k r α =
      @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (H_addCommGroup (k - 2 * r)).toZero)) →
    α = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (H_addCommGroup k).toZero)
