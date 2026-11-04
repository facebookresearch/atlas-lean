/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectionTheory

/-- The abstract data of an AD-regular configuration space at every scale $\delta$:
each $\delta$ has a type of configurations whose "ratio" measures the incidence count;
configurations at scale $\delta_1 \delta_2$ can be coarsened to scale $\delta_1$ and
restricted to scale $\delta_2$, and the ratio factors (up to a sub-polynomial loss) as
$R(\delta_1\delta_2) \lessapprox (\delta_1\delta_2)^{-\varepsilon} R(\delta_1) R(\delta_2)$. -/
structure ADConfigSpace where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  ratio_factoring : ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ c : Config (δ₁ * δ₂),
        ratio (δ₁ * δ₂) c ≤ C * (δ₁ * δ₂)⁻¹ ^ ε *
          (ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
           ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c))

/-- The raw data of an AD-regular configuration space, equipped only with the
pointwise incidence decomposition $R(\delta_1\delta_2) \le R(\delta_1) R(\delta_2)$
(without the $\varepsilon$-loss factor). -/
structure ADConfigData where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  incidence_decomp : ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ c : Config (δ₁ * δ₂),
      ratio (δ₁ * δ₂) c ≤
        ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
        ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)








end ProjectionTheory
