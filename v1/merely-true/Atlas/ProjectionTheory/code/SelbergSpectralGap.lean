/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Matrix BigOperators

namespace SelbergSpectralGap

/-- The group $\mathrm{SL}_2(\mathbb{F}_p)$ of $2 \times 2$ matrices with determinant $1$
over the finite field $\mathbb{Z}/p\mathbb{Z}$. -/
abbrev SL2p (p : ℕ) [Fact (Nat.Prime p)] := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

/-- The Selberg generating set $A_{\operatorname{sel}} \subset \mathrm{SL}_2(\mathbb{F}_p)$,
consisting of the four unipotent matrices
$\begin{pmatrix} 1 & \pm 1 \\ 0 & 1 \end{pmatrix}$ and $\begin{pmatrix} 1 & 0 \\ \pm 1 & 1 \end{pmatrix}$. -/
noncomputable def selbergGeneratingSet (p : ℕ) [Fact (Nat.Prime p)] : Finset (SL2p p) := by
  classical
  exact {⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
         ⟨!![1, -1; 0, 1], by simp [Matrix.det_fin_two]⟩,
         ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩,
         ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two]⟩}

/-- The averaging operator $T_A$ associated with a finite subset $A \subseteq G$ of a finite
group: $(T_A f)(x) = \frac{1}{|A|} \sum_{a \in A} f(x \cdot a)$. -/
noncomputable def averagingOperator {G : Type*} [Group G] [Fintype G]
    (A : Finset G) : (G → ℝ) → (G → ℝ) :=
  fun f x => (A.card : ℝ)⁻¹ * ∑ a ∈ A, f (x * a)

/-- The $\ell^2$ norm of a function $f : G \to \mathbb{R}$ on a finite group $G$,
defined as $\|f\|_{\ell^2} = \sqrt{\sum_{g \in G} f(g)^2}$. -/
noncomputable def l2Norm {G : Type*} [Fintype G] (f : G → ℝ) : ℝ :=
  Real.sqrt (∑ g : G, f g ^ 2)

/-- A function $f : G \to \mathbb{R}$ on a finite group has *mean zero* if
$\sum_{g \in G} f(g) = 0$, i.e. it is orthogonal to the constant function. -/
def HasMeanZero {G : Type*} [Fintype G] (f : G → ℝ) : Prop :=
  ∑ g : G, f g = 0

end SelbergSpectralGap

open SelbergSpectralGap

