/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card

namespace Certifiable

variable {n : ℕ} {Ω : Fin n → Type*}

/-- Definition 9.5.20 ($s$-certifiable). A set $A \subseteq \prod_i \Omega_i$ is
$s$-certifiable if every $x \in A$ admits an index set $I$ of size at most $s$ such that
any other point $y$ agreeing with $x$ on $I$ also lies in $A$. -/
def IsCertifiable (s : ℕ) (A : Set ((i : Fin n) → Ω i)) : Prop :=
  ∀ x ∈ A, ∃ I : Finset (Fin n), I.card ≤ s ∧
    ∀ y : (i : Fin n) → Ω i, (∀ i ∈ I, y i = x i) → y ∈ A

end Certifiable
