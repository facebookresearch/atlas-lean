/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Data.Nat.ModEq

set_option maxHeartbeats 400000

open Finset Nat

namespace ErdosKoRado

/-- (Theorem 1.2.9, Erdős–Ko–Rado) For $n \ge 2k$, an intersecting family of $k$-subsets
of $[n]$ has size at most $\binom{n-1}{k-1}$. -/
theorem erdos_ko_rado_theorem {n k : ℕ} (hn : 2 * k ≤ n)
    (F : Finset (Finset (Fin n)))
    (hF_int : (↑F : Set (Finset (Fin n))).Intersecting)
    (hF_sized : Set.Sized k (↑F : Set (Finset (Fin n)))) :
    F.card ≤ (n - 1).choose (k - 1) :=
  Finset.erdos_ko_rado hF_int hF_sized (by omega)

end ErdosKoRado
