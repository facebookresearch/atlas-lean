/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

open scoped Pointwise

namespace AdditiveCombinatorics

/-- **Plünnecke–Ruzsa inequality.** Let `Z` be an abelian group and `A, B ⊂ Z` finite
sets with $|A + B| \le K|A|$. Then for any natural numbers `m, n`,
$$|B^{\oplus m} - B^{\oplus n}| \le K^{m+n}\, |A|,$$
where $B^{\oplus k} = k \cdot B$ denotes the `k`-fold sumset of `B` with itself. -/
theorem plunnecke_inequality {Z : Type*} [DecidableEq Z] [AddCommGroup Z]
    {A B : Finset Z} (hA : A.Nonempty) {K : ℚ≥0}
    (hK : ((A + B).card : ℚ≥0) ≤ K * A.card) (m n : ℕ) :
    ((m • B - n • B).card : ℚ≥0) ≤ K ^ (m + n) * A.card := by
  have hAcard : (0 : ℚ≥0) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hle : ((A + B).card : ℚ≥0) / A.card ≤ K := by
    rwa [div_le_iff₀ hAcard]
  calc ((m • B - n • B).card : ℚ≥0)
      ≤ ((A + B).card / A.card) ^ (m + n) * A.card :=
        Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
    _ ≤ K ^ (m + n) * A.card := by gcongr

end AdditiveCombinatorics
