# The right rank increases exactly at a right-block position

For p, q : ℕ and an ordered (p, q)-shuffle s, let R be its set of right positions and r : Fin
(p + q + 1) → Fin (q + 1) its right rank map. For every edge k : Fin (p + q), r(k.succ).val =
r(k.castSucc).val + (if k ∈ R then 1 else 0).
