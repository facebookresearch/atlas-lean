# The left rank increases exactly at a left-block position

For p, q : ℕ and an ordered (p, q)-shuffle s, let L be its set of left positions and ℓ : Fin
(p + q + 1) → Fin (p + 1) its left rank map. For every edge k : Fin (p + q), ℓ(k.succ).val =
ℓ(k.castSucc).val + (if k ∈ L then 1 else 0).
