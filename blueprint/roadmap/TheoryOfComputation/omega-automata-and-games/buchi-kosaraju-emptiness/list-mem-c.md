# List Mem C

Assume that equality on `V` is decidable.

Costed list-membership test: the same `Bool` as `decide (t ∈ l)`, plus
the number of entries examined. It stops at the first matching entry
(short-circuit), so the cost is the index of the first match plus one,
or the full length when `t` is absent.
