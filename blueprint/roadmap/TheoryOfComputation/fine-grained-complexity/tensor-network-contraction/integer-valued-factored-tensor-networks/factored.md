# Integer-valued factored tensor network

An integer-valued factored tensor network.

Only `Θ a b` with `a < b` supplies labels. The factors `f a b` and `f b a` are the two
sides of the same interaction. Capacities `c` are metadata used by `totalCapacity`, `Shaped`,
and `Sized`; `value` does not read them.
