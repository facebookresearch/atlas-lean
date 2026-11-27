# Delta Ring

A `δ`-structure on a commutative ring `A` for the prime `p` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Definition 2.1): a map
`delta` with `delta 0 = delta 1 = 0`, the product rule
`delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y` and the sum rule
`delta (x + y) = delta x + delta y + (x ^ p + y ^ p - (x + y) ^ p) / p`, where the last quotient
is the polynomial `DeltaRing.addCorrection p x y`.

The prime `p` is a parameter rather than a hypothesis of the class; the results that need its
primality assume `Fact p.Prime`.
