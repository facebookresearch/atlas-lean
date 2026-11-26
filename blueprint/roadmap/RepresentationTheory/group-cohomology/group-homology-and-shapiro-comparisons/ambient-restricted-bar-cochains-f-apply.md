# Restricted bar morphism of an ambient cochain

Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `n : ℕ`, and `z : (Fin n →
G) → A`. Then `(ambientRestrictedBarCochains H A).f n (z) = (Rep.resFunctor H.subtype).map
(Rep.freeLift k G A z)`. This identifies the degree-`n` restricted bar morphism with the
restriction of the ambient equivariant linear extension.
