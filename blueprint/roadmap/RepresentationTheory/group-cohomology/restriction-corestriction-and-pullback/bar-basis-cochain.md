# Basis-valued inhomogeneous cochain

For a group `G`, a commutative ring `k`, and `n : ℕ`, `barBasisCochain n : (Fin n → G) →
(Rep.barComplex k G).X n` sends a tuple `g` to `Finsupp.single g (MonoidAlgebra.single 1 1)`.
It is an inhomogeneous degree-`n` cochain with values in the degree-`n` bar representation.
