# Restricted comultiplication

Let `R` be a domain with fraction field `K`, `A` a commutative
Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an `R`-subalgebra of `A`
that is flat over `R` and whose comultiplication lands in the image of `S ⊗[R] S` in
`A ⊗[K] A`. This is the `R`-linear map `S → S ⊗[R] S` lifting the comultiplication of `A` along
`HopfOrder.tensorSqHom S`; by flatness `HopfOrder.tensorSqHom S` is injective, so the lift is
unique.
