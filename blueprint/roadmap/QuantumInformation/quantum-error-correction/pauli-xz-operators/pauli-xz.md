# Pauli operator X^a Z^b

For bitstrings `a b : Fin n → ZMod 2`, `pauliXZ a b` is the complex matrix
of the Pauli operator `X^a Z^b` in the computational basis, whose basis
states are the bitstrings `x : Fin n → ZMod 2`: it sends the basis state `x`
to `(-1) ^ (b ⬝ᵥ x)` times the basis state `x + a`, where the dot product `b
⬝ᵥ x` is computed in `ZMod 2` and the exponent is its value `0` or `1`.
