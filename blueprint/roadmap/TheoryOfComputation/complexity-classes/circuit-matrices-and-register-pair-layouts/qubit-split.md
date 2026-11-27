# Qubit layout of a register pair

The pair `(p, q)` of a `v`-qubit register and an
`m`-qubit register is the index `p + 2 ^ v * q` of `v + m` qubits: the first register sits on
the low-order `v` qubits, as in `tensorProd`.
