# Encoded 2-local Hamiltonian term

A 2-local Hamiltonian term is encoded as a triple
$(i, j, e)$ of natural numbers $i$ and $j$, the qubits it acts on, and a list $e$ of pairs of
encoded rational numbers, the real and imaginary parts of the entries of its $4 \times 4$ matrix
in row-major order.

The encoding itself does not require $e$ to have $16$ entries or the matrix to be Hermitian; the
qubit bounds, the number of entries and positive semidefiniteness (hence Hermiticity) are part of
the validity of a term.
