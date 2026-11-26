# Exchanging the qubits of an entry list preserves unitarity

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. If an entry list $e$
satisfies $M(e)^\dagger M(e) = I$, then its swap-conjugated entry list $e'$, which encodes $M(e)$
with its two qubits exchanged, also satisfies $M(e')^\dagger M(e') = I$.
