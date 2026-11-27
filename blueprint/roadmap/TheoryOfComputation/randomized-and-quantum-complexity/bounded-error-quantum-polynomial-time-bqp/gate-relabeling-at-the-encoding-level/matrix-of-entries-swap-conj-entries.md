# Decoding a swap-conjugated entry list

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. For a pair of bits
$p = (a, b)$ write $\bar p = (b, a)$. For every entry list $e$ with swap-conjugated entry list $e'$,
$M(e')(p, q) = M(e)(\bar p, \bar q)$ for all pairs of bits $p$ and $q$.
