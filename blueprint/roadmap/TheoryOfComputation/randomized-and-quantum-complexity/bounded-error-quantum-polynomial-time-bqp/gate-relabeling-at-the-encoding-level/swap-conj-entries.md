# Entry list of a matrix with its two qubits exchanged

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. For a pair of bits
$p = (a, b)$ write $\bar p = (b, a)$. For an entry list $e$, the swap-conjugated entry list is the
entry list of the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(\bar p) + \mathrm{idx}(\bar q)$ (zero when the list is too short): the matrix
$M(e)$ with its two qubits exchanged.
