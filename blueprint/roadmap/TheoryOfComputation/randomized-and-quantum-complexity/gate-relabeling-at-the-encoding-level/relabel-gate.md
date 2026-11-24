# Relabelling the qubits of a gate

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. For a map $\pi$ on qubit
positions and a gate $(i, j, e)$, the relabelled gate is $(\pi(i), \pi(j), e)$ when
$\pi(i) < \pi(j)$, and otherwise $(\pi(j), \pi(i), e')$, where $e'$ encodes $M(e)$ with its two
qubits exchanged.
