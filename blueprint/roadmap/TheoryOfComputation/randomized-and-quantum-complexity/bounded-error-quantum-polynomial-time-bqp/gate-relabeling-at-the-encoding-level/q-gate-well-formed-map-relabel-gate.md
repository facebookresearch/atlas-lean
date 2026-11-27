# Relabelling keeps every gate of a list well-formed

Index the rows and columns of a $4 \times 4$ complex matrix by pairs of bits $(a, b)$, numbered
$2a + b$. A two-qubit gate is a triple $(i, j, e)$ of qubit positions $i, j$ and a list $e$ of
entries; $M(e)$ is the matrix whose entry at $(p, q)$ is the entry of $e$ at position
$4 \cdot \mathrm{idx}(p) + \mathrm{idx}(q)$, read as $0$ when the list is too short. The gate is
well-formed on $N$ qubits when $i < j < N$ and $M(e)^\dagger M(e) = I$. Relabel a gate $(i, j, e)$
by a map $\pi$ on qubit positions as $(\pi(i), \pi(j), e)$ when $\pi(i) < \pi(j)$, and otherwise as
$(\pi(j), \pi(i), e')$ with $e'$ encoding $M(e)$ with its qubits exchanged. If every gate of a list
is well-formed on $N$ qubits, $\pi$ is injective on $\{0, \dots, N - 1\}$ and maps it into
$\{0, \dots, N' - 1\}$, then every gate of the relabelled list is well-formed on $N'$ qubits.
