# Valid 2-local Hamiltonian term

A 2-local term acting on qubits $i$ and $j$ with entry
list $e$ is valid on $n$ qubits when $i < j < n$, the list $e$ has exactly $16$ entries, each
entry has nonzero denominators in the encodings of both its real and its imaginary part, the
$4 \times 4$ complex matrix $M$ encoded by $e$ is positive semidefinite, and
$\sum_{p, q} |M_{pq}|^2 \le 1$, that is, $M$ has Frobenius norm at most $1$.

In particular $M$ is Hermitian and has operator norm at most $1$.
