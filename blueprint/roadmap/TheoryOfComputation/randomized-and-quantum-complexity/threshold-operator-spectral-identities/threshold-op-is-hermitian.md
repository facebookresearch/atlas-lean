# The threshold operator of a Hermitian matrix is Hermitian

View a vector $\Psi$ indexed by $\{0, \dots, 2^{km} - 1\}$ as a state of $k$ blocks of $m$ qubits,
block $0$ in the lowest $m$ binary digits. For a $2^m \times 2^m$ complex matrix $Q$ and a real
threshold $T$, the threshold operator is $T_k(Q, T) = \sum_b \bigotimes_{i < k} Q_{b_i}$, summed
over the Boolean strings $b$ of length $k$ with at least $T$ true entries, where
$Q_{\mathrm{true}} = Q$ and $Q_{\mathrm{false}} = 1 - Q$. If $Q$ is Hermitian, then $T_k(Q, T)$ is
Hermitian for every threshold $T$.
