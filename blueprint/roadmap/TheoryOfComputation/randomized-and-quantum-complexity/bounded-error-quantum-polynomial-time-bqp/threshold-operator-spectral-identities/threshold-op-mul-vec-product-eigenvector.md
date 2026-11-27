# The threshold operator is diagonal in the product eigenbasis

View a vector $\Psi$ indexed by $\{0, \dots, 2^{km} - 1\}$ as a state of $k$ blocks of $m$ qubits,
block $0$ in the lowest $m$ binary digits. For a $2^m \times 2^m$ complex matrix $Q$ and a real
threshold $T$, the threshold operator is $T_k(Q, T) = \sum_b \bigotimes_{i < k} Q_{b_i}$, summed
over the Boolean strings $b$ of length $k$ with at least $T$ true entries, where
$Q_{\mathrm{true}} = Q$ and $Q_{\mathrm{false}} = 1 - Q$. For real numbers $\mu_0, \dots, \mu_{k-1}$
and $T$, the upper-tail weight is
$\tau(\mu, T) = \sum_b \prod_{i < k} (\mu_i \text{ if } b_i \text{ else } 1 - \mu_i)$, summed over
the Boolean strings $b$ of length $k$ with at least $T$ true entries. Let $Q$ be Hermitian with
eigenvalues $\lambda_0, \dots, \lambda_{2^m - 1}$ and an orthonormal basis of eigenvectors
$v_0, \dots, v_{2^m - 1}$. For $j = (j_0, \dots, j_{k-1})$ write
$v_j = v_{j_0} \otimes \cdots \otimes v_{j_{k-1}}$ for the product eigenvector and
$\lambda_j = (\lambda_{j_0}, \dots, \lambda_{j_{k-1}})$. Then
$T_k(Q, T)\, v_j = \tau(\lambda_j, T)\, v_j$ for every $j$.
