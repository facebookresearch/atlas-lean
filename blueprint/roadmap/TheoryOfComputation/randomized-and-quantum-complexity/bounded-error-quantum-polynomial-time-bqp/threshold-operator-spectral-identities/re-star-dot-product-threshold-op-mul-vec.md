# The threshold quadratic form of a unit vector is bounded by the worst tail

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
$\lambda_j = (\lambda_{j_0}, \dots, \lambda_{j_{k-1}})$. Let $\Psi \in \mathbb{C}^{2^{km}}$ satisfy
$\sum_s |\Psi_s|^2 = 1$ and let $B$ be a real number with $\tau(\lambda_j, T) \le B$ for every $j$.
Then $\operatorname{Re}(\Psi^\dagger \, T_k(Q, T)\, \Psi) \le B$. This quadratic form is an acceptance probability only when $Q$ is an effect, $0 \le Q \le I$; for Hermitian $Q$ in general it need not lie in $[0, 1]$ (for one block, $Q = 2I$ and $T = 1$ it is $2$).
