# The threshold quadratic form of a product of identical unit vectors

View a vector $\Psi$ indexed by $\{0, \dots, 2^{km} - 1\}$ as a state of $k$ blocks of $m$ qubits,
block $0$ in the lowest $m$ binary digits. For a $2^m \times 2^m$ complex matrix $Q$ and a real
threshold $T$, the threshold operator is $T_k(Q, T) = \sum_b \bigotimes_{i < k} Q_{b_i}$, summed
over the Boolean strings $b$ of length $k$ with at least $T$ true entries, where
$Q_{\mathrm{true}} = Q$ and $Q_{\mathrm{false}} = 1 - Q$. For real numbers $\mu_0, \dots, \mu_{k-1}$
and $T$, the upper-tail weight is
$\tau(\mu, T) = \sum_b \prod_{i < k} (\mu_i \text{ if } b_i \text{ else } 1 - \mu_i)$, summed over
the Boolean strings $b$ of length $k$ with at least $T$ true entries. Let $Q$ be Hermitian and let
$\psi \in \mathbb{C}^{2^m}$ satisfy $\sum_s |\psi_s|^2 = 1$, with
$p = \operatorname{Re}(\psi^\dagger Q \psi)$. Then
$(\psi^{\otimes k})^\dagger \, T_k(Q, T)\, \psi^{\otimes k} = \tau((p, \dots, p), T)$. This is an acceptance probability only when $Q$ is an effect, $0 \le Q \le I$, so that $p \in [0, 1]$.
