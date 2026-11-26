# Quantum soundness of the low individual degree test

There are universal constants $a \ge 1$ and $0 < b \le 1$ such that, with

$$\delta_{\mathrm{ld}}(\varepsilon, q, m, d, k) = a\,(dmk)^{a}\big(\varepsilon^{b} + q^{-b} + 2^{-bmd}\big),$$

the following holds for every $\varepsilon > 0$ and every parameter tuple $(q, m, d, k)$ of the low individual degree test. If a projective entangled strategy $(\psi, A, B)$ wins the test with probability at least $1 - \varepsilon$, then there are projective measurements $G^A$ and $G^B$ on the respective players' spaces, whose outcomes are $k$-tuples $(g_1, \dots, g_k)$ of polynomials $\mathbb{F}_q^m \to \mathbb{F}_q$ of individual degree at most $d$, such that, on the state $\psi$ and up to error $O(\delta_{\mathrm{ld}})$ in the consistency measure $\mathbb{E}_x \sum_{\alpha \ne \beta} \langle \psi | M^x_\alpha \otimes N^x_\beta | \psi \rangle$: player A's point measurement at a uniform point $u$ is consistent with B's outcome $(g_1(u), \dots, g_k(u))$ of $G^B$; A's outcome $(g_1(u), \dots, g_k(u))$ of $G^A$ is consistent with B's point measurement at $u$; and $G^A$ is consistent with $G^B$.

## Proof sketch

The test with $k = 1$ is the two-prover tensor code test for the $m$-fold tensor power of the degree-$d$ Reed–Solomon code over $\mathbb{F}_q$; its quantum soundness theorem gives the case $k = 1$, and a standard reduction extends it to general $k$.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", accepted version, arXiv:2001.04383v4, 2026, Theorem 7.8 and its proof.
