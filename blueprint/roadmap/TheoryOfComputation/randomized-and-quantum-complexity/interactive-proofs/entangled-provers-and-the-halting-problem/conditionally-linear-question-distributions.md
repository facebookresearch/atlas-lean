# Conditionally linear question distributions

Let $V = V_1 \oplus \cdots \oplus V_k$ be a decomposition of $V = \mathbb{F}_2^m$ into coordinate subspaces. A map $L : V \to V$ is *conditionally linear* if $L(v) = \sum_{j=1}^k L_j(v_j)$, where each $L_j : V_j \to V_j$ is a linear map that is allowed to depend on the already computed values $L_1(v_1), \dots, L_{j-1}(v_{j-1})$ (and on nothing else). A *conditionally linear distribution* is the law of a pair $(L^A(z), L^B(z))$ for $z$ uniform on $V$ and conditionally linear maps $L^A, L^B$. A *normal form verifier* is a pair $(S, D)$ of Turing machines where $S$, on index $n$, describes a conditionally linear distribution over $\mathbb{F}_2^{m(n)} \times \mathbb{F}_2^{m(n)}$ and $D$, on $(n, x, y, a, b)$, decides acceptance; it defines a sequence of synchronous games $(V_n)_{n \ge 1}$.

## Depends on

- [Synchronous two-prover games](synchronous-two-prover-games.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
