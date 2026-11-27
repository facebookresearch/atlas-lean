# Conditionally linear question distributions

Let $V = \mathbb{F}_2^m$, the case used by normal form verifiers, and call a subspace of $V$ a *register subspace* if it is spanned by a set of standard basis vectors. *Conditionally linear* (CL) maps $L : V \to V$ are defined by their number of levels. The only $0$-level CL map is the zero map. For $\ell \ge 1$, an $\ell$-level CL map has the form $L(x) = L_1(x_{V_1}) + L_{>1,\,L_1(x_{V_1})}(x_{V_{>1}})$, where $V = V_1 \oplus V_{>1}$ for complementary register subspaces $V_1, V_{>1}$, $L_1 : V_1 \to V_1$ is linear, and for each value $u$ of $L_1$ the map $L_{>1,u}$ is an $(\ell-1)$-level CL map on $V_{>1}$. Thus $L$ applies linear maps to successive blocks of coordinates, and both the next block $V_j$ and the next linear map may depend on the values already computed. A *conditionally linear distribution* is the law of a pair $(L^A(z), L^B(z))$ for $z$ uniform on $V$ and CL maps $L^A, L^B$. A *normal form verifier* is a pair $(S, D)$ of Turing machines where $S$, on index $n$, describes a conditionally linear distribution over $\mathbb{F}_2^{m(n)} \times \mathbb{F}_2^{m(n)}$ and $D$, on $(n, x, y, a, b)$, decides acceptance; it defines a sequence of two-prover one-round nonlocal games $(V_n)_{n \ge 1}$ with question sets $\{0,1\}^{m(n)}$, which need not be synchronous.

## Depends on

- [Synchronous two-prover games](synchronous-two-prover-games.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
