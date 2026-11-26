# Commuting-operator strategies and value

A *commuting-operator strategy* for a game $G$ consists of a C*-algebra (or a Hilbert space $H$), a state (or unit vector $\psi \in H$), and POVMs $\{P^x_a\}$ and $\{Q^y_b\}$ acting on the same space with $[P^x_a, Q^y_b] = 0$ for all $x, y, a, b$; it answers with probability $p(a,b \mid x,y) = \langle \psi, P^x_a Q^y_b \psi\rangle$. The *commuting-operator value* $\mathrm{val}^{co}(G)$ is the supremum of its winning probability. Every tensor strategy is a commuting one (take $P^x_a \otimes 1$ and $1 \otimes Q^y_b$), so

$$\mathrm{val}(G) \le \mathrm{val}^*(G) \le \mathrm{val}^{co}(G).$$

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Sources

- R. Cleve, L. Liu and W. Slofstra, "Perfect Commuting-Operator Strategies for Linear System Games", Journal of Mathematical Physics 58(1), 2017.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
