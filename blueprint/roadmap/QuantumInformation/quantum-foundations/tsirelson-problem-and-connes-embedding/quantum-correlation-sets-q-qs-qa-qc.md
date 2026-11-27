# Quantum correlation sets C_q, C_qs, C_qa and C_qc

Fix finite sets $\mathcal{X}$ (questions) and $\mathcal{A}$ (answers). A correlation is a vector $p = (p(a, b \mid x, y)) \in [0,1]^{\mathcal{A}^2 \times \mathcal{X}^2}$.

- $C_q$: correlations $p(a,b \mid x,y) = \langle \psi | A^x_a \otimes B^y_b | \psi\rangle$ with $\psi \in \mathbb{C}^d \otimes \mathbb{C}^d$, $d < \infty$, and POVMs $\{A^x_a\}_a$, $\{B^y_b\}_b$.
- $C_{qs}$: the same with arbitrary (possibly infinite-dimensional) Hilbert spaces $H_A \otimes H_B$.
- $C_{qa} := \overline{C_q}$, the closure.
- $C_{qc}$: correlations $p(a,b\mid x,y) = \langle \psi | A^x_a B^y_b | \psi \rangle$ on a single Hilbert space $H$ with POVMs satisfying $[A^x_a, B^y_b] = 0$ for all $x, y, a, b$.

The commuting-operator value of a game is $\omega^{co}(G) = \sup_{p \in C_{qc}} \sum_{x,y}\mu(x,y)\sum_{a,b}V(x,y,a,b)\, p(a,b\mid x,y)$, and $\omega^*(G)$ equals the same supremum over $C_q$ (equivalently over $C_{qa}$).

## Depends on

- [Two-player nonlocal games: classical and entangled values](../two-player-nonlocal-games-classical-and-entangled-values.md)

## Sources

- Marius Junge, Miguel Navascues, Carlos Palazuelos, David Perez-Garcia, Volkher B. Scholz, Reinhard F. Werner, "Connes embedding problem and Tsirelson's problem", Journal of Mathematical Physics 52 (2011); arXiv:1008.1142.
- Tobias Fritz, "Tsirelson's problem and Kirchberg's conjecture", Reviews in Mathematical Physics 24 (2012); arXiv:1008.1168.
- William Slofstra, "The set of quantum correlations is not closed", Forum of Mathematics, Pi 7 (2019); arXiv:1703.08618.
