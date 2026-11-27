# Quantum Merlin-Arthur-Merlin games (QMAM)

A **QMAM protocol** (Marriott–Watrous, Definition 5.1) is a three-message quantum interactive proof in which (1) Merlin sends a quantum register $\mathsf{X}$; (2) Arthur sends a uniformly random public string $y \in \{0,1\}^{s(|x|)}$ of polynomially many random bits ($s(|x|) = \mathrm{poly}(|x|)$); (3) Merlin sends a second register $\mathsf{Y}$; then Arthur applies a polynomial-time measurement $\{\Pi_y, I - \Pi_y\}$ on $\mathsf{X}\mathsf{Y}$ and accepts on outcome $\Pi_y$. For completeness $c$ and soundness $s_0$, $\mathrm{QMAM}(c, s_0)$ is the class of promise problems admitting such a protocol with completeness at least $c$ and soundness at most $s_0$, and $\mathrm{QMAM} = \mathrm{QMAM}(2/3, 1/3)$. The special case $s(|x|) = 1$ (a single public coin flip) is called a **single-coin QMAM protocol** (used with completeness $1$ and soundness $1/2 + 2^{-r(|x|)}$ in Marriott–Watrous Theorem 5.4).

## Depends on

- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
