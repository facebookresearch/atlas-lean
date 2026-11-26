# Quantum Merlin-Arthur-Merlin games (QMAM)

A *QMAM protocol* is a three-message quantum interactive proof in which (1) Merlin sends a quantum register $\mathsf{X}$; (2) Arthur sends a single uniformly random public bit $b$; (3) Merlin sends a second register $\mathsf{Y}$; then Arthur applies a polynomial-time measurement $\{\Pi_b, I - \Pi_b\}$ on $\mathsf{X}\mathsf{Y}$ and accepts on outcome $\Pi_b$. The class $\mathrm{QMAM}$ consists of promise problems with QMAM protocols of completeness $2/3$ and soundness $1/3$.

## Depends on

- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
