# FGLSS graph of a nonadaptive PCP verifier

Let $V$ be a nonadaptive PCP verifier that on input $x$ uses $r$ random bits and queries positions $Q_\rho \subseteq \mathbb{N}$ on random string $\rho \in \{0,1\}^r$. A *view* is a pair $(\rho, a)$ where $a$ assigns a bit to each queried position of $Q_\rho$ (consistently, if a position is queried twice). The *FGLSS graph* $G_{V,x}$ has as vertices the accepting views, those $(\rho, a)$ with $V(x, \rho, a) = 1$, and joins two distinct views $(\rho, a)$ and $(\rho', a')$ by an edge when they assign different values to some common position (in particular distinct views with $\rho = \rho'$ are adjacent).

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- U. Feige, S. Goldwasser, L. Lovász, S. Safra and M. Szegedy, "Interactive Proofs and the Hardness of Approximating Cliques", Journal of the ACM 43(2), 1996.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
