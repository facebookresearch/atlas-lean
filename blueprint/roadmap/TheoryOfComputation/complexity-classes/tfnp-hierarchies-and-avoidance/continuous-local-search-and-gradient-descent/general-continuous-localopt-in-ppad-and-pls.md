# GENERAL-CONTINUOUS-LOCALOPT lies in PPAD ∩ PLS

Recall that PPAD is the class of total search problems polynomial-time reducible to END-OF-LINE and PLS the class reducible to LOCALOPT (given circuits $S:[2^n]\to[2^n]$ and $V:[2^n]\to\mathbb{Z}$, find $v$ with $V(S(v))\ge V(v)$). For every dimension $n$, GENERAL-CONTINUOUS-LOCALOPT belongs to $\mathsf{PPAD}\cap\mathsf{PLS}$. In particular $\mathsf{CLS}\subseteq\mathsf{PPAD}\cap\mathsf{PLS}$.

## Proof sketch

PPAD: the map $F=\Pi_D\circ g$ is a continuous self-map of the compact convex set $D$, $L$-Lipschitz unless a violation is exhibited; if $\|F(x)-x\|\le\varepsilon/L$ then $L$-Lipschitzness of $p$ gives $p(F(x))\ge p(x)-\varepsilon$, so an approximate Brouwer fixed point solves the instance, and approximate fixed points of polynomially evaluable Lipschitz maps are computable in PPAD by the standard grid/Sperner reduction to END-OF-LINE (failures of Lipschitzness surface as violation pairs). PLS: restrict to a grid of mesh $\delta$, let the neighbour of a grid point be the grid rounding of $F(x)$ and the potential be $p$ scaled to integers; a PLS local optimum satisfies $p(\mathrm{round}(F(x)))\ge p(x)-\varepsilon/2$, and rounding moves the point by at most $\delta\sqrt n$, so with $\delta=\varepsilon/(2L\sqrt n)$ the point solves the instance or a violation appears.

## Depends on

- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](continuous-localopt-and-cls.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [END-OF-THE-LINE is total](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)

## Sources

- Constantinos Daskalakis and Christos H. Papadimitriou, "Continuous Local Search", SODA (2011).
- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
