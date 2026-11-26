# KKT, GD-LOCAL-SEARCH, GD-FIXPOINT and GENERAL-CONTINUOUS-LOCALOPT are PPAD ∩ PLS-complete on the unit square

The problems KKT, GD-LOCAL-SEARCH, GD-FIXPOINT and GENERAL-CONTINUOUS-LOCALOPT are $\mathsf{PPAD}\cap\mathsf{PLS}$-complete, and remain so when the domain is fixed to $[0,1]^2$ and when only promise instances (no violations) are considered. Equivalently, the class GD of problems reducible to finding a point where projected gradient descent with fixed step size terminates on a bounded polytope equals $\mathsf{PPAD}\cap\mathsf{PLS}$.

## Proof sketch

Domain- and promise-preserving reductions connect the three gradient problems in a triangle: an approximate fixed point of the projected step yields an approximate KKT point and conversely (using the Taylor bound to control $f$ along a step), and a point where descent improves by less than $\varepsilon$ is, by the Taylor bound, one where the step is short. GD-LOCAL-SEARCH reduces to GENERAL-CONTINUOUS-LOCALOPT with $p=f$ and $g(x)=x-\eta\nabla f(x)$, which lies in $\mathsf{PPAD}\cap\mathsf{PLS}$. Hardness transfers from KKT on $[0,1]^2$ along the domain-preserving reductions.

## Depends on

- [GD-LOCAL-SEARCH and GD-FIXPOINT: termination points of projected gradient descent with fixed step size](gd-local-search-and-gd-fixpoint.md)
- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](continuous-localopt-and-cls.md)
- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Fearnley–Goldberg–Hollender–Savani: KKT on the unit square is PPAD ∩ PLS-hard, already for promise instances](kkt-unit-square-ppad-pls-hard.md)
- [GENERAL-CONTINUOUS-LOCALOPT lies in PPAD ∩ PLS](general-continuous-localopt-in-ppad-and-pls.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
