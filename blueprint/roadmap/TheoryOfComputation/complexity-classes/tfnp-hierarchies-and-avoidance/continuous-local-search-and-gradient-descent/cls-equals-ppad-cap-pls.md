# CLS = PPAD ∩ PLS, with 2D-CLS, promise-CLS and Linear-CLS equal to CLS and Banach-type contraction problems complete

$\mathsf{CLS}=\mathsf{PPAD}\cap\mathsf{PLS}$, refuting the conjecture of Daskalakis and Papadimitriou that the inclusion is strict. Moreover the definition is robust: the classes defined via 2D-CONTINUOUS-LOCALOPT, via $n$-dimensional or general-polytope versions, via the promise version without violations, and via linear arithmetic circuits (gates without true multiplications, computing piecewise-linear functions) all coincide with CLS; the one-dimensional version is polynomial-time solvable. The previously known CLS-complete problems BANACH (a contraction map with an input metric, with violation witnesses) and METAMETRICCONTRACTION are $\mathsf{PPAD}\cap\mathsf{PLS}$-complete.

## Proof sketch

GENERAL-CONTINUOUS-LOCALOPT on $[0,1]^2$ is $\mathsf{PPAD}\cap\mathsf{PLS}$-hard even for promise instances; padding with a dummy third coordinate gives hard instances of 3D-CONTINUOUS-LOCALOPT, so $\mathsf{PPAD}\cap\mathsf{PLS}\subseteq\mathsf{CLS}$, and the reverse inclusion is the membership lemma. The linear variant follows because linear circuits efficiently approximate any Lipschitz well-behaved circuit to arbitrary precision. Completeness of BANACH and METAMETRICCONTRACTION follows from their known CLS-completeness.

## Depends on

- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](continuous-localopt-and-cls.md)
- [Well-behaved arithmetic circuits and Lipschitz violation witnesses for continuous total search problems](well-behaved-arithmetic-circuits.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [KKT, GD-LOCAL-SEARCH, GD-FIXPOINT and GENERAL-CONTINUOUS-LOCALOPT are PPAD ∩ PLS-complete on the unit square](gradient-descent-problems-ppad-pls-complete.md)
- [GENERAL-CONTINUOUS-LOCALOPT lies in PPAD ∩ PLS](general-continuous-localopt-in-ppad-and-pls.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
- Constantinos Daskalakis and Christos H. Papadimitriou, "Continuous Local Search", SODA (2011).
