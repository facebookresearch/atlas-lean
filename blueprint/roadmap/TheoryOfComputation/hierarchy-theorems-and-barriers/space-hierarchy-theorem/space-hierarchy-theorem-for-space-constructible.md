# Space hierarchy theorem for space-constructible bounds

If $f$ and $g$ are space-constructible, $g(n) \ge \log n$ and $f(n) = o(g(n))$, then $\mathsf{DSPACE}(f(n)) \subsetneq \mathsf{DSPACE}(g(n))$. In particular $\mathsf{L} \subsetneq \mathsf{PSPACE}$.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)

## Expansion

This page becomes ready once:

- Space-constructible functions (statement prerequisite; not yet stated)

## Sources

- R. E. Stearns, J. Hartmanis and P. M. Lewis II, "Hierarchies of memory limited computations", *Proceedings of the 6th IEEE Symposium on Switching Circuit Theory and Logical Design*, 1965
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, <https://theory.cs.princeton.edu/complexity/>, Theorem 3.2
