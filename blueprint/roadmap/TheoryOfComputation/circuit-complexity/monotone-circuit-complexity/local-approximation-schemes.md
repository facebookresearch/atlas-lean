# Local approximation schemes (Razborov's method of approximations)

A *local approximation scheme* for a circuit $C$ over a basis with exact interpretation $I$ consists of an approximate interpretation $\tilde I$ (with a decoding of approximate values) and a finite sample space $X$. For each gate $g$ it provides an *exception set* $E_g\subseteq X$ of samples on which applying the approximate operation to correct approximate arguments may produce an incorrect approximate value, with $|E_g|\le c(g)$. Then on every sample outside $\bigcup_g E_g$ every wire's approximate value is correct; hence if the approximate output is wrong on at least $N$ samples (for every approximate circuit), any circuit computing the target satisfies $\sum_g c(g)\ge N$.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on the Monotone Complexity of Some Boolean Functions", Soviet Mathematics Doklady 31, 1985.
- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989), 1989 (formal framework of approximation models).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
