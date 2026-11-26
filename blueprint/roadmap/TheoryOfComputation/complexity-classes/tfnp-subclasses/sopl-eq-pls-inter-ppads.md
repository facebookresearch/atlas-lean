# Göös et al.: SOPL = PLS ∩ PPADS and EOPL = PLS ∩ PPAD

$\mathsf{SOPL}=\mathsf{PLS}\cap\mathsf{PPADS}$ and $\mathsf{EOPL}=\mathsf{PLS}\cap\mathsf{PPAD}$.

## Proof sketch

For $\mathsf{PLS}\cap\mathsf{PPADS}\subseteq\mathsf{SOPL}$, combine a local-search instance with a sink-of-line instance: make the PLS transitions reversible by recording a path-pigeonhole history, which yields a potential line on a graph of width $n_1+2(n_1+n_2)$ whose sinks give solutions of one of the two instances. Together with $\mathsf{EOPL}=\mathsf{SOPL}\cap\mathsf{PPAD}$ and $\mathsf{PPAD}\subseteq\mathsf{PPADS}$ this gives the second equality.

## Depends on

- [End-of-Potential-Line and the classes EOPL and SOPL](end-of-potential-line.md)
- [The class PLS of polynomial local search problems](../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [EOPL = SOPL ∩ PPAD](eopl-eq-sopl-inter-ppad.md)
- [Inclusions among the TFNP subclasses](tfnp-subclass-inclusions.md)

## Sources

- Mika Göös et al., "Further Collapses in TFNP", 37th Computational Complexity Conference (CCC 2022), arXiv:2202.07761, 2022, Theorems 1 and 2.
