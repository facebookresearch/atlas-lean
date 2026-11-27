# Ikenmeyer–Mulmuley–Walter: deciding positivity of Kronecker coefficients is NP-hard

Given partitions $\lambda, \mu, \nu$ of $N$ encoded in unary, deciding whether $g(\lambda, \mu, \nu) > 0$ is NP-hard. Moreover, there are infinitely many triples $(\lambda, \mu, \nu)$ of partitions with $g(\lambda,\mu,\nu) = 0$ although the triple lies in the Kronecker polytope (the moment polytope of the corresponding representations), so Kronecker coefficients do not have the saturation property.

## Proof sketch

Reduce from 3-dimensional matching (or a variant of it) by encoding a matching problem in the lower bound for Kronecker coefficients given by counting certain $3$-dimensional binary contingency tables with prescribed marginals; for two-row shapes the Kronecker coefficient equals such a count, and zero counts correspond to the absence of a perfect matching. The non-saturation statement follows from explicit families constructed by the same encoding.

## Depends on

- [Kronecker coefficients of the symmetric group](kronecker-coefficients.md)

## Sources

- C. Ikenmeyer, K. D. Mulmuley, M. Walter, "On vanishing of Kronecker coefficients", Computational Complexity 26 (2017) 949-992, arXiv:1507.02955.
