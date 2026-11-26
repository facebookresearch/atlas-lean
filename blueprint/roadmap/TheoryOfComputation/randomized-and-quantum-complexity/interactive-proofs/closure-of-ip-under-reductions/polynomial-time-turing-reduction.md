# Polynomial-time Turing (Cook) reduction

A language $L \subseteq \{0,1\}^*$ is *polynomial-time Turing reducible* (Cook reducible) to a language $L'$, written $L \le_T^p L'$, if there is a deterministic oracle Turing machine $M$ running in time polynomial in its input length such that for every $x$, $M^{L'}(x)$ accepts iff $x \in L$. The oracle queries may be adaptive (each query may depend on earlier answers). Every polynomial-time many-one reduction is a Cook reduction with a single query whose answer is returned unchanged.

## Depends on

- [Polynomial-time many-one reduction](../../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
