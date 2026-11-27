# The powering construction of small-bias spaces

Let $F$ be a field with $2^m$ elements, identified with $\{0,1\}^m$ by an additive bijection $\beta$. The powering sample space maps a seed $(x, y) \in F \times F$ (that is, $2m$ bits) to the $n$ bits $\langle \beta(x^i), \beta(y)\rangle$ for $0 \le i < n$, where $\langle\cdot,\cdot\rangle$ is the inner product modulo $2$. Its bias at a set $S$ equals the fraction of $x \in F$ that are roots of $p_S(X) = \sum_{i \in S} X^i$, so the space is $((n-1)/2^m)$-biased. Hence for all $m \ge 1$ and $n$, $2m$ uniform bits can be stretched to $n$ bits with bias at most $(n-1)/2^m$.

## Proof sketch

The parity on $S$ equals $\langle \beta(p_S(x)), \beta(y)\rangle$. For fixed $x$ with $p_S(x) \ne 0$ this is an unbiased bit over uniform $y$; if $p_S(x) = 0$ it is constantly $0$. A nonzero polynomial of degree less than $n$ has at most $n-1$ roots.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [The Galois field with pⁿ elements](../../../FieldTheory/finite-fields/finite-field-existence.md)
- [Inner product of bit strings modulo two](../../../ComputerScience/quantum-algorithms/deutsch-jozsa-and-bernstein-vazirani-algorithms/bit-dot.md)

## Sources

- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992, Construction 3 and Proposition 3.
