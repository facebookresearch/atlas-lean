# Iterates of a one-way permutation are one-way

Let $f$ be a length-preserving one-way permutation and let $k(n) \ge 1$ be computable in time polynomial in $n$ (for example $k(n) = \lceil n^c \rceil$ for a rational $c > 0$). Then $F(x) = f^{(k(|x|))}(x)$, the $k(|x|)$-fold iterate, is a one-way permutation. Concretely, an inverter for $F$ with success $\varepsilon$ is itself an inverter for $f$ after $k(n) - 1$ additional evaluations of $f$, with the same success probability.

## Proof sketch

Because $f$ is a permutation, $f^{(k-1)}(x)$ is uniform when $x$ is. Given $y = f(z)$ for uniform $z$, the reduction computes $f^{(k-1)}(y) = F(z)$ and inverts $F$; any preimage of $F(z)$ equals $z$ by injectivity.

## Depends on

- [One-way permutation families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-permutation.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
