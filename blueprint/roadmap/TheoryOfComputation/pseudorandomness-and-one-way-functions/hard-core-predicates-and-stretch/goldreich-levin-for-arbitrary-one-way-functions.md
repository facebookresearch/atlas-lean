# Goldreich–Levin for arbitrary one-way functions

Let $f$ be any one-way function (not necessarily a permutation or length preserving). Define $g(x, r) = (f(x), r)$ for $|x| = |r|$, padded with at most one spare bit so that every input length is covered. Then the inner product $b(x, r) = \langle x, r \rangle = \bigoplus_i x_i r_i \bmod 2$ is a hard-core predicate of $g$, against probabilistic polynomial-time predictors. This predicate is hard-core for $g$, not for $f$ itself.

## Proof sketch

A predictor with advantage $\varepsilon$ on a noticeable set of good $x$ gives a Boolean oracle $r \mapsto B(r)$ agreeing with $\langle x, \cdot\rangle$ on a $\tfrac12 + \varepsilon/2$ fraction. The Goldreich–Levin list decoder recovers a short list containing $x$, and checking $f$ on each candidate inverts $f$ with noticeable probability.

## Depends on

- [Hard-core predicate of a function](hard-core-predicate.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Inner product modulo 2](../goldreich-levin-theorem/xor-dot.md)

## Proof depends on

- [Goldreich–Levin list decoding of the Hadamard code with oracle access](goldreich-levin-list-decoding.md)
- [Goldreich-Levin: hardcore predicate from one-way permutations](../goldreich-levin-theorem/goldreich-levin.md)

## Sources

- O. Goldreich and L. A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
