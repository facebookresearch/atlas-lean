# Naor–Yung: one-way permutations yield universal one-way hash functions

Let $f$ be a one-way permutation. Then there is a keyed hash family defined on all bit strings, with polynomial-time keys and evaluation, that is target collision resistant: a probabilistic polynomial-time adversary that commits to a target $x$ before seeing a uniform key $k$ finds $x' \ne x$ with $H_k(x') = H_k(x)$ only with negligible probability. One step of the construction is $x \mapsto \pi_k(f(x))$, where $\pi_k$ drops one bit after a key-dependent invertible mixing (the original uses a pairwise-independent hash followed by truncation); a tree of such steps extends the domain.

## Proof sketch

Given a target $x$ and a challenge $y = f(z)$, the reduction chooses the key so that the compressed image of $f(x)$ collides exactly with that of $y$, which is possible because the mixing is pairwise independent and the key is uniform conditioned on this constraint. A collision $x'$ then satisfies $f(x') = y$, inverting $f$.

## Depends on

- [One-way permutation families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-permutation.md)
- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- M. Naor and M. Yung, "Universal One-Way Hash Functions and their Cryptographic Applications", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
- O. Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
