# Compressing collision-resistant hash families are one-way

Let $H$ be a keyed hash family mapping $\mathrm{in}(n)$-bit inputs to $\mathrm{out}(n)$-bit digests under keys $k$, and suppose $2^{\mathrm{out}(n)}/2^{\mathrm{in}(n)}$ is negligible. If $H$ is collision resistant, then the function $(k, x) \mapsto (k, H_k(x))$ is one-way.

## Proof sketch

Given an inverter, the collision finder samples $x$, inverts $(k, H_k(x))$ and outputs the returned preimage together with $x$. Since all but a negligible fraction of inputs lie in fibers of size at least two (at most $2^{\mathrm{out}}$ inputs have no sibling), and the inverter's view is independent of which element of the fiber was sampled, the returned preimage differs from $x$ with probability at least about half of the inversion probability.

## Depends on

- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- O. Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
