# There is no universal hard-core predicate

Let $f$ be a one-way function and $b : \{0,1\}^* \to \{0,1\}$ a polynomial-time computable predicate. Then $g(x) = f(x) \| b(x)$ is a one-way function, and $b(x)$ is the last bit of $g(x)$, computable in deterministic polynomial time from the image alone. Hence $b$ is not a hard-core predicate of $g$; no fixed polynomial-time predicate is hard-core for every one-way function.

## Proof sketch

An inverter for $g$ is given $f(x)$ and $b(x)$; an inverter for $f$ computes nothing extra but can guess $b(x)$ with probability at least one half, so any inverter for $g$ yields one for $f$ losing at most a factor of two.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Hard-core predicate of a function](../hard-core-predicates-and-stretch/hard-core-predicate.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
