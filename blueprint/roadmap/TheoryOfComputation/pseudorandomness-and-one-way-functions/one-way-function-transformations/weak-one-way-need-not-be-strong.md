# A weak one-way function need not be strongly one-way

If a one-way function exists, then there exists a weak one-way function that is not strongly one-way. For instance, from a one-way $f$ define $g$ on inputs $b \| x$ by $g(b \| x) = b \| f(x)$ when the first bits $b$ (a block of fixed small length) are all zero, and $g(b \| x) = b \| x$ otherwise. Then the identity inverter succeeds on most inputs, while every efficient inverter fails on a noticeable fraction (the hard branch), so $g$ is weakly one-way with a constant failure bound.

## Proof sketch

On the easy branch the image reveals the input; on the hard branch an inverter for $g$ yields an inverter for $f$ at a shifted length. The hard branch has constant probability, which gives weak one-wayness with a constant polynomial, and the easy branch rules out strong one-wayness.

## Depends on

- [Weak one-way function](weak-one-way-function.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
