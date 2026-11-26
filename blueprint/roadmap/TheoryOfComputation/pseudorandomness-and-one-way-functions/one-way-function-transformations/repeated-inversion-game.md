# Repeated inversion game for a one-way function

Let $f$ be a function on bit strings and $t(n)$ a polynomial. In the *repeated inversion game* the challenger samples $x_1, \dots, x_{t(n)}$ independently and uniformly from $\{0,1\}^n$ and gives $1^n$ and $y_i = f(x_i)$ for all $i$ to the adversary. The adversary may adaptively request any $x_i$ to be revealed, and finally outputs an index $j$ that was not revealed together with a candidate $x'$. It wins if $f(x') = y_j$.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Inversion experiment](../../../ComputerScience/cryptography/security-games/asymptotic-security/invert-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
