# One-way functions have negligible output collision probability

For every function $f$ and every $n$, the probability that $f(x) = f(x')$ for independent uniform $x, x' \in \{0,1\}^n$ equals the success probability of the inverter that ignores its input and outputs a fresh uniform $n$-bit string. Hence every one-way function has negligible output collision probability, with no injectivity, regularity or length-preservation assumption.

## Proof sketch

The guessing inverter succeeds on challenge $f(x)$ exactly when its guess $x'$ satisfies $f(x') = f(x)$; this guesser runs in polynomial time.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
