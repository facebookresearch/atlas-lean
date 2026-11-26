# Iterates of a one-way function need not be one-way

If a one-way function exists, then there is a one-way function $f$ with a single polynomial-time output length per input length such that for every count $k(n)$ with $k(n) \ge 2$ for all large $n$ (in particular $k(n) = \lceil n^c \rceil$ for every real $c > 0$), the iterate $x \mapsto f^{(k(|x|))}(x)$ is not one-way.

## Proof sketch

Build $f$ from a one-way $g$ so that $f$ maps every input to an image of a special form on which $f$ is constant (for instance, padding $g(x)$ with zeros and sending padded strings to a fixed string). Then $f$ remains one-way, but the second iterate is constant, so any fixed preimage inverts it.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Normalizing the output length of a one-way function](normalizing-one-way-function-output-length.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
