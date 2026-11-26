# Uhlig's mass-production theorem

Let $d:\mathbb{N}\to\mathbb{N}$ satisfy $d(n)\log_2 n=o(n)$. Then every Boolean function $f$ on $n$ inputs satisfies

$$
C\bigl(f^{\times 2^{d(n)}}\bigr)\le(1+o(1))\,\frac{2^n}{n},
$$

uniformly in $f$: up to $2^{d(n)}$ independent copies of any $n$-variable function cost no more, asymptotically, than the worst-case single-copy bound of Lupanov.

## Proof sketch

One layer of Uhlig's construction evaluates two copies of a function on $p+m$ inputs from $2^p+1$ copies of functions on $m$ inputs, using a recovery code over the $p$-bit prefixes; iterating $d$ layers with $p=2\log_2 n+2$ multiplies the size by $(2^p+1)^d$ and adds lower-order overhead, which Lupanov's bound absorbs when $d\log n=o(n)$.

## Depends on

- [Mass complexity of a Boolean function](mass-complexity-of-a-boolean-function.md)

## Proof depends on

- [Lupanov's asymptotic circuit upper bound](../circuit-synthesis-upper-bounds/lupanov-circuit-upper-bound.md)

## Sources

- Dietmar Uhlig, "Networks Computing Boolean Functions for Multiple Input Values", Boolean Function Complexity, 1992.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
