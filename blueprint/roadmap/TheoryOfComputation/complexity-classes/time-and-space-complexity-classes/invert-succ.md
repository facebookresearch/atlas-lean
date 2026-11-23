# Inversion success probability

Let $f$ be a family of functions, $f_n$ mapping $n$-bit
strings to bitstrings, and let $A$ be an inverter mapping a triple $(n, y, r)$ of a length $n$,
an output $y$ and a coin string $r$ to a bitstring. For natural numbers $n$ and $m$, the
inversion success probability of $A$ against $f$ at length $n$ with $m$ coins is the fraction of
the $2^{n+m}$ pairs $(x, r)$ of an $n$-bit string $x$ and an $m$-bit string $r$ such that
$f_n(x') = f_n(x)$, where $x'$ is the $n$-bit string whose $i$-th bit is the $i$-th bit of
$A(n, f_n(x), r)$, or false when that output has no $i$-th bit.

The inverter receives the length $n$ explicitly: when output lengths vary, it could not
otherwise recover $n$ from $f_n(x)$ alone.

## Sources

- O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University Press, 2001, Section 2.2.
