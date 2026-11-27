# Counting functions with small De Morgan circuits

For all $n,s\ge 0$, let $N(n,s)$ be the number of Boolean functions $f:\{0,1\}^n\to\{0,1\}$ computed by a circuit with at most $s$ gates over the five De Morgan operations ($\wedge$, $\vee$, $\neg$ and the two constants, every gate counted). Then

$$
N(n,s)\cdot s! \le (s+1)\bigl(5(n+s+1)^2\bigr)^{s}\,(n+s).
$$

As a corollary, $N(n,s)\le 2^{M}$, where

$$
M=(s+1)\bigl(2\lceil \log_2(n+s+1)\rceil+3\bigr),
$$

since $s!\ge 1$, $5\le 2^3$ and $(s+1)(n+s)\le (n+s+1)^2$. In particular at most $2^{O((s+1)\log(n+s+2))}$ functions have circuits of size $s$, whereas there are $2^{2^n}$ functions in total.

## Proof sketch

A circuit with at most $s$ gates is described by its number of gates, the list of its gates (each one of the five operations applied to at most two of the at most $n+s+1$ available wires, so at most $5(n+s+1)^2$ choices per gate) and its output wire among at most $n+s$ wires; counting these descriptions modulo the relabelings of the gates gives the factor $s!$. The corollary is the arithmetic above.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Sources

- CSLib, `Cslib.Circuits.Boolean.card_computableFunctions_mul_factorial_le` (module `Cslib.Computability.Circuit.Boolean.Counting`): the displayed bound with the factor $s!$.
- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 59–98, 1949.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
