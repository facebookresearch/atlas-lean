# Counting functions with small De Morgan circuits

For all $n,s\ge 0$, the number of Boolean functions $f:\{0,1\}^n\to\{0,1\}$ with De Morgan circuit complexity at most $s$ is at most $2^{M}$, where

$$
M=(s+1)\bigl(2\lceil \log_2(n+s+1)\rceil+3\bigr).
$$

In particular at most $2^{O(s\log(n+s))}$ functions have circuits of size $s$, whereas there are $2^{2^n}$ functions in total.

## Proof sketch

A circuit with at most $s$ gates over a basis of at most $5$ operations is described by listing, for each gate, its operation (three bits) and two argument indices among at most $n+s$ wires, plus the output index; this gives an injective description of length $M$ bits.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal, 1949.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
