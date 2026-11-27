# All minterms in linear size

All $2^n$ minterms on $x_1,\dots,x_n$ can be computed simultaneously by one circuit over the full binary basis $B_2$ with $n$ inputs and $2^n$ outputs (the output indexed by $a\in\{0,1\}^n$ is the minterm $[x=a]$) of size $2^n+O(n\,2^{n/2})$ and depth $O(\log n)$.

## Proof sketch

With $O(n\,2^{n/2})$ gates compute in parallel all $2^{\lceil n/2\rceil}$ minterms on the first half of the variables and all $2^{\lfloor n/2\rfloor}$ minterms on the second half, each by a balanced tree; afterwards each of the $2^n$ minterms on all variables is the conjunction of one minterm from each half, one gate apiece. Derived here for De Morgan circuits with constants and negations charged: building the minterms of the first $i$ bits from those of the first $i-1$ bits by one conjunction with $x_i$ or $\neg x_i$ each gives, for every $n\ge0$, at most $4\cdot 2^n-3$ gates, the count being a geometric sum dominated by its last term.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987 (Chapter 3, Lemma 4.1, pp. 75–76).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
