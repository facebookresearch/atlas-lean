# All minterms in linear size

For every $n\ge 0$ there is a De Morgan circuit with $n$ inputs and $2^n$ outputs whose output indexed by $a\in\{0,1\}^n$ is the minterm $[x=a]$, with at most $4\cdot 2^n-3$ gates (constants and negations included).

## Proof sketch

Build the minterms of the first $i$ bits from those of the first $i-1$ bits by one conjunction with $x_i$ or $\neg x_i$ each; the number of gates is a geometric sum dominated by its last term.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
