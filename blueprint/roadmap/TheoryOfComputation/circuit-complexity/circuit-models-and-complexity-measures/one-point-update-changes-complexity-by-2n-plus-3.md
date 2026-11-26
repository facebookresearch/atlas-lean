# Changing one value changes circuit complexity by at most 2n + 3

Let $f,g:\{0,1\}^n\to\{0,1\}$ differ on exactly one input $a$. Then $|C(f)-C(g)|\le 2n+3$, where $C$ denotes De Morgan circuit complexity with every gate charged. Consequently every Boolean function on $n$ bits satisfies $C(f)\le 2^n(2n+3)+1$, and a constant function has complexity exactly $1$.

## Proof sketch

The minterm of $a$ (a conjunction of $n$ literals) costs at most $2n$ gates beyond the inputs including negations, and $g=f\oplus[x=a]$ is obtained from a circuit for $f$ by at most three further gates. Walking from a constant to $f$ one point at a time gives the global bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
