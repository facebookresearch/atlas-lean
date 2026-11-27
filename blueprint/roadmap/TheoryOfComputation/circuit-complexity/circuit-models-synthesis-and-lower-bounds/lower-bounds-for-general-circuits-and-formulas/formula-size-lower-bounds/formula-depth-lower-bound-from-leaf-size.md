# Formula depth from formula leaf size

A De Morgan formula with at most $d$ AND and OR gates on every root-to-leaf path has at most $2^d$ leaves. Hence if every formula for $f$ has at least $L$ leaves, every formula (equivalently, every fan-in-two De Morgan circuit) for $f$ has depth at least $\log_2 L$; in particular parity of $n$ bits requires depth at least $2\log_2 n$.

## Proof sketch

A binary tree of depth $d$ has at most $2^d$ leaves, and a circuit unfolds into a formula of the same depth.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Unfolding a circuit into a formula of the same depth](../../circuit-models-and-classes/circuit-models-and-complexity-measures/unfolding-a-circuit-into-a-formula.md)
- [Khrapchenko: parity needs n^2 formula leaves](khrapchenko-parity-needs-n-squared-leaves.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
