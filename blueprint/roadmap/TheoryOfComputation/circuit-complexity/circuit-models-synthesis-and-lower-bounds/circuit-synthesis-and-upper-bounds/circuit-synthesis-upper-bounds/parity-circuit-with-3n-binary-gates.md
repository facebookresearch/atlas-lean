# Parity of n + 1 bits with 3n binary De Morgan gates

The parity of $n+1$ bits is computed by a De Morgan circuit with $4n$ gates, of which $3n$ are AND or OR gates, by chaining $x\oplus y=(x\vee y)\wedge\neg(x\wedge y)$.

## Proof sketch

Each exclusive or of two wires uses one OR, one AND, one NOT and one further AND.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
