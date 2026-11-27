# Khrapchenko: parity needs n^2 formula leaves

Every De Morgan formula computing the parity of $n$ bits has at least $n^2$ leaves (counted with multiplicity). Combined with Yablonskii's construction, the formula size of parity lies between $n^2$ and $\tfrac98n^2$.

## Proof sketch

Take $A$ the odd-weight and $B$ the even-weight inputs: $|A|=|B|=2^{n-1}$ and every odd input has $n$ even neighbours, so $|E(A,B)|=n2^{n-1}$ and Khrapchenko's bound gives $n^2$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Proof depends on

- [Khrapchenko's formula lower bound](khrapchenko-formula-lower-bound.md)

## Sources

- V. M. Khrapchenko, "Complexity of the realization of a linear function in the class of Π-circuits", Mathematical Notes of the Academy of Sciences of the USSR, 1971.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
