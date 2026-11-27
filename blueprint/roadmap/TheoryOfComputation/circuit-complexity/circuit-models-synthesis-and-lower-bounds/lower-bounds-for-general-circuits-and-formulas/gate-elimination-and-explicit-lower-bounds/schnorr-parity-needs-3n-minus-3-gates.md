# Schnorr: parity needs 3(n - 1) binary De Morgan gates

Every De Morgan circuit computing the parity $x_1\oplus\cdots\oplus x_n$ of $n\ge 1$ bits contains at least $3(n-1)$ AND and OR gates, regardless of the number of negations and constants it uses. This is tight.

## Proof sketch

Gate elimination: in a minimal circuit some input feeds two binary gates, and at least one of them has a successor; fixing that input to the constant that makes one of these gates constant eliminates at least three binary gates, while the restricted function is parity (or its negation) on $n-1$ bits. Induct on $n$. The chained construction gives the matching upper bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Proof depends on

- [Parity of n + 1 bits with 3n binary De Morgan gates](../../circuit-synthesis-and-upper-bounds/circuit-synthesis-upper-bounds/parity-circuit-with-3n-binary-gates.md)

## Sources

- Claus-Peter Schnorr, "Zwei lineare untere Schranken für die Komplexität Boolescher Funktionen", Computing, 1974.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
