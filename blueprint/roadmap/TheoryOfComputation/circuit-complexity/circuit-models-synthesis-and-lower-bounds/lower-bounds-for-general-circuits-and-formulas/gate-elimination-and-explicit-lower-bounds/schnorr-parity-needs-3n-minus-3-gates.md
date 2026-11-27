# Schnorr: parity needs 3(n - 1) binary De Morgan gates

Every De Morgan circuit computing the parity $x_1\oplus\cdots\oplus x_n$ of $n\ge 1$ bits contains at least $3(n-1)$ AND and OR gates, regardless of the number of negations and constants it uses. This is tight.

## Proof sketch

Gate elimination, for $n\ge 2$: let $g$ be a first binary gate of an optimal circuit; its arguments are literals of two variables $x_i,x_j$. If $x_i$ fed only $g$, a constant for $x_j$ making $g$ constant would make the output independent of $x_i$, so $x_i$ feeds a second binary gate $g'$. Setting $x_i$ to the constant that makes $g$ constant removes $g$, $g'$ and a successor $h$ of $g$ ($g$ is not the output, since parity of $n-1\ge 1$ bits is not constant; if $h=g'$, the successor of $g'$ is removed instead). The restricted function is parity or its negation on $n-1$ bits; induct on $n$. The chained construction gives the matching upper bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Proof depends on

- [Parity of n + 1 bits with 3n binary De Morgan gates](../../circuit-synthesis-and-upper-bounds/circuit-synthesis-upper-bounds/parity-circuit-with-3n-binary-gates.md)

## Sources

- Claus-Peter Schnorr, "Zwei lineare untere Schranken für die Komplexität Boolescher Funktionen", Computing 13, 155–171, 1974.
- Claus-Peter Schnorr, "The Combinational Complexity of Equivalence", Theoretical Computer Science 1(4), 289–295, 1976.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
