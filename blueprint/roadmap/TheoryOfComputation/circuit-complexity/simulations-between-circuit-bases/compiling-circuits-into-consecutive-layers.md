# Polynomial-time compilation of circuits into consecutive layers

There is a polynomial-time transformation that, given a Boolean circuit with $n$ inputs, $s$ gates, $m$ outputs and output depth $d$, produces a *layered* circuit (each node reads only the preceding layer; copy nodes carry values across layers; NAND nodes may read a wire twice) with $2d+O(1)$ layers, each of width $O(n+s)$, computing the same outputs on the last layer. The encoded size is $O\bigl(d(n+3s)\log(n+3s)\bigr)$, and layered circuits can be padded with identity layers to any larger layer count in polynomial time.

## Proof sketch

Compute all wire depths; at each original depth use one preparation layer (copying all previously available values) and one finishing layer that computes the gates of that depth from values in the previous layer.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
