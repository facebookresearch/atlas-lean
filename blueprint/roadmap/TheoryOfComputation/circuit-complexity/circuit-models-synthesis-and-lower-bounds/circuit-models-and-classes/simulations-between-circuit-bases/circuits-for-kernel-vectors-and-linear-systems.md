# Circuits for kernel vectors and linear systems over a field

Over a field $F$, Gaussian elimination is a fixed arithmetic computation: for all $r,c$ there is a circuit over the full binary basis of $F$ (every operation on at most two field elements, including division by nonzero elements with an arbitrary value at zero, counts as one gate) with a number of gates polynomial in $r$ and $c$ that, given an $r\times c$ matrix $A$, outputs a nonzero vector of $\ker A$ whenever one exists, and more generally solves consistent linear systems $Ax=b$ and returns kernel vectors with a prescribed nonzero entry. Over a finite field, composing with bit-blasting gives Boolean circuits of polynomial size.

## Proof sketch

Elimination with pivot selection is implemented by multiplexers on 'is zero' tests; back substitution sets free variables to fixed values.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Proof depends on

- [Bit-blasting circuits over a finite carrier with an injective encoding](bit-blasting-circuits-over-finite-carriers.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
