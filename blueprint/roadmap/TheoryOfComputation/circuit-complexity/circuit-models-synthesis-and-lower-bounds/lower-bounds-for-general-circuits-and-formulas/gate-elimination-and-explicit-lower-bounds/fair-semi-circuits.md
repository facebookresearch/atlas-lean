# Fair semi-circuits over the full binary basis

A *cyclic xor-circuit* is a directed graph, not necessarily acyclic, whose internal gates have in-degree two and compute affine operations ($x\oplus y$, $x\oplus y\oplus 1$, passing or constant gates), with possibly several outputs. It corresponds to a linear system over $\mathbb{F}_2$ with one equation per internal gate (the gate equals the operation applied to its inputs), whose square matrix does not depend on the values of the input variables. The cyclic xor-circuit is *fair* if this matrix has full rank; then for every assignment to the inputs there are unique consistent gate values, and every gate computes an affine function of the inputs. A *semi-circuit* is the composition of a cyclic xor-circuit $X$ with an ordinary acyclic circuit $C$ over the full binary basis $B_2$ whose inputs may be gates of $X$, with no wires from $C$ back to $X$; it is *fair* if $X$ is fair. Every ordinary $B_2$ circuit is a fair semi-circuit with $X$ consisting of its inputs only. The gate-elimination proof of the $(3+\tfrac{1}{86})n-o(n)$ lower bound for affine dispersers works with fair semi-circuits, because affine substitutions and gate removals keep a semi-circuit fair.

## Depends on

- [The full binary basis B2 and the basis U2](../../circuit-models-and-classes/circuit-models-and-complexity-measures/full-binary-basis-b2-and-u2.md)
- [Affine dispersers](affine-dispersers.md)

## Sources

- Magnus Gausdal Find, Alexander Golovnev, Edward A. Hirsch, Alexander S. Kulikov, "A Better-than-3n Lower Bound for the Circuit Complexity of an Explicit Function", IEEE 57th Annual Symposium on Foundations of Computer Science, 89–98, 2016 (Section 2.1).
