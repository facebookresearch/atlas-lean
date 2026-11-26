# Unique Sink Orientations of cubes lie in UEOPL

A **unique sink orientation (USO)** of the $n$-cube is an orientation of its edges such that every face has exactly one sink; it is given succinctly by a circuit returning, for each vertex, the orientation of its $n$ incident edges. Recognizing USOs is coNP-complete, so the search problem USO asks for the global sink or a short certificate (such as a face with two sinks) that the orientation is not a USO. USO lies in UEOPL under promise-preserving reductions; before this it was not known to lie in PPAD or PLS, answering Kalai's challenge to place it in a non-trivial subclass of TFNP.

## Proof sketch

View the cube as the grid $\{0,1\}^n$ and let $D_i(v)$ be zero if $v$ is the sink of its edge in direction $i$, and up or down according to the edge's orientation otherwise. Unique sinks on faces give unique fixpoints on $i$-slices, and the second OPDC condition follows because the sink of a face is reached by following outgoing edges. Each OPDC violation produced is converted into a face with zero or two sinks, a USO violation; then apply OPDC in UEOPL.

## Depends on

- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [OPDC lies in UEOPL under promise-preserving reductions via a surface-walking line with a lexicographic potential](opdc-in-ueopl.md)
- [One-Permutation Discrete Contraction (OPDC): direction functions on a grid with unique fixpoints on i-slices](one-permutation-discrete-contraction.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
