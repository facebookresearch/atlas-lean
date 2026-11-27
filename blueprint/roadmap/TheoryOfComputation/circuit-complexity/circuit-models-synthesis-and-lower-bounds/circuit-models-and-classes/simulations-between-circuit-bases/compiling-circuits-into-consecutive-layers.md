# Polynomial-time compilation of circuits into consecutive layers

There is a polynomial-time transformation that, given a fan-in-two Boolean circuit with $n$ inputs, $s$ gates and depth $d$, produces an equivalent *synchronous* (layered) circuit of the same depth $d$: every path from an input to a gate $G$ has the same length, so the gates split into layers $1,\dots,d$ and each gate reads only gates of the preceding layer (or inputs, for layer $1$). The new circuit is obtained by inserting identity (copy) gates and has at most $s\,d$ gates; appending identity layers pads it to any larger number of layers.

## Proof sketch

Let $\ell(G)$ be the length of a longest input-to-$G$ path. For a gate $G$ with predecessors $G_1,G_2$, where $\ell(G_1)=\ell(G)-1$, insert a chain of $\ell(G)-\ell(G_2)-1$ identity gates on the wire from $G_2$ to $G$ (and similarly for a wire from an input). Each original gate receives at most $d-1$ added gates, the depth is unchanged, and all longest-path lengths can be computed in linear time.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Section 12.1 (Definition 12.1.1 and Theorem 12.1.1: synchronous circuits).
