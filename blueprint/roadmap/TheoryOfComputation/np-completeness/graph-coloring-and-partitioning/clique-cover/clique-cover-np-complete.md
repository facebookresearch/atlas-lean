# CLIQUE COVER is NP-complete

The CLIQUE COVER decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Karp proves it by reducing CHROMATIC NUMBER: a graph $G$ has a proper colouring with $k$ colours exactly when the vertices of its complement $\overline{G}$ are covered by $k$ cliques, the colour classes, so $(G, k) \mapsto (\overline{G}, k)$ is a reduction. With the vertex count written in binary, the complement of a graph with few listed edges can have exponentially many edges, so the reduction first compacts the instance: it keeps the endpoints of the listed edges and, if some vertex lies on no listed edge, one such isolated vertex, renumbered. This does not change $k$-colourability (the other isolated vertices can share the representative's colour, and a graph with at least one vertex has no colouring with $0$ colours either way), and leaves at most $2|E| + 1$ vertices, whose complement has polynomially many edges. Inputs that are not well-formed instances are sent to a fixed no-instance.

## Informally uses

- [GRAPH COLORING is NP-complete](../graph-coloring/graph-coloring-np-complete.md): the source problem of Karp's reduction.

## Sources

- Richard M. Karp, "Reducibility among combinatorial problems", in Raymond E. Miller and James W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, 1972, 85–103, the reduction CHROMATIC NUMBER ∝ CLIQUE COVER. Reprinted in Michael Jünger et al. (eds.), *50 Years of Integer Programming 1958–2008*, Springer, 2010, chapter 8, 219–241.
