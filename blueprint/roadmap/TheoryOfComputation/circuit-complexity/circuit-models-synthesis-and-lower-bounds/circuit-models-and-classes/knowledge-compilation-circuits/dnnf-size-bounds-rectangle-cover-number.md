# DNNF size bounds the multi-partition rectangle cover number

If a DNNF with $s$ nodes (gates, literal leaves included) computes $f$ on $n\ge2$ variables, then $f^{-1}(1)$ is covered by at most $s$ balanced rectangles (each for its own partition with both sides of at least $n/3$ variables). Consequently any function whose $1$-set needs many balanced rectangles requires large DNNFs.

## Proof sketch

Each accepted input has a certificate (a sub-DAG choosing one child at each $\vee$-gate), and by decomposability the inputs accepted by certificates through a gate $g$ form a rectangle with respect to the scope of $g$ and its complement. Eliminate gates one at a time: while the remaining DNNF has more than $2n/3$ variables, descend from the output to a gate whose scope has between $n/3$ and $2n/3$ variables, record its rectangle and eliminate it (relabel it $0$ and propagate); once at most $2n/3$ variables remain, record the rectangle of the remaining satisfying set, padded to a balanced partition. Eliminating $g$ loses only inputs in the rectangle of $g$, so at most $s$ recorded rectangles cover $f^{-1}(1)$.

## Depends on

- [Balanced multi-partition rectangle covers](multi-partition-rectangle-covers.md)
- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)

## Sources

- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016, Theorems 1 and 6.
