# DNNF size bounds the multi-partition rectangle cover number

If a DNNF with $s$ nodes computes $f$ on $n\ge2$ variables, then $f^{-1}(1)$ is covered by at most $s$ balanced rectangles (each for its own partition with both sides of at least $n/3$ variables). Consequently any function whose $1$-set needs many balanced rectangles requires large DNNFs.

## Proof sketch

Each accepted input has a certificate (a sub-DAG choosing one child at each $\vee$-gate). Every certificate passes through a node whose variable scope has between $n/3$ and $2n/3$ variables; the inputs whose certificates pass through a given node form a rectangle with respect to that node's scope and its complement, by decomposability.

## Depends on

- [Balanced multi-partition rectangle covers](multi-partition-rectangle-covers.md)

## Sources

- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016.
