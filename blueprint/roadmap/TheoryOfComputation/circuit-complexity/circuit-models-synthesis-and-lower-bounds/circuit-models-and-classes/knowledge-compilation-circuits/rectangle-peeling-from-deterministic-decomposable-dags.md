# Peeling large rectangles from deterministic decomposable DAGs

In a smooth decomposable DAG (unions of children with equal scopes, products of children with disjoint scopes), the inputs on whose accepting certificates a node $v$ occurs form a rectangle (its accepted assignments times its contexts). If moreover unions are disjoint (a smooth d-DNNF), every accepted input has a unique certificate, so the accepted set is partitioned according to the node of balanced scope on each certificate, and a d-DNNF of size $s$ partitions $f^{-1}(1)$ into at most $s$ disjoint balanced rectangles. In particular one can count accepted inputs, and inputs above any weight threshold, by dynamic programming over the DAG.

## Proof sketch

Decomposability makes the set of certificates through $v$ a product of a sub-certificate set and a context set; disjointness of unions makes certificates unique.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)

## Proof depends on

- [DNNF size bounds the multi-partition rectangle cover number](dnnf-size-bounds-rectangle-cover-number.md)

## Sources

- Adnan Darwiche, "Decomposable Negation Normal Form", Journal of the ACM, 2001.
- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016.
