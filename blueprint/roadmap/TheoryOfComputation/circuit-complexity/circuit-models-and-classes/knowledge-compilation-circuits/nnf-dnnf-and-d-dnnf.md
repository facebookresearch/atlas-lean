# Negation normal form circuits, DNNF and d-DNNF

A *negation normal form (NNF) circuit* over variables $x_1,\dots,x_n$ is a DAG whose leaves are literals $x_i,\neg x_i$ or constants and whose inner nodes are fan-in-two $\wedge$ and $\vee$ gates. It is *decomposable* (a DNNF) if for every $\wedge$-gate the two sub-DAGs mention disjoint sets of variables, and *deterministic* if for every $\vee$-gate the two disjuncts are mutually exclusive (no input satisfies both); a d-DNNF is a deterministic DNNF. It is *smooth* if both arguments of every $\vee$-gate mention the same variables. Size is the number of nodes.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Adnan Darwiche, "Decomposable Negation Normal Form", Journal of the ACM, 2001.
- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016.
