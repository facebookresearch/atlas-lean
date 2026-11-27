# Dynamic treewidth data structures under a treewidth promise

Fix an integer $k$. A **dynamic treewidth data structure** maintains an $n$-vertex graph $G$, initially edgeless on a fixed vertex set $V$, under updates that insert or delete a single edge, under the **promise** that $\operatorname{tw}(G)\le k$ holds after every update. After each update it maintains (explicitly, as a pointer structure) a tree decomposition of $G$ of width at most $\alpha(k)$. The **amortized update time** is the total time of any sequence of $q$ updates divided by $q$. A **dynamic programming scheme** on tree decompositions (computing a state per node from the states of its children) is maintained if after each update the state at the root is available; for CMSO$_2$-definable properties this is the dynamic version of Courcelle's theorem. Dynamic graph problems of this kind complement fine-grained lower bounds for general dynamic graphs.

## Depends on

- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Dynamic graph problems](../../../fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Sources

- Tuukka Korhonen, Konrad Majewski, Wojciech Nadara, Michał Pilipczuk and Marek Sokołowski, "Dynamic treewidth", FOCS (2023), arXiv:2304.01744.
- Tuukka Korhonen, "Dynamic Treewidth in Logarithmic Time", arXiv preprint (2025), arXiv:2504.02790.
