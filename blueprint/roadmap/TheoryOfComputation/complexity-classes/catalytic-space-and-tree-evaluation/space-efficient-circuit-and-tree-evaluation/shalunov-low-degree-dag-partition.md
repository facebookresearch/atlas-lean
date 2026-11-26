# Shalunov's low-degree DAG partition lemma

Let $G$ be a directed acyclic graph with $s$ vertices and maximum in-degree $d\gt 1$, and let $b\in[d,s]$ be an integer. Then there is a subdivision $G'$ of $G$ (obtained by replacing edges by directed paths through new vertices) and a partition $P$ of the vertices of $G'$ such that:

1. every part of $P$ has at most $b$ vertices;
2. every vertex of the quotient graph $G'/P$ has in-degree at most $2$;
3. every directed path in $G'/P$ has length less than $d\cdot s/b$.

Here $G'/P$ has one vertex per part and an edge from part $A$ to part $B$ whenever some edge of $G'$ goes from $A$ to $B$; it is acyclic when parts are chosen as intervals of a topological order. A refined version trades final in-degree against depth: in-degree $d+1$ allows depth $s/b$.

## Proof sketch

First cut a topological ordering of $G$ into consecutive intervals of size at most $b/d$, producing a quotient DAG with about $d\cdot s/b$ parts, so its depth is bounded by its size regardless of the structure of $G$. The in-degree of a part can be as large as the number of wires entering it; subdividing those wires and routing them through binary merging trees placed inside parts of size at most $b$ reduces every in-degree to $2$ without lengthening any quotient path.

## Proof depends on

- [The Circuit Value Problem](../../../completeness-other-classes/circuit-value-problem/cvp-dec.md)

## Sources

- Yakov Shalunov, "Improved Bounds on the Space Complexity of Circuit Evaluation", CCC (2026), arXiv:2504.20950.
