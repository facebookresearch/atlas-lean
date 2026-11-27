# Dynamic graph problems

A *dynamic graph problem* fixes three things:
- a class of initial graphs $G = (V, E)$ with $n = |V|$ and $m = |E|$;
- a set of *updates*, such as inserting or deleting an edge, or switching a vertex on or off;
- a set of *queries*, such as whether $u$ and $v$ are connected, or the distance from $s$ to $t$.

An algorithm first *preprocesses* the initial graph. It then processes an online sequence of updates and queries, answering each query before it sees the next operation. Each query is answered with respect to the graph obtained by applying all updates so far.

The algorithm has three costs, measured as functions of $m$ and $n$ in the [word-RAM model](the-word-ram-model.md):
- *preprocessing time* $p(m, n)$;
- *update time* $u(m, n)$;
- *query time* $q(m, n)$.

These times are *worst-case* if every single operation obeys the bound. They are *amortized* if, for every $k$, the first $k$ updates, or the first $k$ queries, take total time at most $k$ times the bound. A problem is *fully dynamic* if updates can both add and remove, and *partially dynamic*, either incremental or decremental, otherwise. Randomized algorithms answer each query correctly with probability at least $2/3$, for example.

For example, in *subgraph connectivity* the graph $G$ is fixed, and the algorithm maintains a set $S \subseteq V$ of switched-on vertices:
- updates add a vertex to $S$ or remove one from it;
- a query asks whether $s$ and $t$ are connected in the subgraph induced by $S$.

The *$s$-$t$* version fixes the two query vertices in advance.

## Depends on

- [The word-RAM model](the-word-ram-model.md)

## Sources

- M. Henzinger, S. Krinninger, D. Nanongkai and T. Saranurak, "Unifying and strengthening hardness for dynamic problems via the online matrix-vector multiplication conjecture", *Proceedings of the 47th ACM STOC*, 2015, arXiv:1511.06773, <https://arxiv.org/abs/1511.06773>, Section 1: dynamic problems with preprocessing, update and query time, amortized versus worst-case bounds, the definition of subgraph connectivity (after Frigioni and Italiano), and the summary table with $p(m, n)$, $u(m, n)$ and $q(m, n)$.
