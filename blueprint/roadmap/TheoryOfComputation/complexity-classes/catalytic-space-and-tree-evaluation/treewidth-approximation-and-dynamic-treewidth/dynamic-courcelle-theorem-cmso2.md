# Dynamic Courcelle's theorem: maintaining any fixed CMSO2 property on graphs of bounded treewidth

**CMSO$_2$** is monadic second-order logic over graphs with quantification over vertices, edges, vertex sets and edge sets, extended by modular counting predicates $|X|\equiv a \pmod m$. Courcelle's theorem states that for every fixed CMSO$_2$ sentence $\varphi$ and every $k$, whether a graph of treewidth at most $k$ satisfies $\varphi$ is decidable in time $f(\varphi,k)\cdot n$, by running a tree automaton for $\varphi$ on a tree decomposition. Korhonen, Majewski, Nadara, Pilipczuk and Sokołowski show the dynamic version: for every fixed $k$ and CMSO$_2$ sentence $\varphi$ there is a data structure maintaining a dynamic $n$-vertex graph under edge insertions and deletions, under the promise $\operatorname{tw}(G)\le k$, that after every update reports whether $G\models\varphi$, with amortized update time $O_{k,\varphi}\bigl(2^{\sqrt{\log n}\,\log\log n}\bigr)$. Examples include maintaining Hamiltonicity, 3-colourability, or the existence of a perfect matching on bounded-treewidth dynamic graphs.

## Proof sketch

The tree automaton $\mathcal{A}_\varphi$ is run bottom-up on the maintained decomposition, storing at each node the automaton state of its subtree. Updates change only the rebuilt top part of the decomposition, so states are recomputed only for rebuilt nodes, and the cost per node is bounded in terms of $k$ and $\varphi$; amortized costs follow those of the decomposition maintenance.

## Depends on

- [Monadic second-order logic over words](../../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)
- [Dynamic treewidth data structures under a treewidth promise](dynamic-treewidth-data-structures.md)

## Proof depends on

- [Korhonen–Majewski–Nadara–Pilipczuk–Sokołowski: dynamic treewidth with width 6k+5 and subpolynomial amortized update time](kmnps-dynamic-treewidth.md)

## Sources

- Tuukka Korhonen, Konrad Majewski, Wojciech Nadara, Michał Pilipczuk and Marek Sokołowski, "Dynamic treewidth", FOCS (2023), arXiv:2304.01744.
