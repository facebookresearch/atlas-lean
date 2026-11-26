# Korhonen–Majewski–Nadara–Pilipczuk–Sokołowski: dynamic treewidth with width 6k+5 and subpolynomial amortized update time

For every fixed $k$ there is a dynamic treewidth data structure that, for a dynamic $n$-vertex graph $G$ updated by edge insertions and deletions under the promise $\operatorname{tw}(G)\le k$, maintains a tree decomposition of $G$ of width at most $6k+5$ with amortized update time

$$
O_k\bigl(2^{\sqrt{\log n}\,\log\log n}\bigr),
$$

where $O_k$ hides factors depending only on $k$; in particular the update time is $n^{o(1)}$.

## Proof sketch

The decomposition is kept "prefix-rebuildable": an update affects a top part of the decomposition, which is rebuilt using a static refinement procedure (in the spirit of Korhonen's 2-approximation) that improves a given decomposition locally, while a recursive height-reduction mechanism controls the depth of the decomposition; the balance between rebuild cost and depth produces the $2^{\sqrt{\log n}\log\log n}$ amortized bound.

## Depends on

- [Dynamic treewidth data structures under a treewidth promise](dynamic-treewidth-data-structures.md)

## Proof depends on

- [Korhonen: a single-exponential time 2-approximation for treewidth](korhonen-2-approximation-treewidth.md)

## Sources

- Tuukka Korhonen, Konrad Majewski, Wojciech Nadara, Michał Pilipczuk and Marek Sokołowski, "Dynamic treewidth", FOCS (2023), arXiv:2304.01744.
