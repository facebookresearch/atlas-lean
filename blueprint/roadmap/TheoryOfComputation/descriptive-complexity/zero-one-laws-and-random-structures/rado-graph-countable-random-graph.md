# The Rado graph is the countable random graph

The *Rado graph* $\mathcal{R}$ on $\mathbb{N}$, with $i < j$ adjacent iff the $i$-th binary digit of $j$ is $1$, satisfies every extension axiom, so it is a model of $T_{\mathrm{rg}}$ and, by $\aleph_0$-categoricity, every countable graph satisfying all extension axioms is isomorphic to it. Every countable graph embeds as an induced subgraph of $\mathcal{R}$, and the complement of $\mathcal{R}$ is isomorphic to $\mathcal{R}$.

## Proof sketch

Given finite disjoint sets $U$ (to be adjacent) and $W$ (non-adjacent), the number $z = \sum_{u \in U} 2^u + 2^{N}$ with $N$ larger than all elements realizes the pattern. The complement also satisfies all extension axioms; embedding is by the forth half of back-and-forth.

## Depends on

- [Extension axioms and the theory of the random graph](extension-axioms-random-graph.md)

## Proof depends on

- [The theory of the random graph is $\aleph_0$-categorical and complete](random-graph-theory-categorical-and-complete.md)

## Sources

- R. Rado, "Universal Graphs and Universal Functions", Acta Arithmetica 9, 331–340, 1964.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
