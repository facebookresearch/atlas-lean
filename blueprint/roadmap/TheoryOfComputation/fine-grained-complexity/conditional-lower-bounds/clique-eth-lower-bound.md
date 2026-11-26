# Under ETH, Clique has no f(k)·n^{o(k)} algorithm

Assuming ETH, there is no algorithm deciding whether an $N$-vertex graph has a clique of size $k$ in time $f(k)\cdot N^{o(k)}$ for any computable (indeed any) function $f$; in particular Clique is not fixed-parameter tractable under ETH.

## Proof sketch

Clause grouping: split the $m$ clauses of a 3-CNF into $k$ groups of $m/k$ clauses; the vertices of group $i$ are the $\le 2^{3m/k}$ partial assignments satisfying that group, and edges join consistent assignments. A $k$-clique is exactly a satisfying assignment. With $N\le k2^{3m/k}$, an $f(k)N^{o(k)}$ algorithm gives $2^{o(m)}$ time for 3-SAT for slowly growing $k$, contradicting ETH via sparsification.

## Depends on

- [Parameterized Clique](../../complexity-classes/parameterized-complexity/clique-param.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [Fixed-parameter tractable problems](../../complexity-classes/parameterized-complexity/fpt.md)

## Proof depends on

- [ETH holds for sparse 3-SAT iff for general 3-SAT](../sparsification-lemma/eth-for-sparse-3sat.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorem 14.21.
