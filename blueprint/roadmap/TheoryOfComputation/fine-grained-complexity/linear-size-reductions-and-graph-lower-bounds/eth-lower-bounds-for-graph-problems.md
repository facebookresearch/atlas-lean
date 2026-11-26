# ETH and SH lower bounds for classical graph problems

Assuming ETH, none of 3-Colouring, Independent Set, Vertex Cover, and directed or undirected Hamiltonian Path and Cycle is decidable in time $2^{o(|V|+|E|)}$, and Clique has no $2^{o(|V|)}$ algorithm (Clique is solvable in $2^{O(\sqrt{|E|}\log|V|)}$ time, so it is excluded from the $|V|+|E|$ and SH statements); moreover Independent Set, Clique and 3-Colouring have no $2^{o(|V|)}$ algorithm. Assuming the Satisfiability Hypothesis, none of these problems admits an algorithm with a fixed power saving, i.e. in time $2^{O((|V|+|E|)^{p})}$ for some $p<1$.

## Proof sketch

Compose sparsification (which makes the number of clauses linear in the number of variables) with the standard reductions from 3SAT, all of which have size linear in the number of variables plus clauses: the three-occurrence normal form, the gadget reductions to 3-colouring and independent set, complements for clique and vertex cover, and the sparse Hamiltonian reduction.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [The Satisfiability Hypothesis (SH) and its counting version](../sat-exponents-and-hypotheses/satisfiability-hypothesis.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification lemma](../sparsification-lemma/impagliazzo-paturi-zane-sparsification-lemma.md)
- [ETH holds for sparse 3-SAT iff for general 3-SAT](../sparsification-lemma/eth-for-sparse-3sat.md)
- [Linear-size parsimonious reduction to three occurrences per variable](linear-three-occurrence-reduction.md)
- [A linear-size reduction from 3SAT to Hamiltonian path and cycle](linear-size-hamiltonian-reduction.md)
- [Exponent transfer under the Satisfiability Hypothesis](../sat-exponents-and-hypotheses/sh-exponent-transfer.md)

## Sources

- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015.
- MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2, 2026.
