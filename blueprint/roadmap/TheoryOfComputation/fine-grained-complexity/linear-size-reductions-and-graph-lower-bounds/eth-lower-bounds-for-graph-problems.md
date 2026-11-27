# ETH lower bounds for classical graph problems

Assuming ETH, none of 3-Colouring, Independent Set, Vertex Cover, Dominating Set, Feedback Vertex Set, and directed or undirected Hamiltonian Path and Cycle is decidable in time $2^{o(|V|+|E|)}$ on graphs $(V,E)$, and Clique has no $2^{o(|V|)}$ algorithm. (Clique is excluded from the $|V|+|E|$ statement: a $k$-clique needs $\binom{k}{2}\le|E|$ edges, so Clique is solvable in time $2^{O(\sqrt{|E|}\log|V|)}=2^{o(|E|)}$.)

## Proof sketch

Compose sparsification (3-SAT has no $2^{o(n+m)}$ algorithm under ETH) with standard reductions from 3-SAT whose output size is linear in $n+m$: the three-occurrence normal form, the gadget reductions to 3-Colouring, Vertex Cover, Dominating Set, Feedback Vertex Set, and the sparse Hamiltonian reduction; Independent Set is Vertex Cover on the same graph. Clique on $G$ is Independent Set on the complement of $G$, which has the same vertex set but possibly quadratically many edges, so only the $2^{o(|V|)}$ bound transfers.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification lemma](../sparsification-lemma/impagliazzo-paturi-zane-sparsification-lemma.md)
- [ETH holds for sparse 3-SAT iff for general 3-SAT](../sparsification-lemma/eth-for-sparse-3sat.md)
- [Linear-size parsimonious reduction to three occurrences per variable](linear-three-occurrence-reduction.md)
- [A linear-size reduction from 3SAT to Hamiltonian path and cycle](linear-size-hamiltonian-reduction.md)

## Sources

- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorems 14.4 and 14.6, Observation 14.7.
