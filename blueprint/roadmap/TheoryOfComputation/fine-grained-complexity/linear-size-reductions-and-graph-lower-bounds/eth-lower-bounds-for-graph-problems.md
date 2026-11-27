# ETH lower bounds for classical graph problems

Assuming ETH, none of Vertex Cover, Dominating Set, Feedback Vertex Set, 3-Colouring and Hamiltonian Cycle admits an algorithm running in time $2^{o(|V|+|E|)}$ on graphs $(V,E)$, and none of Dominating Set, Independent Set, Vertex Cover and Hamiltonian Path admits an algorithm running in time $2^{o(|V|)}$.

## Proof sketch

Compose sparsification (3-SAT has no $2^{o(n+m)}$ algorithm under ETH) with standard reductions from 3-SAT whose output size is linear in $n+m$: the three-occurrence normal form, the gadget reductions to 3-Colouring, Vertex Cover, Dominating Set and Feedback Vertex Set, and the linear reduction to Hamiltonian Cycle; Independent Set is Vertex Cover on the same graph. (Derived.) The same reductions give the $2^{o(|V|+|E|)}$ bound for Independent Set, and the bound for Hamiltonian Cycle transfers to directed Hamiltonian Cycle (replace each edge by two opposite arcs) and to Hamiltonian Path, directed or not (add a twin $v'$ of a vertex $v$ with the same neighbours and pendant vertices at $v$ and $v'$; the graph has a Hamiltonian cycle iff the new graph has a Hamiltonian path), each with linear blow-up. Clique on $G$ is Independent Set on the complement of $G$, which has the same vertex set but possibly quadratically many edges, so Clique has no $2^{o(|V|)}$ algorithm; it is excluded from the $|V|+|E|$ statement because a $k$-clique needs $\binom{k}{2}\le|E|$ edges, so Clique is solvable in time $2^{O(\sqrt{|E|}\log|V|)}=2^{o(|E|)}$.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification lemma](../sparsification-lemma/impagliazzo-paturi-zane-sparsification-lemma.md)
- [ETH holds for sparse 3-SAT iff for general 3-SAT](../sparsification-lemma/eth-for-sparse-3sat.md)
- [Linear-size parsimonious reduction to three occurrences per variable](linear-three-occurrence-reduction.md)
- [A linear-size reduction from 3SAT to Hamiltonian cycle](linear-size-hamiltonian-reduction.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorems 14.4 and 14.6, Observation 14.7.
- Daniel Lokshtanov, Dániel Marx and Saket Saurabh, "Lower Bounds Based on the Exponential Time Hypothesis", Bulletin of the EATCS 105, 2011, Theorems 3.2 and 3.3.
- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
