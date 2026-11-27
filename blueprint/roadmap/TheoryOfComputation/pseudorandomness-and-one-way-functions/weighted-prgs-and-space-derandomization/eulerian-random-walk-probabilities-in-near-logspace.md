# Ahmadinejad–Kelner–Murtagh–Peebles–Sidford–Vadhan: Eulerian random-walk probabilities in deterministic space Õ(log N)

There is a deterministic algorithm using space $\widetilde{O}(\log N)$, where $N$ is the input length, that given an undirected graph or, more generally, an Eulerian directed graph $G$, vertices $u,v$ and a length $t\le\mathrm{poly}(N)$, outputs the probability that a $t$-step random walk from $u$ ends at $v$ within additive error $\varepsilon=1/\mathrm{poly}(N)$. Previously the best bounds for this problem, even for undirected graphs, were randomized space $O(\log N)$ (Aleliunas et al.) and deterministic space $O(\log^{3/2}N)$ (Saks–Zhou), both valid for arbitrary digraphs. The algorithm also improves on both for non-Eulerian digraphs when $\varepsilon=1/N^{\omega(1)}$, and it inverts Eulerian Laplacian matrices deterministically in space $\widetilde{O}(\log N)$.

## Proof sketch

Powering the random-walk matrix is reduced to inverting Eulerian Laplacians of cycle-lifted graphs, whose adjacency matrix is the tensor product of the original one with a directed cycle. A notion of spectral approximation for Eulerian graphs preserved under powering lets a derandomized-squaring sequence serve as a preconditioner, and the inverse is computed in $\widetilde{O}(\log N)$ space by a recursive preconditioned Richardson iteration, building on the undirected space-efficient Laplacian solver of Murtagh et al.

## Depends on

- [Probability of an event for a random walk on a regular graph](../../../GraphTheory/graph-families-and-operations/expander-graphs/walk-prob.md)

## Proof depends on

- [Spectral approximation of graphs](../../../ComputerScience/graph-algorithms/graph-algorithm-bounds/spectral-approximation-of-graphs.md)

## Sources

- AmirMahdi Ahmadinejad, Jonathan Kelner, Jack Murtagh, John Peebles, Aaron Sidford and Salil Vadhan, "High-precision Estimation of Random Walks in Small Space", FOCS (2020), arXiv:1912.04524.
- Lijie Chen, William M. Hoza, Xin Lyu, Avishay Tal and Hongxun Wu, "Weighted Pseudorandom Generators via Inverse Analysis of Random Walks and Shortcutting", FOCS (2023), ECCC TR23-114.
