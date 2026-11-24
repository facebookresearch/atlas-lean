# Disjoint-box cap hypothesis for multi-open events

For $d \in \mathbb{N}$ and $0 < p < 1$, the cap hypothesis holds when for every finite family $\mathcal{P}$ of finite sets of unordered pairs of sites and every $N \in \mathbb{N}$ there are $g \in \mathbb{Z}^d$ and $r \in \mathbb{N}$ such that, with $M = N + r$, for all $T, T' \in \mathcal{P}$ there exist a set $F$ and sets $t_T, t_{T'}$ of pairs of vertices of $\Lambda_M$ and a graph $C'$ on $\Lambda_M$ containing the clique on $\partial\Lambda_M$, with:

- $T = t_T$ and $T' - g = t_{T'}$ as sets of pairs of sites, and no pair of $t_{T'}$ lies in $F$;
- for every configuration $\psi$ of $\Lambda_M$ closed on $F$, the probability that every pair of $t_T$ is open under the [conditional measure](../fkg-inequality-and-monotonicity-of-random-cluste/cond-bc-prob.md) of the random-cluster measure on $\Lambda_M$ with boundary wiring $C'$ at $(p, 2)$ given agreement with $\psi$ off $F$ is at most $\phi^1_N(O_T)$;
- $\phi^1_M(O_{t_{T'}}) \le \phi^1_N(O_{T'})$.

Here $\Lambda_k = \{-k, \dots, k\}^d$, $\partial\Lambda_k = \Lambda_k \setminus \Lambda_{k-1}$, $\phi^1_k$ is the [wired box measure](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-finite-measure.md) on $\Lambda_k$ at $(p, 2)$, and $O_s$ is the event that every pair of the finite set $s$ is open.
