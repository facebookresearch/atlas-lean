# Conditional product cap for multi-open events in boxes

For $d \in \mathbb{N}$ and $0 < p < 1$, the conditional product cap holds when for every finite family $\mathcal{P}$ of finite sets of unordered pairs of sites and every $N \in \mathbb{N}$ there is $g \in \mathbb{Z}^d$ such that for all sufficiently large $m$ and all $T, T' \in \mathcal{P}$ there exist a set $F$ of pairs of vertices of $\Lambda_m$, sets $S_A, S_B$ of configurations of $\Lambda_m$ and a graph $C'$ on $\Lambda_m$ containing the clique on $\partial\Lambda_m$, with:

- $O_T \cap \tau_g^{-1}(O_{T'})$ equals the cylinder event of $S_A \cap S_B$ on $\Lambda_m$, and the cylinder events of $S_A \cap S_B$ and of $S_B$ are measurable;
- $S_A$ is increasing and $S_B$ depends only on the pairs outside $F$;
- $\phi^1_N(O_T) \ge 0$, and for every configuration $\psi$ of $\Lambda_m$ closed on $F$, the mass of $S_A$ under the [conditional measure](../fkg-inequality-and-monotonicity-of-random-cluste/cond-bc-prob.md) of the random-cluster measure on $\Lambda_m$ with boundary wiring $C'$ at $(p, 2)$ given agreement with $\psi$ off $F$ is at most $\phi^1_N(O_T)$;
- $\phi^1_m(\text{cylinder of } S_B) \le \phi^1_N(O_{T'})$.

Here $\Lambda_k = \{-k, \dots, k\}^d$, $\partial\Lambda_k = \Lambda_k \setminus \Lambda_{k-1}$, $\phi^1_k$ is the [wired box measure](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-finite-measure.md) on $\Lambda_k$ at $(p, 2)$, $O_s$ is the event that every pair of the finite set $s$ is open, and $\mathbb{Z}^d$ acts on configurations by $(\tau_g\omega)(e) = \omega(e - g)$, where $e - g$ is the pair $e$ translated by $-g$.
