# Moore refinement step

Let $M$ be a DFA with state set $S$ and transition function
$\delta$. One round of Moore's refinement sends a set $E \subseteq S \times S$ of pairs of
states to the set of pairs $(p, q) \in S \times S$ such that $p$ is accepting if and only if
$q$ is accepting and, for every letter $a$, the pair $(\delta(p, a), \delta(q, a))$ lies in
$E$.
