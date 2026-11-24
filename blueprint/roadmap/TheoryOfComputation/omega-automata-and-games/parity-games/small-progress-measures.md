# Small progress measures

Let $G$ be a finite parity game with priorities in $\{0, \dots, d\}$, where player Even wins an infinite play when the largest priority occurring infinitely often is even. For each odd priority $i$ let $n_i$ be the number of positions of priority $i$, and let $M_G$ be the set of tuples $(m_i)_{i \text{ odd}}$ with $0 \le m_i \le n_i$, together with a top element $\top$. For a priority $p$, the truncation $x|_p$ of a tuple keeps the components with index at least $p$, and truncated tuples are compared lexicographically starting from the largest index; $\top$ is above every tuple. A *game parity progress measure* is a map $\rho$ from positions to $M_G$ such that every position of Even has some successor $w$, and every position of Odd has all successors $w$, along which $\rho$ *progresses* from $v$: $\rho(v)|_{p(v)} \ge \rho(w)|_{p(v)}$, strictly if $p(v)$ is odd, unless $\rho(v) = \top$.

Every finite parity game has a least game parity progress measure $\rho^*$, the least simultaneous fixed point of monotone lift operators, and the positions $v$ with $\rho^*(v) \ne \top$ are exactly Even's winning region. The least measure is computed by iterating lifts in time $O(d\, m\, (n/\lfloor d/2\rfloor)^{\lfloor d/2\rfloor})$ for a game with $n$ positions and $m$ edges, and a positional winning strategy for Even is obtained by choosing a successor witnessing progress.

These are Jurdziński's progress measures with the order of priorities reversed: replacing each priority $p$ by $D - p$ for an even $D \ge d$ turns the least-priority condition of the source into the largest-priority condition used here.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Positional determinacy of finite parity games.
- Proof prerequisite: Min-parity to max-parity transport.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000
