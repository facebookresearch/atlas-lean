# Progress measures give winning strategies in parity games

Let $G$ be a finite parity game with priorities in $\{0, \dots, d\}$, where player Even wins an infinite play when the largest priority occurring infinitely often is even. For each odd priority $i$ let $n_i$ be the number of positions of priority $i$, and let $M_G$ be the set of tuples $(m_i)_{i \text{ odd}}$ with $0 \le m_i \le n_i$, together with a top element $\top$. For a priority $p$, the truncation $x|_p$ of a tuple keeps the components with index at least $p$, and truncated tuples are compared lexicographically starting from the largest index; $\top$ is above every tuple. A *game parity progress measure* is a map $\rho$ from positions to $M_G$ such that every position of Even has some successor $w$, and every position of Odd has all successors $w$, along which $\rho$ *progresses* from $v$: $\rho(v)|_{p(v)} \ge \rho(w)|_{p(v)}$, strictly if $p(v)$ is odd, unless $\rho(v) = \top$.

If $\rho$ is a game parity progress measure, then choosing at every position $v$ of Even with $\rho(v) \ne \top$ a successor along which $\rho$ progresses defines a positional strategy for Even that wins from every position $v$ with $\rho(v) \ne \top$.

These are Jurdziński's progress measures with the order of priorities reversed: replacing each priority $p$ by $D - p$ for an even $D \ge d$ turns the least-priority condition of the source into the largest-priority condition used here.

## Depends on

- [Parity game](parity-game.md)

## Proof depends on

- [Reversing priorities exchanges the min-parity and max-parity conditions](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, Corollary 7
