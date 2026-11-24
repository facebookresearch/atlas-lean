# Small progress measures

Let $G$ be a finite parity game with priorities in $\{0, \dots, d - 1\}$ for some $d \ge 2$, where, after the standard compression that closes gaps and merges consecutive used priorities of the same parity without changing the winner of any play, every value in $\{0, \dots, d - 1\}$ occurs, so that $d$ is at most the number of positions, where player Even wins an infinite play when the largest priority occurring infinitely often is even. For each odd priority $i$ let $n_i$ be the number of positions of priority $i$, and let $M_G$ be the set of tuples $(m_i)_{i \text{ odd}}$ with $0 \le m_i \le n_i$, together with a top element $\top$. For a priority $p$, the truncation $x|_p$ of a tuple keeps the components with index at least $p$, and truncated tuples are compared lexicographically starting from the largest index; $\top$ is above every tuple. A *game parity progress measure* is a map $\rho$ from positions to $M_G$ such that every position of Even has some successor $w$, and every position of Odd has all successors $w$, along which $\rho$ *progresses* from $v$: $\rho(v)|_{p(v)} \ge \rho(w)|_{p(v)}$, strictly if $p(v)$ is odd, unless $\rho(v) = \top$.

Every finite parity game has a least game parity progress measure $\rho^*$, the least simultaneous fixed point of monotone lift operators, and the positions $v$ with $\rho^*(v) \ne \top$ are exactly Even's winning region. The least measure is computed by iterating lifts in time $O(d\, m\, (n/\lfloor d/2\rfloor)^{\lfloor d/2\rfloor})$ for a game with $n$ positions and $m$ edges, and a positional winning strategy for Even is obtained by choosing a successor witnessing progress.

These are Jurdziński's progress measures with the order of priorities reversed: replacing each priority $p$ by $D - p$, where $D$ is whichever of $d - 1$ and $d$ is even, turns the least-priority condition of the source into the largest-priority condition used here and keeps the number $\lfloor d/2 \rfloor$ of odd priorities.

## Depends on

- [Parity game](parity-game.md)
- [Winning region of a parity game](winning-region.md)

## Proof depends on

- [Finite parity games are positionally determined](finite-parity-games-are-positionally-determined.md)
- [Progress measures give winning strategies in parity games](progress-measures-give-winning-strategies-in.md)
- [Reversing priorities exchanges the min-parity and max-parity conditions](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md)

## Expansion

This page becomes ready once:

- Winner-preserving compression of parity-game priorities, which closes gaps and merges consecutive used priorities of equal parity so that $d$ is at most the number of positions (statement prerequisite; not yet stated)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000
