# Freezing, bounded-change and convergent cellular automata

Freezing, bounded-change and convergent cellular automata form three nested classes, defined by an order on states that cell updates never increase, by a uniform bound on the number of state changes of a cell, and by convergence of every orbit.

Let $F:Q^{\mathbb Z^d}\to Q^{\mathbb Z^d}$ be a [cellular automaton](../cellular-automata-on-z-d.md) with finite state set $Q$, neighborhood $V$ and local rule $f$.
- $F$ is *freezing* if there is a partial order $\le$ on $Q$ with $F(c)_z\le c_z$ for every configuration $c$ and cell $z$.
- $F$ is *$k$-change* if for every configuration $c$ and cell $z$ the set $\{t\in\mathbb N: F^{t+1}(c)_z\neq F^t(c)_z\}$ has at most $k$ elements, and *bounded-change* if it is $k$-change for some $k$.
- $F$ is *convergent* if for every configuration $c$ the sequence $(F^t(c))_{t\in\mathbb N}$ has a limit in the product (Cantor) topology; its limit is written $F^\omega(c)$, and the *freezing time* $\tau(c,z)$ of cell $z$ is the first time after which $z$ never changes.
- $F$ is *nilpotent* if some power $F^t$, $t>0$, is constant.

A freezing automaton with $n$ states is $(n-1)$-change, nilpotent automata are bounded-change, and bounded-change automata are convergent; both inclusions are strict. Whether an automaton is freezing is decidable in time $O(n^{|V|})$.

**Canonical problems.** For a *bounded configuration* $u\in Q^{\mathcal B(n)}$, where $\mathcal B(n)$ is the ball of radius $n$ for the maximum norm, the *cylinder* $[u]$ is the set of configurations agreeing with $u$ on $\mathcal B(n)$. The *cylinder reachability problem* $\mathrm{CYREACH}_F$ asks, given bounded configurations $u,v$, whether $F^t(c)\in[v]$ for some $c\in[u]$ and $t\in\mathbb N$. For convergent $F$, the *limit value problem* $\mathrm{LIMIT}_F$ maps a computable configuration $c$, given by a Turing machine, to $F^\omega(c)_0$, and the *freezing time problem* $\mathrm{TIME}_F$ maps it to $\tau(c,0)$.

## Depends on

- [Cellular automata on ℤ^d](../cellular-automata-on-z-d.md)

## Proof depends on

None.

## Expansion

Examples of freezing automata include Ulam's crystal-growth rule, bootstrap percolation, forest-fire models and Life without Death. A convergent automaton that is not nilpotent has at least two distinct fixed points. Prediction of a cell after $t$ steps is in NLOGSPACE for one-dimensional bounded-change automata.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for theorems, propositions and corollaries): the formal setting of Section 1, Definitions 1–3, Fact 1, the nilpotency definition and the strict hierarchy (Fact 2) in Section 2, Definitions 4–5 (prediction and cylinder reachability), Definition 7 (limit value and freezing time), Proposition 1 (two fixed points) and Proposition 6 (prediction in NLOGSPACE).
