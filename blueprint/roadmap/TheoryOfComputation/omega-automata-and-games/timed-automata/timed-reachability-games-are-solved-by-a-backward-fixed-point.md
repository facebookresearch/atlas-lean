# Timed reachability games are solved by a backward fixed point

In a [timed game](timed-games.md) with configurations $V$, let $\mathrm{Pred}_{\ge 0}(X, Y)$ be the set of configurations from which $X$ is reached by letting time pass
without meeting $Y$, let $\mathrm{Pred}_c(X)$ and $\mathrm{Pred}_u(X)$ be the predecessors of $X$ by an edge of Eve and of Adam respectively, and define the
*controllable predecessor* operator $\pi(X) = \mathrm{Pred}_{\ge 0}(X \cup \mathrm{Pred}_c(X),\ \mathrm{Pred}_u(V \setminus X))$, which is monotone. For every target set $G$ that is, in each location, a finite union of
zones (for instance a set of locations), the sequence $\pi^k(G)$ stabilizes after finitely many steps, and its limit is exactly the set of configurations from which Eve has a strategy to reach $G$. Every
iterate is a finite union of [zones](zones-and-difference-bound-matrices.md) in each location, so the backward algorithm runs on unions of DBMs; termination
follows because the iterates are unions of regions for the largest constant of the game and of $G$.

## Depends on

- [Timed games](timed-games.md)
- [Zones and difference-bound matrices](zones-and-difference-bound-matrices.md)

## Proof depends on

- [Region abstraction decides reachability for timed automata](../../../Logic/temporal-logic/timed-and-infinite-state-verification/region-abstraction-decides-reachability-for.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 11 (N. Markey and O. Sankur, "Timed games"): Section 11.3, the operators $\mathrm{Pred}_{\ge 0}$, $\mathrm{Pred}_c$, $\mathrm{Pred}_u$ and $\pi$ with Lemma 11.1, and Section 11.4, Theorem 11.3 (correctness of the backward algorithm) with its proof sketch via regions.
