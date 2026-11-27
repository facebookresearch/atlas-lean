# Timed reachability games are solved by a backward fixed point

In a [timed game](timed-games.md) with configurations $V$, let $\mathrm{CPre}(X)$ be the set of configurations from which Eve has a legal action (a delay and one
of her enabled edges, or the dummy action when she has none) such that every legal action of Adam leads, by the round semantics of timed games
(the action with the smaller delay is performed, ties going to Adam), to a configuration in $X$. For every target set $G$ that is, in each location,
a finite union of [zones](zones-and-difference-bound-matrices.md) (for instance a set of locations), the increasing sequence $X_0 = G$, $X_{k+1} = X_k \cup \mathrm{CPre}(X_k)$
stabilizes after finitely many steps, and its limit is exactly the set of configurations from which Eve has a strategy to reach $G$. Every $X_k$ is,
in each location, a union of regions for the largest constant of the game and of $G$, and so a finite union of zones; the backward algorithm runs on
unions of DBMs.

The cited operator $\pi(X) = \mathrm{Pred}_{\ge 0}(X \cup \mathrm{Pred}_c(X), \mathrm{Pred}_u(V \setminus X))$ does not compute this set for the round semantics. With one clock,
let Adam's only edge go from $s$ to an absorbing $\mathrm{Win}$ under the guard $x = 0$ and Eve's only edge go from $s$ to an absorbing $\mathrm{Lose}$ under
$x = 1$. From $(s, 0)$ Adam's move at delay $0$ always preempts Eve's, so Eve reaches $\mathrm{Win}$, yet $\pi(\{\mathrm{Win}\}) = \{\mathrm{Win}\}$.

## Depends on

- [Timed games](timed-games.md)
- [Zones and difference-bound matrices](zones-and-difference-bound-matrices.md)

## Proof depends on

- [Region abstraction decides reachability for timed automata](../../../Logic/temporal-logic/timed-and-infinite-state-verification/region-abstraction-decides-reachability-for.md)

## Expansion

This page becomes ready once:

- A source for the fixed point of the one-round controllable predecessor under the round semantics with forced moves of Adam, dummy actions and ties, and for its invariance under regions (proof source; not yet stated)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 11 (N. Markey and O. Sankur, "Timed games"): Section 11.3, the operators $\mathrm{Pred}_{\ge 0}$, $\mathrm{Pred}_c$, $\mathrm{Pred}_u$ and $\pi$ with Lemma 11.1, and Section 11.4, Theorem 11.3 (correctness of the backward algorithm) with its proof sketch via regions.
