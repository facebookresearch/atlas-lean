# Finite-state Nash equilibria with constrained payoff are undecidable

Whether a stochastic multiplayer game has a finite-state Nash equilibrium with constrained payoff is undecidable, even for
simple stochastic multiplayer games with fourteen players, both for randomized and for pure finite-state profiles.

Let FinNE and PureFinNE be the decision problems of
[stochastic multiplayer games and the constrained Nash equilibrium problem](stochastic-multiplayer-games-and-the-constrained.md): given a
finite initialised game $(\mathcal{G}, v_0)$ and rational thresholds $\vec{x}, \vec{y}$, is there a finite-state (for
PureFinNE, a pure finite-state) Nash equilibrium with payoff between $\vec{x}$ and $\vec{y}$? The equilibrium condition still
ranges over all deviations, finite-state or not.

**Theorem.** FinNE and PureFinNE are undecidable, even when restricted to simple stochastic multiplayer games with $14$
players.

The number of players is fixed; everything else is part of the input. For PureFinNE the source lowers the bound to $13$
players. PureFinNE is recursively enumerable, since pure finite-state profiles can be enumerated and each can be checked on a
finite Markov chain and finitely many finite Markov decision processes; the plain problem NE is
[not recursively enumerable](constrained-nash-equilibria-in-simple-stochastic.md).

## Depends on

- [Stochastic multiplayer games and the constrained Nash equilibrium problem](stochastic-multiplayer-games-and-the-constrained.md)

## Proof depends on

- [Constrained Nash equilibria in simple stochastic multiplayer games are not recursively enumerable](constrained-nash-equilibria-in-simple-stochastic.md)
- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter machines, which is recursively enumerable, so this time the reduction
goes from halting rather than from non-halting. It modifies the game of the construction for NE by adding a third counter,
with four more players checking its updates, that must be incremented at every step; it also replaces the gadget of a halting
state and adds a new instruction $\mathrm{halt}$ with its own counter gadget. If the machine does not halt, a Nash
equilibrium in which player $0$ wins almost surely must follow the infinite computation and increment the new counter forever,
which needs infinite memory. If the machine halts, the equilibrium built as for NE can be implemented with finite memory.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in stochastic multiplayer games", *Logical Methods in Computer Science* 7(3), paper 20, 2011, doi:10.2168/LMCS-7(3:20)2011; Theorem 4.14 of the version arXiv:1109.4017v2 with its proof sketch, Remark 4.15 (thirteen players for PureFinNE), and the discussion before Theorem 4.14 (PureFinNE is recursively enumerable).
