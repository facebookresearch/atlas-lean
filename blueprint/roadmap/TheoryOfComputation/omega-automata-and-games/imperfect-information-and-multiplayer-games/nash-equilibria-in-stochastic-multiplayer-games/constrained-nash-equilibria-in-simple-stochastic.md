# Constrained Nash equilibria in simple stochastic multiplayer games are not recursively enumerable

The existence of a Nash equilibrium with constrained payoff in a stochastic multiplayer game is not recursively enumerable,
even for simple stochastic multiplayer games with ten players, both for arbitrary and for pure strategy profiles.

Let NE and PureNE be the decision problems of
[stochastic multiplayer games and the constrained Nash equilibrium problem](stochastic-multiplayer-games-and-the-constrained.md): given a
finite initialised game $(\mathcal{G}, v_0)$ and rational thresholds $\vec{x}, \vec{y}$, is there a Nash equilibrium (for
PureNE, a pure Nash equilibrium) with payoff between $\vec{x}$ and $\vec{y}$?

**Theorem.** NE and PureNE are not recursively enumerable, even when restricted to simple stochastic multiplayer games with
$10$ players. In particular both problems are undecidable.

The number of players is fixed at $10$; the arena, the transition probabilities and the thresholds vary. The lower bound holds
already for the qualitative variant, which asks for a Nash equilibrium in which player $0$ wins almost surely. For PureNE the
source strengthens the bound to $9$ players, by merging two players of the construction.

By contrast, the problems for positional and for stationary profiles are decidable (in NP and in PSPACE,
respectively), and PureFinNE is recursively enumerable.

## Depends on

- [Stochastic multiplayer games and the constrained Nash equilibrium problem](stochastic-multiplayer-games-and-the-constrained.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the non-halting problem for deterministic two-counter machines, which is not recursively enumerable. From a
machine $\mathcal{M}$ it computes a $10$-player SSMG $(\mathcal{G}, v_0)$ with players $0$ and $1$ and eight players
$A_j^t, B_j^t$ ($j \in \{1, 2\}$, $t \in \{0, 1\}$). Player $1$ chooses the transitions of $\mathcal{M}$ and player $0$
updates the counters, which are stored as probabilities: in the $n$-th simulated step, counter $j$ with value $c$ corresponds
to probability $1/2^{c}$ of reaching certain vertices of a counter gadget. In each step the players $A_j^t$ and $B_j^t$ may quit
for a fixed payoff ($\frac{1}{3}$ and $\frac{1}{6}$), which gives players $0$ and $1$ nothing; they have no reason to quit
exactly when counter $j$ has been updated neither too high nor too low. Hence in a Nash equilibrium where player $0$ wins almost
surely the play follows the computation of $\mathcal{M}$ forever, and such an equilibrium, which can be taken pure, exists if
and only if the computation of $\mathcal{M}$ is infinite.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in stochastic multiplayer games", *Logical Methods in Computer Science* 7(3), paper 20, 2011, doi:10.2168/LMCS-7(3:20)2011; Theorem 4.9 of the version arXiv:1109.4017v2 with its proof, Lemma 4.10, Remark 4.11 (nine players for PureNE), and Theorems 4.3 and 4.5 (positional and stationary equilibria).
