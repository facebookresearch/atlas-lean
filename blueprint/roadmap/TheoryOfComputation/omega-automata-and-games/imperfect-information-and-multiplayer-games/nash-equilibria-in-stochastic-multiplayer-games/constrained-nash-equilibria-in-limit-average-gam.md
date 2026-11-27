# Constrained Nash equilibria in limit-average games are not recursively enumerable

Whether a limit-average game has a Nash equilibrium in randomized strategies with payoffs between given thresholds is not
recursively enumerable, even for turn-based terminal-reward games with fourteen players.

**Theorem.** The problem NE of [concurrent limit-average games](concurrent-limit-average-games-and-their-nash-eq.md),
which asks for a Nash equilibrium in randomized strategies with payoff between thresholds $\vec{x}$ and $\vec{y}$, is not
recursively enumerable, even when restricted to turn-based terminal-reward games with $14$ players. In particular it is
undecidable.

The number of players is fixed at $14$. Turn-based games always have a Nash equilibrium, so the hardness comes from the
constraint on the payoff. Restricting to equilibria in pure strategies makes the problem decidable: PureNE is NP-complete, and
the problems for positional and for stationary equilibria are decidable as well (NP-complete and in PSPACE). Since in a
terminal-reward game the limit-average payoff is the reward of the terminal state reached, the result also holds for the
total-reward criterion.

## Depends on

- [Concurrent limit-average games and their Nash equilibria](concurrent-limit-average-games-and-their-nash-eq.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the non-halting problem for deterministic two-counter machines, which is not recursively enumerable. From a
machine $\mathcal{M}$ it computes a turn-based terminal-reward game with players $0$, $1$ and twelve further players. Player $1$
chooses the transitions of $\mathcal{M}$ and player $0$ updates the counters, which are encoded in the probabilities with which
player $0$'s randomized strategy reaches certain terminal states; the game has no chance states, so all randomness comes from the
strategies. Eight players $A_j^t, B_j^t$ ($j \in \{1, 2\}$, $t \in \{0, 1\}$) can quit to a terminal state that pays them $1$
and player $0$ the reward $-1$, and have no reason to do so exactly when counter $j$ is updated neither too high nor too low;
four players $D^t$ and $E_j$ force player $0$'s randomization into a restricted form. The computation of $\mathcal{M}$ is
infinite if and only if the game has a Nash equilibrium in which player $0$ receives expected payoff at least $0$.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in limit-average games", in *CONCUR 2011 – Concurrency Theory*, Lecture Notes in Computer Science 6901, pp. 482–496, Springer, 2011, doi:10.1007/978-3-642-23217-6_32; Section 7 of the version arXiv:1109.6220v1 (the undecidability theorem for randomised strategies with its proof), and the summary of results in Section 1.
