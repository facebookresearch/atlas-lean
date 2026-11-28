# Quantitative reachability in stochastic timed games is undecidable

No algorithm decides whether a player of a stochastic timed game can reach a target with a probability meeting a given threshold strictly
between $0$ and $1$, already with one player against randomness and four clocks, or with two players, five clocks and a bounded time horizon.

**Stochastic timed games.** A *stochastic timed game* (STG) consists of a [timed automaton](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md) whose locations are partitioned into locations of player $\Box$,
of player $\Diamond$ and of a stochastic player, together with positive integer weights on the edges leaving stochastic locations and, for each state $s$ of a stochastic location, a probability
measure $\mu(s)$ on the set $I(s)$ of delays allowed from $s$, equivalent to Lebesgue measure when $I(s)$ has positive measure. From a stochastic state a delay $t$ is drawn from $\mu(s)$, then an
edge enabled after the delay is chosen with probability proportional to its weight; in the other locations the owning player chooses the delay and the edge. As in the source, strategies are *deterministic*: a strategy maps each finite run ending in a location of its player to a delay and an edge, and strategy profiles must be measurable (for every sequence of edges and state, the map from the delays of a run to the chosen move is measurable). A *$1\tfrac12$-player* STG has no
locations of player $\Box$; a *$2\tfrac12$-player* STG may have both. Given a set $T$ of target locations, an initial state and a threshold $\bowtie p$ with $\bowtie \in \{<, \le, =, \ge, >\}$ and rational $p \in [0, 1]$, the
*reachability problem* asks whether player $\Diamond$ has a strategy such that, against every strategy of player $\Box$, the probability of visiting $T$ satisfies $\bowtie p$; it is *quantitative* when
$0 < p < 1$. In the *time-bounded* version, $T$ must be visited within a given number $\Delta$ of time units.

**Theorem.**

1. The quantitative reachability problem is undecidable for $1\tfrac12$-player STGs with at least $4$ clocks.
2. The time-bounded quantitative reachability problem is undecidable for $2\tfrac12$-player STGs with at least $5$ clocks.

(Theorems 3 and 6 of the source.) Both hold for finite instances: in the reductions every stochastic state has a bounded set $I(s)$ of allowed delays and draws its delay from the uniform distribution on it, so an instance is given by the timed automaton with integer constants, the integer weights and the threshold $p = 1/2$.

In contrast, quantitative reachability is decidable for $1\tfrac12$-player and $2\tfrac12$-player STGs with a single clock under the source's hypotheses: the underlying timed automaton is structurally non-Zeno, delays in stochastic locations are exponentially distributed with rates depending only on the location, and the game is initialized. Item 2 is notable because time-boundedness restores decidability for
several classical problems on timed automata, such as language inclusion.

## Depends on

- [Timed automata over finite timed words](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both proofs simulate two-counter machines, encoding a counter value $c$ by a clock value $1/2^c$. For item 1, player $\Diamond$ simulates the machine and the stochastic player checks the simulation, punishing an
incorrect step by a gadget whose reaching probability departs from the threshold; the reduction is from the non-halting problem, which lets the stochastic player verify the simulation without an
opponent. For item 2, the machine halts exactly when player $\Diamond$ can reach the target locations with probability $1/2$ whatever player $\Box$ does, and the construction keeps the total time
spent below $\Delta = 5$; the reduction is from the halting problem.

## Sources

- S. Akshay, P. Bouyer, S. N. Krishna, L. Manasa and A. Trivedi, "Stochastic timed games revisited", in *41st International Symposium on Mathematical Foundations of Computer Science (MFCS 2016)*, LIPIcs 58, paper 8, 2016, doi:10.4230/LIPIcs.MFCS.2016.8; read in arXiv:1607.05671v1: Theorem 2 and Definition 1 in Section 2 (stochastic timed games, strategies, reachability problems), Theorem 3 (Section 3.1, $1\tfrac12$-player STGs with four clocks) and Theorem 6 (Section 3.2, time-bounded $2\tfrac12$-player STGs with five clocks), and Theorem 8 and Corollary 9 for one clock under the hypotheses $(\star)$ of Section 4, with the numbering of that version.
