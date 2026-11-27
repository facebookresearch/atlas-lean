# Quantitative reachability in stochastic timed games is undecidable

No algorithm decides whether a player of a stochastic timed game can reach a target with a probability meeting a given threshold strictly
between $0$ and $1$, already with one player against randomness and four clocks, or with two players, five clocks and a bounded time horizon.

**Stochastic timed games.** A *stochastic timed game* (STG) consists of a [timed automaton](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md) whose locations are partitioned into locations of player $\Box$,
of player $\Diamond$ and of a stochastic player, together with positive integer weights on the edges leaving stochastic locations and, for each state $s$ of a stochastic location, a probability
measure $\mu(s)$ on the set $I(s)$ of delays allowed from $s$, equivalent to Lebesgue measure when $I(s)$ has positive measure. From a stochastic state a delay $t$ is drawn from $\mu(s)$, then an
edge enabled after the delay is chosen with probability proportional to its weight; in the other locations the owning player chooses the delay and the edge. A *$1\tfrac12$-player* STG has no
locations of player $\Box$; a *$2\tfrac12$-player* STG may have both. Given a set $T$ of target locations, an initial state and a threshold $\bowtie p$ with $\bowtie \in \{<, \le, =, \ge, >\}$ and rational $p \in [0, 1]$, the
*reachability problem* asks whether player $\Diamond$ has a strategy such that, against every strategy of player $\Box$, the probability of visiting $T$ satisfies $\bowtie p$; it is *quantitative* when
$0 < p < 1$. In the *time-bounded* version, $T$ must be visited within a given number $\Delta$ of time units.

**Theorem.**

1. The quantitative reachability problem is undecidable for $1\tfrac12$-player STGs with at least $4$ clocks.
2. The time-bounded quantitative reachability problem is undecidable for $2\tfrac12$-player STGs with at least $5$ clocks.

In contrast, quantitative reachability is decidable for initialized $1\tfrac12$-player and $2\tfrac12$-player STGs with a single clock. Item 2 is notable because time-boundedness restores decidability for
several classical problems on timed automata, such as language inclusion.

## Depends on

- [Timed automata over finite timed words](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both proofs simulate two-counter machines, encoding a counter value $c$ by a clock value $1/2^c$. For item 1, player $\Diamond$ simulates the machine and the stochastic player checks the simulation, punishing an
incorrect step by a gadget whose reaching probability departs from the threshold; the reduction is from the non-halting problem, which lets the stochastic player verify the simulation without an
opponent. For item 2, the machine halts exactly when player $\Diamond$ can reach the target locations with probability $1/2$ whatever player $\Box$ does, and the construction keeps the total time
spent below $\Delta = 5$; the reduction is from the halting problem.

## Sources

- S. Akshay, P. Bouyer, S. N. Krishna, L. Manasa and A. Trivedi, "Stochastic timed games revisited", in *41st International Symposium on Mathematical Foundations of Computer Science (MFCS 2016)*, LIPIcs 58, paper 8, 2016, doi:10.4230/LIPIcs.MFCS.2016.8; read in arXiv:1607.05671v1: the summary theorem and the definitions of Section 2 (stochastic timed games, strategies, reachability problems), the undecidability theorems of Section 3 for $1\tfrac12$-player STGs with four clocks and time-bounded $2\tfrac12$-player STGs with five clocks, and the decidability theorem for one clock in Section 4.
