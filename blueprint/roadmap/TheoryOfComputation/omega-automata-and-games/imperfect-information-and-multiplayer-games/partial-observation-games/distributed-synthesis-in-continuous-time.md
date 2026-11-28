# Distributed synthesis in continuous time is undecidable

For parallel compositions of interactive Markov chains, each controlled by a player who sees only its own module's timed history, no algorithm decides whether the players can jointly reach a target with a given probability (two players) or almost surely (three players); almost-sure reachability is undecidable already for two-player decentralized POMDPs.

A *distributed IMC* is a parallel composition of $n$ modules, each an interactive Markov chain with private actions, synchronization actions and delay transitions, each labeled by the rate $\lambda > 0$ of an exponentially distributed delay (the source restricts to exponential delays, rates given as rationals); modules synchronize by CSP-style handshake on shared actions. It is a game with $n+1$ players: player $i\le n$ controls module $i$ based only on its local timed history, and a scheduler resolves the interleaving. For a target set $T$ and a rational $p\in[0,1]$, the *existence problem* asks whether some strategy profile reaches $T$ (and stays there for positive time) with probability $\ge p$ against every scheduler, and the *value problem* whether $\sup_\sigma\inf_\delta\Pr^{\sigma,\delta}(\Diamond T)\ge p$; the problems are *qualitative* for $p=1$ and *quantitative* in general. A *decentralized POMDP* (DEC-POMDP) is a discrete-time POMDP controlled by $n$ players who each receive their own observations and choose actions jointly.

**Theorem.** For distributed IMCs, the qualitative value, quantitative value and quantitative existence problems are undecidable with $n\ge2$ players, and the qualitative existence problem is EXPTIME-hard with $2$ players and undecidable with $n\ge3$ players (Theorem 2 of the source).

The source derives part of this from a result on discrete time: it is undecidable whether a DEC-POMDP with $n\ge2$ players has a strategy profile reaching a set of target states with probability $1$ (Theorem 3).

Almost-sure reachability (qualitative existence) is decidable for POMDPs (one player), and for *non-urgent* distributed IMCs with two players and synchronization-state targets the quantitative value problem is decidable in EXPTIME.

## Depends on

- [Decentralized POMDPs and joint-policy evaluation](../../../../ComputerScience/heuristic-search-and-planning/partially-observable-planning/decentralized-pomdps-and-joint-policy-evaluation.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [The emptiness problem for probabilistic automata is undecidable](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)
- [The value-1 problem for probabilistic automata is undecidable](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Expansion

Theorem 3 reduces non-halting of a deterministic Turing machine on the blank tape: in a two-player DEC-POMDP each player receives a single black observation with probability $1$, at the same time or one step apart, and three modules then check that the action sequences of the two players encode the initial configuration, coincide, or encode a non-accepting configuration followed by its successor; almost-sure reachability forces both players to write the run of the machine forever. A DEC-POMDP with $n$ players reduces in polynomial time to reachability in a distributed IMC with $n+1$ players, preserving the probability of reaching the target, which gives the three-player qualitative result. The remaining two-player results follow from the corresponding undecidability results for POMDPs (Paz; Bertoni, Mauri and Torelli; Gimbert and Oualhadj), as one-player DEC-POMDPs.

## Sources

- Holger Hermanns, Jan Krčál and Steen Vester, "Distributed Synthesis in Continuous Time", in *Foundations of Software Science and Computation Structures (FoSSaCS 2016)*, Lecture Notes in Computer Science 9634, 2016, pp. 353–369, doi:[10.1007/978-3-662-49630-5_21](https://doi.org/10.1007/978-3-662-49630-5_21); read in arXiv:1601.01587v1 ([arXiv](https://arxiv.org/abs/1601.01587v1)), whose numbering is used: the introduction, Section 2 (distributed IMCs and the distributed synthesis problem), and Section 4 (undecidability results) with Theorem 2 (distributed IMCs), Proposition 1 (the reduction from DEC-POMDPs) and Theorem 3 (DEC-POMDPs).
