# Mean-payoff games with partial observation are undecidable

No algorithm decides whether the first player of a finite mean-payoff game with partial observation has an observation-based strategy ensuring liminf mean payoff at least zero; whether such a game with limited observation is forcibly terminating is undecidable as well.

A *mean-payoff game with partial observation* is a tuple $G=(Q,q_I,\Sigma,\Delta,w,\mathrm{Obs})$ with a finite set $Q$ of states, an initial state $q_I$, a finite set $\Sigma$ of actions, a total transition relation $\Delta\subseteq Q\times\Sigma\times Q$, integer weights $w$ on transitions, and a partition $\mathrm{Obs}$ of $Q$ into observations. In each round Eve chooses an action and Adam resolves the nondeterminism; Eve sees only the observations and plays *observation-based* strategies, which depend only on the sequence of observations and actions. For a play $\pi$, $\underline{\mathrm{MP}}(\pi)$ is the $\liminf$ of the average weights of its prefixes. The game has *limited observation* if $\{q_I\}$ is an observation and the $\sigma$-successors of an observation always form a union of observations.

**Theorem.** Determining whether Eve has an observation-based strategy ensuring $\underline{\mathrm{MP}}\ge0$ in a mean-payoff game with partial observation is undecidable (Theorem 1 of the source); for the threshold $\underline{\mathrm{MP}}>0$ this was shown by Degorre, Doyen, Gentilini, Raskin and Toruńczyk.

The source also shows that determining whether a mean-payoff game with limited observation is *forcibly terminating*, i.e. whether the reachability game on abstract plays that the source associates with it is won by one of the players, is undecidable (Theorem 6).

Eve may need infinite memory to ensure $\underline{\mathrm{MP}}\ge0$, and these games are not determined under concrete strategies, though they are determined when Adam may play observation-based strategies (Theorem 2, for limited observation). Winning a forcibly terminating game is decidable, and the source identifies subclasses (forcibly first abstract cycle games, first abstract cycle games) whose membership and winner problems are decidable.

## Depends on

- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](../../quantitative-games/classical-quantitative-objectives.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

A mean-payoff game with limited observation can simulate a deterministic four-counter machine, and hence a Turing machine, so that Eve wins the associated reachability game iff the machine accepts and Adam wins it iff the machine rejects; this gives Theorem 6. For Theorem 1 the construction is adapted to two-counter machines: a pumping phase at the start, weights $0$ and $-1$ on its loops, and a sink observation for Adam at the halting state make Adam win, by exiting the pumping phase after $N$ steps and simulating faithfully, iff the machine halts within some $N$ steps; so Eve wins iff the machine does not halt.

## Sources

- Paul Hunter, Arno Pauly, Guillermo A. Pérez and Jean-François Raskin, "Mean-payoff games with partial observation", *Theoretical Computer Science* 735, 2018, pp. 82–110, doi:[10.1016/j.tcs.2017.03.038](https://doi.org/10.1016/j.tcs.2017.03.038); read in arXiv:1309.5462v6 ([arXiv](https://arxiv.org/abs/1309.5462v6)), whose numbering is used (separate counters for theorems and for lemmas, propositions and corollaries): Section 2 (preliminaries), Section 3 (Theorem 1 and the proposition on infinite memory), Proposition on simulating Turing machines and Theorem 6 in the section on forcibly terminating games, and the subsection with the modifications for Theorem 1.
- The undecidability for the strict liminf threshold is due to Aldric Degorre, Laurent Doyen, Raffaella Gentilini, Jean-François Raskin and Szymon Toruńczyk, "Energy and Mean-Payoff Games with Imperfect Information", in *Computer Science Logic (CSL 2010)*, Lecture Notes in Computer Science 6247, 2010, pp. 260–274, doi:[10.1007/978-3-642-15205-4_22](https://doi.org/10.1007/978-3-642-15205-4_22), as recalled in the source above (not read).
