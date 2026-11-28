# Mean-payoff pushdown games are undecidable

No algorithm decides whether the first player of a two-player game on the configuration graph of a weighted pushdown system has a strategy, or a finite-memory strategy, ensuring a nonnegative or positive mean payoff; the same holds when the stack must also stay bounded.

A *weighted pushdown system* $(Q,\Gamma,q_0,E,w)$ has finitely many states with initial state $q_0$, a stack alphabet $\Gamma$ with a bottom symbol $\bot$ that is never pushed or popped, transitions that read the state and the top stack symbol and change the state and apply a push, pop or skip command, and integer weights $w$ on transitions (in binary). In a *weighted pushdown game* the states are partitioned between player 1 and player 2; the infinite game graph has the configurations (stack, state) as vertices, starting from $(\bot,q_0)$, and the owner of the current state picks the next transition. Strategies may depend on the whole history (*global strategies*); *finite-memory* strategies are finite-state transducers over transitions. For an infinite play $\pi$, $\mathrm{LimInfAvg}(\pi)$ and $\mathrm{LimSupAvg}(\pi)$ are the lower and upper limits of the average weights of its prefixes (see [classical quantitative objectives](../classical-quantitative-objectives.md)).

**Theorem.** Given a weighted pushdown game, it is undecidable whether player 1 has a winning strategy, and whether player 1 has a finite-memory winning strategy,
1. for the objective $\Phi\bowtie0$, with $\Phi\in\{\mathrm{LimInfAvg},\mathrm{LimSupAvg}\}$ and $\bowtie\in\{\ge,>\}$;
2. for the same objectives together with *stack boundedness* (the stack height along the play stays bounded).

(Theorem 6 of the source.)

With a single player (pushdown systems) the source solves these problems in polynomial time, and under *modular* strategies, which depend only on the history of the current module invocation of the equivalent recursive game, the problem is NP-complete for pushdown games and systems alike.

## Depends on

- [Classical quantitative objectives](../classical-quantitative-objectives.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of min-plus weighted automata over the integers is undecidable](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/tropical-automata-and-matrices/universality-of-min-plus-integer-automata.md)

## Expansion

The reduction is from non-universality of weighted finite automata with weights in $\{-1,0,1\}$ under min-plus semantics (some word $\rho$ has value $\ge\nu$), undecidable by Krob and by Almagor, Boker and Kupferman. Five gadgets make each iteration of the game consist of player 1 filling the stack with padding symbols and the letters of a word $\rho$, then player 2 simulating a minimal-weight run of the automaton on $\rho$ while popping, after which the game returns to the initial state. If some word has positive value, player 1 repeats it and secures a positive mean payoff; if all values are at most $0$, player 2 keeps the mean payoff at most $0$; this gives the strict objectives, and the non-strict ones for general strategies by duality. For finite-memory or stack-bounded strategies with threshold $0$, a word of value $\ge0$ gives player 1 a finite-memory, stack-bounded winning strategy, while if every word has value $\le-1$, player 2 holds the mean payoff to at most $-1/(2M)$ against memory or stack height $M$.

## Sources

- Krishnendu Chatterjee and Yaron Velner, "Mean-Payoff Pushdown Games", in *2012 27th Annual IEEE Symposium on Logic in Computer Science (LICS)*, 2012, pp. 195–204, doi:[10.1109/LICS.2012.30](https://doi.org/10.1109/LICS.2012.30); read in arXiv:1201.2829v3 ([arXiv](https://arxiv.org/abs/1201.2829v3)), whose numbering, checked in the PDF, is used: the definitions of weighted pushdown systems and mean-payoff objectives in the section on mean-payoff pushdown graphs, and the definition of weighted pushdown games, Theorem 5 (non-universality of weighted automata, cited there), Lemma 19 (the reduction) and Theorem 6 (undecidability) in the section on mean-payoff pushdown games.
