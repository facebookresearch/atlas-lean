# Bounded window mean-payoff games with partial observation are undecidable

No algorithm decides whether the first player of a finite weighted game with partial observation can ensure a bounded window mean-payoff objective, in any of its four variants, even when she observes nothing; with a fixed window size the corresponding problems are decidable.

A *weighted game arena with partial observation* $\langle Q,q_I,\Sigma,\Delta,w,\mathrm{Obs}\rangle$ has a finite set of states, an initial state, actions, a total transition relation $\Delta\subseteq Q\times\Sigma\times Q$, integer weights, and a partition $\mathrm{Obs}$ of $Q$ into observations containing $\{q_I\}$; it is *blind* if there is a single observation. Eve chooses actions based on the observations, Adam resolves the nondeterminism, and an abstract play stands for the set of its concrete plays. For a window bound $\ell_{\max}\ge1$ and a rational threshold $\nu\in\mathbb Q$, a concrete play $\pi$ has a *good window* at position $i$ if some $j\le\ell_{\max}$ has $w(\pi[i..i+j])/j\ge\nu$. The *bounded window mean-payoff* objectives ask for a window bound to exist:

- $\mathrm{UDirBnd}(\nu)$: some $\ell_{\max}$ works for every concrete play and every position;
- $\mathrm{DirBnd}(\nu)$: every concrete play has its own $\ell_{\max}$ that works at every position;
- $\mathrm{UBnd}(\nu)$: some $\ell_{\max}$ and some position $i$ work for every concrete play from $i$ on;
- $\mathrm{Bnd}(\nu)$: every concrete play has its own $\ell_{\max}$ and $i$.

These are window strengthenings, introduced by Chatterjee, Doyen, Randour and Raskin, of the classical mean-payoff objective (see [classical quantitative objectives](../../quantitative-games/classical-quantitative-objectives.md)).

**Theorem (Theorem 2).** Given a weighted game arena with partial observation, determining whether Eve has a winning strategy for any of the bounded window mean-payoff objectives is undecidable, even if the arena is blind.

With perfect information, the multidimensional versions of $\mathrm{UDirBnd}$ and $\mathrm{UBnd}$ are non-primitive-recursive hard (Chatterjee et al.), and for the fixed window objectives with $\ell_{\max}$ given as input the source gives decision procedures.

## Depends on

- [Classical quantitative objectives](../../quantitative-games/classical-quantitative-objectives.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of min-plus weighted automata over the integers is undecidable](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/tropical-automata-and-matrices/universality-of-min-plus-integer-automata.md)

## Expansion

The reduction is from universality of weighted finite automata (every word has minimal accepting-run cost $<0$), undecidable by Almagor, Boker and Kupferman. From an automaton $\mathcal N$ the source builds a blind arena in which Adam secretly picks one of three gadgets; a blind strategy of Eve is an infinite word over $\Sigma\cup\{\#\}$. If $\mathcal N$ is universal Eve wins $\mathrm{UDirBnd}$, and if not, Adam wins the complement of $\mathrm{Bnd}$; since $\mathrm{UDirBnd}\subseteq\mathrm{DirBnd},\mathrm{UBnd}\subseteq\mathrm{Bnd}$, all four objectives are undecidable at once.

## Sources

- Paul Hunter, Guillermo A. Pérez and Jean-François Raskin, "Looking at mean payoff through foggy windows", *Acta Informatica* 55(8), 2018, pp. 627–647, doi:[10.1007/s00236-017-0304-7](https://doi.org/10.1007/s00236-017-0304-7); read in arXiv:1504.02947v1 ([arXiv](https://arxiv.org/abs/1504.02947v1)), whose numbering is used: Section 2 (weighted game arenas with partial observation), Section 3 (window mean-payoff objectives and Theorem 2) and the appendix section with the proof of Theorem 2.
