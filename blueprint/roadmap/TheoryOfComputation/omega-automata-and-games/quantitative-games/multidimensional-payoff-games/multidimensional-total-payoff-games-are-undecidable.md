# Multidimensional total-payoff games are undecidable

No algorithm decides whether the first player of a finite two-player game with five-dimensional integer weights can ensure that the infimum, or the supremum, total payoff reaches a given threshold vector, although the corresponding mean-payoff problems are decidable.

A *multi-weighted game structure* is a finite directed graph in which every vertex has an outgoing edge, so that plays are infinite, whose vertices are split between player 1 and player 2, with a weight function assigning a vector in $\mathbb Z^k$ to each edge (weights in binary). For a play $\pi=s_0s_1\cdots$, the total payoff of a prefix is the sum of its edge weights, and the *infimum* and *supremum total payoff* of $\pi$ are the componentwise $\liminf$ and $\limsup$ of these sums (the one-dimensional objectives are recalled in [classical quantitative objectives](../classical-quantitative-objectives.md)). The *threshold problem* asks, given the game, an initial vertex and a threshold vector $v\in\mathbb Q^k$, whether player 1 has a strategy ensuring that the infimum (respectively supremum) total payoff is $\ge v$ in every dimension against every strategy of player 2.

**Theorem.** The threshold problem for infimum and for supremum total-payoff objectives is undecidable in multi-weighted games with five dimensions (Theorem 1 of the source).

In one dimension total-payoff and mean-payoff games are closely related and solvable in $\mathrm{NP}\cap\mathrm{coNP}$; in several dimensions the threshold problem for infimum mean payoff is coNP-complete and the one for supremum mean payoff is in $\mathrm{NP}\cap\mathrm{coNP}$ (Velner and Rabinovich; Velner et al.), so the undecidability is specific to total payoff.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](../classical-quantitative-objectives.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from halting of two-counter machines, assumed without loss of generality to halt with both counters zero. The game's states copy the machine's control states, and player 1 simulates the machine; edge weights have the form $(c_1,-c_1,c_2,-c_2,d)$, so the running sum is $(v_1,-v_1,v_2,-v_2,-n)$ for counter values $v_1,v_2$ after $n$ steps, and the halting state loops on $(0,0,0,0,1)$. After each step, and after each zero test, player 2 may branch to absorbing states whose self-loops keep a dimension strictly negative exactly when player 1 has let a counter go negative or passed a zero test with a positive counter, while making every dimension nonnegative otherwise; so an unfaithful simulation loses and an interrupted faithful one wins. With threshold $\vec0$, a halting faithful simulation reaches the halting loop with counters $0$ and wins, whereas a non-halting one keeps the fifth sum negative; hence player 1 wins iff the machine halts.

## Sources

- Krishnendu Chatterjee, Laurent Doyen, Mickael Randour and Jean-François Raskin, "Looking at mean-payoff and total-payoff through windows", *Information and Computation* 242, 2015, pp. 25–52, doi:[10.1016/j.ic.2015.03.010](https://doi.org/10.1016/j.ic.2015.03.010); read in arXiv:1302.4248v3 ([arXiv](https://arxiv.org/abs/1302.4248v3)), whose numbering is used: the preliminaries (multi-weighted game structures, total-payoff and mean-payoff objectives) and Theorem 1 with its proof in the section on mean-payoff and total-payoff objectives.
