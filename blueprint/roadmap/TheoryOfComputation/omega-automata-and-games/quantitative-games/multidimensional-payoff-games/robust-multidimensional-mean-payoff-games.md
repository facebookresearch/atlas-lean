# Robust multidimensional mean-payoff games are undecidable

When the winning condition is an arbitrary Boolean combination of threshold conditions on the liminf mean payoffs of several weight dimensions, no algorithm decides the winner of a finite two-player game, already with ten dimensions; the same holds for games over mean-payoff expressions.

A *robust multidimensional mean-payoff game* is a finite two-player game graph with a weight function $w:E\to\mathbb Q^k$ and a winning condition that is a Boolean formula over atoms $\mathrm{LimInfAvg}_i\sim\nu_i$ with $\sim\in\{\ge,>,\le,<\}$ and $\nu_i\in\mathbb Q$, where $\mathrm{LimInfAvg}_i(\pi)$ is the $\liminf$ of the averages of dimension $i$ along the play (see [classical quantitative objectives](../classical-quantitative-objectives.md)). Equivalently, the condition is a positive Boolean formula over atoms $\mathrm{LimInfAvg}_i\ge\nu_i$, $\mathrm{LimSupAvg}_i\ge\nu_i$ and their strict versions, since $\liminf$ of a sequence is minus the $\limsup$ of its negation. Player 1 wins if he has a strategy, with arbitrary memory, ensuring the condition against every strategy of player 2.

**Theorem.** Deciding the winner of a robust multidimensional mean-payoff game with ten dimensions is undecidable (Theorem 1 of the source); thresholds $0$ and non-strict inequalities suffice.

The source also shows that two-player games over mean-payoff expressions are undecidable (Theorem 2).

For positive formulas over $\mathrm{LimInfAvg}$ atoms only (only $\ge$ and $>$ in the original formulation) the winner is decidable (Velner and Rabinovich), and with player 1 restricted to finite-memory strategies the problem is inter-reducible with Hilbert's tenth problem over the rationals (Velner); the undecidability comes from combining $\liminf$ and $\limsup$ conditions.

## Depends on

- [Classical quantitative objectives](../classical-quantitative-objectives.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem for counter machines, first for one counter and then for two. Gadgets for increment, decrement, no-op and zero test give each counter two dimensions $c_+,c_-$ and guard dimensions, and the winning condition, for two counters

$$
(\mathrm{Inf}_\ell\wedge\mathrm{Inf}_r\vee\mathrm{Sup}_{g_s})\wedge(\mathrm{Inf}_{c^1_+}\wedge\mathrm{Inf}_{c^1_-}\wedge\mathrm{Inf}_{c^2_+}\wedge\mathrm{Inf}_{c^2_-}\vee\mathrm{Sup}_{g_c})\wedge\mathrm{Sup}_x\wedge\mathrm{Sup}_y
$$

with all thresholds $0$, uses ten dimensions; player 2 wins iff the machine halts. Mean-payoff expressions built from $\max$, $\min$, $\mathrm{LimInfAvg}$ and $\mathrm{LimSupAvg}$ can express these conditions, which gives Theorem 2.

## Sources

- Yaron Velner, "Robust Multidimensional Mean-Payoff Games are Undecidable", in *Foundations of Software Science and Computation Structures (FoSSaCS 2015)*, Lecture Notes in Computer Science 9034, 2015, pp. 312–327, doi:[10.1007/978-3-662-46678-0_20](https://doi.org/10.1007/978-3-662-46678-0_20); read in arXiv:1410.5703v1 ([arXiv](https://arxiv.org/abs/1410.5703v1)): Section 1 (related work), Section 2 (robust multidimensional mean-payoff games), Section 3 (the reduction), Section 4.3 (extension to two-counter machines with Theorem 1) and Theorem 2 on mean-payoff expressions in Section 5.
