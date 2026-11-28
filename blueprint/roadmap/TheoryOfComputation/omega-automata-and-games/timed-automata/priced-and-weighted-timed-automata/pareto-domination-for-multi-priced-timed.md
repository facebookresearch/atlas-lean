# Pareto domination for multi-priced timed automata is undecidable

No algorithm decides whether a timed automaton with several cost and reward observers can reach a target location with accumulated costs at most, and rewards at least, a given vector, although the problem is decidable with at most three observers.

A *multi-priced timed automaton* is a timed automaton (locations, clocks, edges with clock constraints and resets, accepting locations; see [timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)) with a finite set $\mathcal Y$ of *observers* and a rate function giving each location a vector of nonnegative integer rates. Along a run, each observer accumulates the time spent in each location multiplied by its rate there. The observers are partitioned into *cost* variables, to be minimized, and *reward* variables, to be maximized; $\gamma'$ *dominates* $\gamma$ if $\gamma'(y)\le\gamma(y)$ for every cost and $\gamma'(y)\ge\gamma(y)$ for every reward. The *Pareto Domination Problem* asks, given the automaton and a target $\gamma\in\mathbb R^{\mathcal Y}$, whether some accepting run accumulates a vector that dominates $\gamma$.

**Theorem.** The Pareto Domination Problem for multi-priced timed automata is undecidable (Theorem 3 of the source); the reduction yields undecidability for some fixed, large number of observers.

The source states the problem for targets $\gamma\in\mathbb R_{\ge0}^{\mathcal Y}$; its reduction, from Hilbert's tenth problem through the problem of reaching a single valuation, uses only targets with natural-number coordinates, so the problem is undecidable already for such targets, which are finite inputs.

By contrast, the problem is decidable for automata with at most three observers, PSPACE-complete when the observers are all costs or all rewards, and an $\varepsilon$-approximate version is decidable without restricting the number and types of observers.

## Depends on

- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from satisfiability over positive integers of conjunctions of equations $X=Y+Z$ and $X=YZ$, which is undecidable by reduction from Hilbert's tenth problem. Pareto constraints such as $c_1\le1\le c_2$ on two observers force clock values of the form $1/n$ for positive integers $n$ when control enters a gadget, and gadgets for addition and multiplication combine such values; a target vector that is dominated exactly when all constraints hold encodes a solution. Universal Diophantine equations (degree $4$ with $58$ variables, Jones) bound the number of observers needed.

## Sources

- Martin Fränzle, Mahsa Shirmohammadi, Mani Swaminathan and James Worrell, "Costs and rewards in priced timed automata", *Information and Computation* 282, 2022, article 104656, doi:[10.1016/j.ic.2020.104656](https://doi.org/10.1016/j.ic.2020.104656); read in arXiv:1803.01914v2 ([arXiv](https://arxiv.org/abs/1803.01914v2)), whose numbering is used: the abstract and introduction, Section 3 (multi-priced timed automata and the Pareto Domination Problem), Section 4 (Theorem 3 and its reduction) with Proposition 16 (the fragment $\mathcal L$ is undecidable) in the appendix, and Sections 6–8 for the decidable cases.
