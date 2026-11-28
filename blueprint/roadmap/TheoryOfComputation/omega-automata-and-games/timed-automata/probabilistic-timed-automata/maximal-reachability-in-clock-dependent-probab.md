# Maximal reachability in clock-dependent probabilistic timed automata is undecidable

No algorithm decides whether the maximum probability of reaching a set of locations in a probabilistic timed automaton whose transition probabilities depend piecewise linearly on clock values is at least a given threshold; this holds already with three clocks.

**Clock-dependent probabilistic timed automata.** Clock constraints over a finite set $\mathcal{X}$ of clocks are conjunctions of comparisons $x \sim c$ with $x \in \mathcal{X}$, ${\sim} \in \{<, \le, \ge, >\}$ and $c \in \mathbb{N}$. A *distribution template* over a set $Q$ assigns to each clock valuation $v$ a probability distribution on $Q$. A *clock-dependent probabilistic timed automaton* (cdPTA) $(L, \bar{l}, \mathcal{X}, \mathit{inv}, \mathit{prob})$ has a finite set $L$ of locations with initial location $\bar{l}$, a finite set $\mathcal{X}$ of clocks, an invariant clock constraint $\mathit{inv}(l)$ for each location, and a finite set $\mathit{prob}$ of *probabilistic edges* $(l, g, \wp)$, each with a source location $l$, a guard $g$ and a distribution template $\wp$ over pairs $(X, l')$ of a set of clocks to reset and a target location. Time elapses in a location while its invariant holds, the amount being chosen nondeterministically; an enabled probabilistic edge is then chosen nondeterministically, and the reset set and target location are drawn from the distribution $\wp[v]$ given by the current valuation $v$. As in the source, each probability of a template is a continuous piecewise linear function of the clock values, given by rational coefficients on finitely many intervals with natural-number endpoints. Resolving the nondeterminism by strategies gives, for a set $F$ of target locations, the *maximal reachability probability*, the supremum over strategies of the probability of reaching $F$.

**Theorem (Sproston).** The *maximal reachability problem*, which asks whether the maximal probability of reaching a given set of locations is at least a given rational threshold, is undecidable for cdPTAs with at least $3$ clocks (Theorem 1 of the source).

The same paper shows that the maximal and minimal reachability probabilities of cdPTAs can be approximated through a region-graph construction.

## Depends on

- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the non-halting problem for two-counter machines. A cdPTA with clocks $x_1, x_2, x_3$ has modules for the instructions; on entry to a module $x_1 = 2^{-c_1}$, $x_2 = 2^{-c_2}$ and $x_3 = 0$. A step is simulated by a nondeterministic delay, after which a probabilistic edge whose probabilities depend on the clocks, such as $\frac12(x_1 + x_3)$, either continues the simulation or checks the delay; the check reaches the target with probability exactly $\frac14$ if the delay was correct and with smaller probability otherwise. Summing over steps, some strategy reaches the target with probability at least $\frac14$ if and only if the machine does not halt.

## Sources

- J. Sproston, "Probabilistic Timed Automata with Clock-Dependent Probabilities", *Fundamenta Informaticae* 178(1–2), 2021, pp. 101–138, doi:10.3233/FI-2021-2000; read as arXiv:1707.04507v1, <https://arxiv.org/abs/1707.04507v1>: Theorem 1 (the maximal reachability problem is undecidable for cdPTAs with at least $3$ clocks) with its proof in Section 3, the definitions of cdPTAs, distribution templates, piecewise linear clock dependencies and the maximal reachability problem in Section 2, and the abstract (approximation), in the numbering of that version.
