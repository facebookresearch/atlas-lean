# Careful cooperative rational synthesis with two resources is undecidable

No algorithm decides whether a multi-player game with several common resources has a Nash equilibrium of resource-careful players
whose play keeps the resources nonnegative and meets the global specification, already for two players, two resources and
reachability objectives.

**Theorem.** The [careful cooperative rational synthesis](careful-cooperative-rational-synthesis-with-comm.md) problem is
undecidable, even for games with two players and two resources in which all objectives, the global specification included, are reachability objectives (Theorem 5 of the source). The reduction is from reachability of a target location with both counters zero in [two-counter automata](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md) with guards, and takes the global specification equal to Player 1's objective.

With a single common resource the problem is decidable (in polynomial space for parity objectives), and it becomes decidable again
when every resource has a bounded capacity, with LTL objectives no harder than reactive synthesis.

## Depends on

- [Careful cooperative rational synthesis with common resources](careful-cooperative-rational-synthesis-with-comm.md)
- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces reachability in $2$-counter automata, whose transitions carry integer updates and lower and upper guards on the
counters: does some run from the initial location with zero counters reach a target location with both counters $0$? It is
undecidable by a reduction from two-counter machines (Minsky). The two counters become the two resources. Player 1, whose objective is
also the global specification, owns the locations and chooses the transitions; for each transition, gadgets owned by Player 2 let
Player 2 reach a winning sink if an upper guard is violated, while a violated lower guard drives a resource below $0$. A solution
profile exists exactly when the counter automaton has a run reaching the target with zero counters.

## Sources

- R. Condurache, C. Dima, M. Jitaru, Y. Oualhadj and N. Troquard, "Careful autonomous agents in environments with multiple common resources", in *Proceedings of the Second Workshop on Agents and Robots for reliable Engineered Autonomy (AREA 2022)*, Electronic Proceedings in Theoretical Computer Science 362, pp. 3–14, 2022, doi:10.4204/EPTCS.362.3; read in arXiv:2207.09707v1: Theorem 5 in Section 3 (Undecidability) with Lemma 3 ($2$-counter automata) and Proposition 4 (the reduction) before it, Theorem 7 in Section 4 (bounded resources), and the introduction (the one-resource case).
