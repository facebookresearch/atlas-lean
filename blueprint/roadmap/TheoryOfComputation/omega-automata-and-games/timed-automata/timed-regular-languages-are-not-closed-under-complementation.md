# Timed regular languages are not closed under complementation

There is a [timed regular language](timed-buchi-automata.md) whose complement, in the set of all timed words over the same
alphabet, is not timed regular. Otherwise $L(\mathcal{A}_1) \not\subseteq L(\mathcal{A}_2)$ would hold exactly when some timed Büchi
automaton $\mathcal{C}$ has $L(\mathcal{A}_1) \cap L(\mathcal{C}) \ne \emptyset$ and $L(\mathcal{A}_2) \cap L(\mathcal{C}) = \emptyset$ (closure under complement gives such a $\mathcal{C}$
when inclusion fails, and any such $\mathcal{C}$ witnesses non-inclusion); both conditions are decidable, by closure under intersection and
decidability of emptiness, so enumerating candidates $\mathcal{C}$ would make non-inclusion recursively enumerable, contradicting the
$\Pi^1_1$-hardness of inclusion.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Proof depends on

- [Timed regular languages are closed under union and intersection](timed-regular-languages-are-closed-under-union-and-intersection.md)
- [Universality of timed automata is undecidable](universality-of-timed-automata-is-undecidable.md)
- [Region abstraction decides reachability for timed automata](../../../Logic/temporal-logic/timed-and-infinite-state-verification/region-abstraction-decides-reachability-for.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 5.5 and Corollary 5.6 with its proof.
