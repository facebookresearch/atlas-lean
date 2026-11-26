# Timed regular languages are not closed under complementation

There is a [timed regular language](timed-buchi-automata.md) whose complement, in the set of all timed words over the same
alphabet, is not timed regular. Otherwise inclusion $L(\mathcal{A}_1) \subseteq L(\mathcal{A}_2)$ would hold exactly when the
intersection of $L(\mathcal{A}_1)$ with a timed Büchi automaton for the complement of $L(\mathcal{A}_2)$ is empty, and enumerating
timed Büchi automata, whose emptiness is decidable, would make non-inclusion recursively enumerable, contradicting the
$\Pi^1_1$-hardness of inclusion.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Proof depends on

- [Universality of timed automata is undecidable](universality-of-timed-automata-is-undecidable.md)
- [Region abstraction decides reachability for timed automata](../../../Logic/temporal-logic/timed-and-infinite-state-verification/region-abstraction-decides-reachability-for.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 5.5 and Corollary 5.6 with its proof.
