# Deterministic timed Muller automata are closed under Boolean operations

The timed languages accepted by [deterministic timed Muller automata](deterministic-timed-automata.md) over an alphabet
$\Sigma$ are closed under union, intersection and complementation with respect to the set of all timed words over
$\Sigma$. Completing an automaton with a sink state, entered on the negation of the disjunction of the constraints of the
other edges with the same source and letter, gives exactly one run over every timed word, so complementation replaces the
acceptance family $\mathcal{F}$ by $2^S \setminus \mathcal{F}$.

By contrast, the timed languages of deterministic timed Büchi automata are closed under union and intersection but not
under complementation; the complement of such a language is accepted by a deterministic timed Muller automaton.

## Depends on

- [Deterministic timed automata](deterministic-timed-automata.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 6.4 and its proof, and Theorem 6.5.
