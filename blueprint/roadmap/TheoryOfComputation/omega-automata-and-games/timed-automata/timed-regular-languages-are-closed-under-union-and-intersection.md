# Timed regular languages are closed under union and intersection

If $L_1, \dots, L_n$ are [timed regular languages](timed-buchi-automata.md) over the same alphabet, then so are
$L_1 \cup \dots \cup L_n$ and $L_1 \cap \dots \cap L_n$. For the union take the disjoint union of timed Büchi automata for the
$L_i$; for the intersection run them in parallel on disjoint sets of clocks, with a counter $k \in \{1, \dots, n\}$ that
waits for an accepting state of the $k$-th automaton before moving to the next, as in the product of Büchi automata.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 3.15 and its proof.
