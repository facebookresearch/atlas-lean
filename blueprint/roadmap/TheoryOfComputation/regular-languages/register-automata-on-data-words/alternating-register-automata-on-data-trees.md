# Alternating register automata on data trees become undecidable with upward moves or two registers

Nonemptiness of forward alternating automata with one register on finite data trees is decidable but not primitive recursive; allowing upward moves, leftward moves, or a second register makes it undecidable.

A *data tree* is a finite (or countably infinite) sibling-ordered tree whose nodes carry a letter from a finite alphabet and a datum from an infinite set, data being compared only for equality. A *forward alternating automaton with one register* (ATRA$_1$) reads a data tree moving only downward (to the first child) and rightward (to the next sibling); its transitions are positive Boolean combinations of moves, and it can store the current datum in its register and compare later data with it (compare [register automata on data words](register-automata-on-data-words.md)).

**Theorem (Jurdziński and Lazić).** Nonemptiness of ATRA$_1$ over data trees becomes undecidable (more precisely, hard for the recursively enumerable sets) if any one of the following is added: upward moves, leftward moves, or a second register. With the weak acceptance mechanism over infinite data trees, nonemptiness of ATRA$_1$ is undecidable as well.

By contrast, nonemptiness of ATRA$_1$ over finite data trees is decidable but not primitive recursive (Theorem 3.1), and nonemptiness of ATRA$_1$ with the safety acceptance mechanism over finite and infinite data trees is decidable but not elementary (Theorem 4.1). The weak-acceptance case already holds for data words, see [nonemptiness of alternating one-register automata on data ω-words](nonemptiness-of-alternating-one-register.md).

As an application, satisfiability of forward XPath with arbitrary DTDs over finite XML trees is decidable, and so is satisfiability of safety forward XPath over finite or infinite trees.

## Depends on

- [Register automata on data words](register-automata-on-data-words.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The decidability results translate ATRA$_1$ into nondeterministic tree automata with faulty (incrementing) counters, whose nonemptiness is decidable by well-quasi-ordering arguments. The undecidability follows from lower-bound results for register automata on data words, which are special data trees: the source derives it from lower-bound results for register automata and logics on data words (Neven, Schwentick and Vianu; David; Demri and Lazić), and the weak-acceptance case from the undecidability over infinite data words of Demri and Lazić. A good expansion links pages for these results.

## Sources

- Marcin Jurdziński and Ranko Lazić, "Alternating automata on data trees and XPath satisfiability", *ACM Transactions on Computational Logic* 12(3), 2011, article 19, pp. 1–21, doi:[10.1145/1929954.1929956](https://doi.org/10.1145/1929954.1929956); read in arXiv:0805.0330v4 ([arXiv](https://arxiv.org/abs/0805.0330v4)), whose numbering is used: the abstract and the introduction (the results on ATRA$_1$ and their limits, which state the undecidability), Theorems 3.1, 4.1 and 5.2, and the preliminaries.
- S. Demri and R. Lazić, "LTL with the freeze quantifier and register automata", *ACM Transactions on Computational Logic* 10(3), 2009, article 16, doi:10.1145/1507244.1507246, and F. Neven, T. Schwentick and V. Vianu, "Finite state machines for strings over infinite alphabets", *ACM Transactions on Computational Logic* 5(3):403–435, 2004, doi:10.1145/1013560.1013562 (original sources of the lower bounds for register automata on data words, cited beside the copy read).
