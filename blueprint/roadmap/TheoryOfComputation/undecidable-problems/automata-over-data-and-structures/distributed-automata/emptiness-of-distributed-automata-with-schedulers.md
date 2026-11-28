# Emptiness of distributed automata with schedulers is undecidable for six of seven classes

Whether a distributed automaton in the Esparza–Reiter framework accepts some labeled graph is undecidable for every class except the weakest one, in which it is trivially decidable.

**Theorem (Principato, Esparza and Czerner).** For every class $xyz$ of [distributed automata with schedulers](distributed-machines-with-schedulers.md) with $xyz\in\{\mathtt d,\mathtt D\}\{\mathtt a,\mathtt A\}\{\mathtt f,\mathtt F\}$ and $xy\neq\mathtt{da}$, given a Turing machine $T$ one can effectively construct an $xyz$-distributed automaton $A^T$ such that $L(A^T)\neq\emptyset$ iff $T$ halts on the blank tape. Hence the emptiness problem is undecidable for these six classes of expressive power (Theorem 2 of arXiv:2504.07339v1).

For the remaining class $\mathtt{daf}$ the emptiness problem is trivially decidable.

Since distributed automata are closed under intersection (Lemma 3 of the source), the safety problem (does the automaton accept some graph of a given recognizable class of dangerous graphs) is undecidable as well for these classes.

## Depends on

- [Distributed automata with schedulers and their classes](distributed-machines-with-schedulers.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem is undecidable for multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof exhibits a family $\{G_n\}$ of labeled graphs (numbered line graphs, or weaker variants for the classes with existence detection or halting acceptance) together with an automaton $A^L$ recognizing exactly the family and an automaton $A^H$ that on $G_n$ simulates $T$ on a tape of $n$ cells and accepts iff $T$ halts within those cells; the product automaton recognizing $L(A^L)\cap L(A^H)$ is nonempty iff $T$ halts. The constructions are given for synchronous scheduling and transferred to liberal scheduling and to strong fairness using the expressive-power results of Esparza and Reiter.

## Sources

- Flavio T. Principato, Javier Esparza and Philipp Czerner, "Undecidability of the emptiness problem for weak models of distributed computing", *Theoretical Computer Science* 1067, 2026, article 115757, doi:[10.1016/j.tcs.2026.115757](https://doi.org/10.1016/j.tcs.2026.115757); read in arXiv:2504.07339v1 ([arXiv](https://arxiv.org/abs/2504.07339v1)), whose numbering is used: the abstract, Section 2 (distributed machines, distributed automata and their classes, Proposition 1), Section 3 (Theorem 2, Lemma 3 and the overall argument), Section 4 (the classes with halting acceptance) and the conclusion.
