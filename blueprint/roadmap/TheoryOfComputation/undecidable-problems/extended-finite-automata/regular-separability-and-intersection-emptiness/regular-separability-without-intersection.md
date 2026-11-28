# Regular separability can be undecidable where intersection emptiness is decidable

There is a class of languages, accepted by automata that only increment a counter and test it against predicates given by reset vector addition systems, for which emptiness of intersections is decidable but separability by regular languages is undecidable; conversely, separability can be decidable while intersection emptiness is not.

**Theorem.** For language classes $\mathcal C_1, \mathcal C_2$, the *intersection emptiness problem* $\mathrm{IE}(\mathcal C_1, \mathcal C_2)$ asks, given $K \in \mathcal C_1$ and $L \in \mathcal C_2$, whether $K \cap L = \emptyset$, and the *regular separability problem* $\mathrm{RS}(\mathcal C_1, \mathcal C_2)$ asks whether there is a regular language $S$ with $K \subseteq S$ and $S \cap L = \emptyset$. For $w \in \{0, 1\}^*$ let $\nu(w)$ be the number it represents in binary ($\nu(\varepsilon) = 0$, $\nu(w0) = 2\nu(w)$, $\nu(w1) = 2\nu(w) + 1$). A *reset VASS* is a finite automaton with counters over $\mathbb N$ whose edges read a word and increment, decrement (only from a positive value), leave unchanged or reset one counter; its language is the set of words leading from the initial state with all counters $0$ to a final state. Let $\mathcal R$ be the class of languages of reset VASS, and call $P \subseteq \mathbb N$ a *pseudo-$\mathcal R$ predicate* if $P = \nu(L)$ for some $L \in \mathcal R$ over $\{0, 1\}$. An *incrementing automaton* over pseudo-$\mathcal R$ predicates has finitely many states and edges $(q, w, m, q')$ that read a word $w$ and add $m \in \{0, 1\}$ to a single counter starting at $0$, and accepts when it reaches a state $q$ with a counter value in a predicate $P$ attached to $q$. For the class $\mathcal I$ of languages accepted by such automata, $\mathrm{IE}(\mathcal I, \mathcal I)$ is decidable and $\mathrm{RS}(\mathcal I, \mathcal I)$ is undecidable (Theorem 4.1 of the source).

Conversely, for the class $\mathcal H$ of languages of higher-order pushdown automata and the class of incrementing automata over the predicates $(\mathbb N \setminus 2^{\mathbb N}) \cup \{2^{\nu(w)} : w \in L\}$, where $2^{\mathbb N}$ is the set of powers of $2$, with $L \in \mathcal H$, regular separability is decidable but intersection emptiness is undecidable (Theorem 5.2). So neither problem reduces to the other in general, although for all classes studied before they were decidable together.

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Coverability is decidable for well-structured transition systems](../../../../Logic/temporal-logic/timed-and-infinite-state-verification/coverability-is-decidable-for-well-structured.md)

## Expansion

Decidability of intersection emptiness uses that reset VASS languages are closed under rational transductions and intersection and have a decidable emptiness problem, as reset VASS are well-structured transition systems (Lemmas 4.2 and 4.3). Regular separability is shown undecidable by reducing the infinity problem for $\mathcal R$, whether a reset VASS language is infinite, which is undecidable because boundedness of reset VASS is undecidable (Dufourd, Finkel and Schnoebelen); a good expansion links pages for these two undecidability results. From $L \in \mathcal R$ one forms $K = \{1 0^{|w|} : w \in L\} \in \mathcal R$, so that $\nu(K)$ is a set of powers of $2$ that is infinite iff $L$ is; then $K_1 = a^{\nu(K)}$ and $K_2 = a^{\mathbb N \setminus 2^{\mathbb N}}$ lie in $\mathcal I$, they are disjoint, and they are regularly separable iff $K_1$ is finite (Lemmas 4.5 and 4.6), because every infinite regular subset of $a^*$ contains an arithmetic progression, which meets every interval between consecutive powers of $2$ once they are long enough.

## Sources

- R. S. Thinniyam and G. Zetzsche, "Regular Separability and Intersection Emptiness Are Independent Problems", in *39th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2019)*, Leibniz International Proceedings in Informatics 150, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2019, article 51, doi:[10.4230/LIPIcs.FSTTCS.2019.51](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.51); read as arXiv:1908.04038v1, whose numbering is used here: Section 2 (Problems 2.3 and 2.4, the map $\nu$), Definition 3.1, Section 4 (reset VASS, Theorem 4.1, Lemmas 4.2 to 4.6), Definition 5.1 and Theorem 5.2.
