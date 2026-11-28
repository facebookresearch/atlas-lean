# Acyclic transducer constraints are PSPACE-complete

A conjunction of regular-membership atoms and transducer atoms whose transducer atoms form a forest on the variables has a PSPACE-complete satisfiability problem, with automata and transducers in the input, and a satisfiable one has a solution whose words have at most exponential length.

Let $\Sigma$ be a finite alphabet. Consider conjunctions $\varphi$ of atoms $P(x)$, with $P \subseteq \Sigma^*$ given by a nondeterministic finite automaton, and atoms $R(x, y)$, with $R \subseteq \Sigma^* \times \Sigma^*$ a [rational relation](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md) given by a transducer, interpreted as in [string constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md). Call $\varphi$ *acyclic* if $x \neq y$ in every atom $R(x, y)$ and the undirected multigraph whose vertices are the variables of $\varphi$, with one edge $\{x, y\}$ for each atom $R(x, y)$, has no cycle; in particular no two transducer atoms share both variables. The input is the list of atoms with explicitly written automata and transducers. Then:

1. Satisfiability of acyclic conjunctions is in [PSPACE](../../complexity-classes/time-and-space-complexity-classes/pspace.md).
2. It is PSPACE-hard, already when every transducer realizes the identity relation $\{(w, w) : w \in \Sigma^*\}$.
3. There is a polynomial $p$ such that every satisfiable acyclic conjunction $\varphi$ has a solution in which every word has length at most $2^{p(|\varphi|)}$.

## Depends on

- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)
- [String constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md)
- [The complexity class PSPACE](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Nonemptiness of alternating automata is PSPACE-complete](../../omega-automata-and-games/alternating-automata/nonemptiness-of-alternating-automata-is-pspace-complete.md)

## Expansion

This node still needs its proof broken down into the synchronization construction, the witness bound and the lower-bound reduction.

Attribution of the three clauses. Lin and Barceló state clauses 1–3 together for their class AC (their Proposition 2), whose edge condition is phrased on a simple graph; with two transducer atoms on the same pair of variables that wording would cover $R(x, y) \wedge R'(x, y)$, whose satisfiability is the nonemptiness of $R \cap R'$ and is [undecidable](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/undecidable-problems-for-rational-relations.md). The multigraph condition above is the one under which the cited proofs apply. Barceló, Figueira and Libkin prove clauses 1–2 for one fixed binary rational relation applied along an acyclic pattern of pairs (their Theorem 6.7). Holík, Janků, Lin, Rümmer and Vojnar prove clause 1 uniformly, with the transducers in the input and $k$-ary rational constraints: in a positive formula, every conjunction joins subformulas sharing at most one variable, and a forest conjunction can be bracketed that way.

Route for clause 1 (Holík et al., Theorem 5.3 and Corollary 5.4): translate each atom into an alternating finite transducer, align the tracks of two conjuncts on their single shared variable, saturate with $\varepsilon$ self-loops on distinct $\varepsilon$ symbols, and intersect; the result is one alternating transducer, built in polynomial time, which is nonempty iff $\varphi$ is satisfiable; its nonemptiness, as an alternating automaton over tuples of letters, is decided in polynomial space.

Route for clause 3 (Barceló et al., Lemma 6.8, restated by Lin and Barceló as their Proposition 14): construct, in exponential time, one multi-tape automaton accepting exactly the solution tuples, by synchronizing the transducers along the forest; each of its states has size polynomial in $|\varphi|$, so it has exponentially many states, and a shortest accepted tuple, read along a simple accepting path, has exponential length.

Clause 2: nonemptiness of the intersection of $m$ regular languages given by automata is PSPACE-complete (Kozen, 1977), and equals the satisfiability of $P_1(x_1) \wedge \dots \wedge P_m(x_m) \wedge \bigwedge_{i < m} \mathrm{Id}(x_i, x_{i+1})$, whose transducer edges form a path.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Section 3.2, the class AC and Proposition 2; Section 5.1.3, Proposition 14 (the multi-track generalization).
- P. Barceló, D. Figueira and L. Libkin, "Graph logics with rational relations", Logical Methods in Computer Science 9(3:1), 2013, doi:[10.2168/LMCS-9(3:1)2013](https://doi.org/10.2168/LMCS-9(3:1)2013); arXiv:1304.4150v2, <https://arxiv.org/abs/1304.4150v2>: Section 3 (the generalized intersection problem) and Section 6.2, Theorem 6.7 and Lemma 6.8 with the proof of Theorem 6.7.
- L. Holík, P. Janků, A. W. Lin, P. Rümmer and T. Vojnar, "String constraints with concatenation and transducers solved efficiently", Proceedings of the ACM on Programming Languages 2 (POPL), Article 4, 2018, doi:[10.1145/3158092](https://doi.org/10.1145/3158092); technical report arXiv:2010.15975v1, <https://arxiv.org/abs/2010.15975v1>: Definition 3.1 (acyclic formulae), Lemma 4.3, Section 5.1 (conjunction and disjunction of alternating transducers, Example 5.2), Theorem 5.3 and Corollary 5.4.
- D. Kozen, "Lower bounds for natural proof systems", 18th Annual Symposium on Foundations of Computer Science (FOCS 1977), pp. 254–266, doi:[10.1109/SFCS.1977.16](https://doi.org/10.1109/SFCS.1977.16): PSPACE-completeness of intersection nonemptiness for finite automata, as cited by Lin and Barceló and by Barceló, Figueira and Libkin.
