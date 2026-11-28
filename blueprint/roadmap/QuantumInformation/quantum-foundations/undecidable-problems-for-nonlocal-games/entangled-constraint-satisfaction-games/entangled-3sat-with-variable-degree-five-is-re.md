# Entangled 3SAT with every variable in five clauses is RE-hard

There is a constant $s < 1$ such that, for 3SAT instances in which every variable occurs in exactly five clauses, deciding whether the clause–variable game has quantum value 1 or at most $s$ is RE-hard.

**Theorem (Culf, Mastel, Paddock and Spirig).** Let 3SAT-5 be the set of 3SAT instances in which every variable appears in exactly 5 clauses. There is a constant $0 < s < 1$ such that it is RE-hard to decide, given a 3SAT-5 instance $B$, whether the clause–variable game of $B$ (the [constraint–variable game](constraint-system-games-and-entangled-csps.md) of $B$ with the uniform distribution on its clauses) has quantum value $1$ or at most $s$, promised that one of the two holds (Theorem 9 of arXiv:2510.03477v3).

The instances are given explicitly; the source proves the result in this direct presentation rather than for succinctly presented games, moving the exponential-time step into a padded version of the halting problem.

## Depends on

- [Constraint system games and entangled constraint satisfaction problems](constraint-system-games-and-entangled-csps.md)
- [Entangled strategies and the entangled value of a game](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

- [Entangled constraint satisfaction problems with NP-complete constraint languages are RE-complete](entangled-csps-with-np-complete-constraints-are.md)
- [Explicit arithmetic constant-degree expanders on every number of vertices](../../../../GraphTheory/graph-families-and-operations/explicit-and-random-expander-constructions/arithmetic-expanders-on-every-vertex-count.md)

## Expansion

The proof starts from the theorem of Culf and Mastel that the halting problem reduces in polynomial time to $\mathrm{SuccinctCSP}_{c\text{-}v}(3\mathrm{SAT})^*_{1,s}$ for some $s < 1$. A padded halting problem, in which inputs are padded to exponential length, turns this into a polynomial-time reduction to the explicit problem with uniform question distribution. The number of occurrences of each variable is then reduced, as in the classical reductions of Papadimitriou and Yannakakis and of Feige: each occurrence gets a copy of the variable, and equality constraints along the edges of a constant-degree expander graph tie the copies together; the expansion keeps the reduction sound against entangled players. The expander family the replacement needs is that of Definition 24 and Theorem 25 of the source: explicit graphs on every number $n$ of vertices with a fixed degree and a fixed spectral gap. The linked page on arithmetic expanders gives such a family as regular multigraphs, with loops and parallel edges; Definition 24 speaks of graphs, so an expansion checks that the replacement argument of Theorem 33 accepts multigraphs or removes the loops and parallel edges. A good expansion also links the RE-hardness of the padded halting problem (Lemma 23 of the source).

## Sources

- E. Culf, K. Mastel, C. Paddock and T. Spirig, "The quantum smooth label cover problem is undecidable", in *53rd International Colloquium on Automata, Languages, and Programming (ICALP 2026)*, Leibniz International Proceedings in Informatics 374, Schloss Dagstuhl, 2026, article 71, pp. 71:1–71:23, doi:10.4230/LIPIcs.ICALP.2026.71; read as arXiv:2510.03477v3, <https://arxiv.org/abs/2510.03477v3>: Section 2 (nonlocal games, constraint system games), Theorem 9 (Section 3) and its proof in Section 4 (Theorem 21, citing Culf and Mastel, Lemma 23 on the padded halting problem, Definition 24 and Theorem 25 on expander families, and Theorem 33 on the soundness of the expander replacement).
