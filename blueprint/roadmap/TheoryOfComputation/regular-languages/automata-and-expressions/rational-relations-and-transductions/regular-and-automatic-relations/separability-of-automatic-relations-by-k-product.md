# Separability of automatic relations by k products of regular languages is undecidable

For every $k \ge 2$, no algorithm decides whether two binary automatic relations can be separated by a union of $k$ products of regular
languages, nor whether an automatic graph has a proper coloring with $k$ colors that are regular languages.

**Automatic and recognizable relations.** Let $\mathbb{A}$ be a finite alphabet and $\bot \notin \mathbb{A}$. For words $w_1, w_2 \in \mathbb{A}^*$, the *convolution* $w_1 \otimes w_2$ is the word over $(\mathbb{A} \cup \{\bot\})^2$ obtained by padding the
shorter word with $\bot$ and reading both letter by letter. A relation $R \subseteq \mathbb{A}^* \times \mathbb{A}^*$ is *automatic* if $\{u \otimes v : (u, v) \in R\}$ is a regular language, and *recognizable* if
$R = \bigcup_{i=1}^n A_i \times B_i$ for regular languages $A_i, B_i \subseteq \mathbb{A}^*$; for fixed $k$, $k\text{-PROD}$ is the class of recognizable relations that are unions of at most $k$ such products. A relation $S$
*separates* $R$ from $R'$ if $R \subseteq S$ and $R' \cap S = \emptyset$.

**Automatic graphs.** An *automatic graph* has as vertices a regular set of words and as edges a binary automatic relation. A *$k$-regular coloring* is a proper coloring of its vertices with $k$ colors in
which every color class is a regular language.

**Theorem.** For every $k \ge 2$:

1. it is undecidable, given an automatic graph, whether it has a $k$-regular coloring; more precisely, the problem is recursively enumerable-complete, also for connected automatic graphs;
2. it is undecidable, given binary automatic relations $R$ and $R'$, whether some relation in $k\text{-PROD}$ separates $R$ from $R'$.

For $k = 1$ the separability question is decidable: a relation in $1\text{-PROD}$ separates $R$ from $R'$ exactly when the product of the two projections of $R$ does. Whether two automatic relations can be separated by some recognizable relation, with no bound on the number of products, is open; the source shows
it is polynomial-time equivalent to deciding whether an automatic graph has a finite coloring by regular languages. In contrast, the source shows that definability, whether a single automatic relation
equals a relation of a bounded class, is decidable for its hierarchy of bounded recognizable relations.

## Depends on

- [Automatic structure](../../../../undecidable-problems/automata-over-data-and-structures/isomorphism-of-automatic-structures/automatic-structure.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Item 1 reduces the *reachable regularity problem*: whether the set of configurations reachable from the initial configuration of a well-founded reversible Turing machine is regular, which is
undecidable by reduction from the halting problem for deterministic reversible Turing machines (Lecerf), which has no page. The configuration graph of such a machine is an automatic graph that is a disjoint union of paths, and the set of nodes without predecessor is regular, which
lets regular colorings detect the reachable set. Item 2 reduces item 1: for a symmetric relation $E$, two regular sets $A, B$ form a coloring of the automatic graph with edges $E$ exactly when
$(A \times B) \cup (B \times A)$ separates $E$ from the identity relation, which gives the case $k = 2$ by taking the symmetric closure of the edge relation.

## Sources

- P. Barceló, D. Figueira and R. Morvan, "Separating automatic relations", in *48th International Symposium on Mathematical Foundations of Computer Science (MFCS 2023)*, LIPIcs 272, paper 17, 2023, doi:10.4230/LIPIcs.MFCS.2023.17; read in arXiv:2305.08727v2: Theorem 4.4 ($k$-regular colorability) in Section 4.2 with Proposition 4.1 and Lemma 4.2 of Section 4.1, Theorem 5.6 ($k$-PROD separability) and Proposition 5.2 ($k = 1$) in Section 5, Theorem 3.1 (the equivalence) in Section 3, and Corollaries 6.2 and 6.4 (definability) in Section 6, with the numbering of that version.
