# Intersecting a regular relation with the suffix or subword relation is undecidable

No algorithm decides whether a given regular relation contains a pair of words in which the first is a suffix of the second,
and none decides it for the subword (factor) relation.

For words $u, w$ write $u \preceq_{\mathrm{suff}} w$ if $w = w' u$ for some word $w'$, and $u \preceq w$ ($u$ is a *subword*,
or factor, of $w$) if $w = w' u w''$ for some words $w', w''$. Let the alphabet $\Sigma$ have at least two letters.

**Theorem.** Each of the following problems is undecidable: given a binary [regular relation](regular-relations.md)
$R \subseteq \Sigma^* \times \Sigma^*$, presented by a nondeterministic finite automaton over $\Sigma_\bot \times \Sigma_\bot$,

1. is $R \cap {\preceq_{\mathrm{suff}}} \neq \emptyset$, that is, is there $(w, w') \in R$ with $w \preceq_{\mathrm{suff}} w'$?
2. is $R \cap {\preceq} \neq \emptyset$, that is, is there $(w, w') \in R$ with $w \preceq w'$?

As a consequence, query evaluation is undecidable for extended conjunctive regular path queries over graph databases once the
suffix or the subword relation is added to them. By contrast, the same problem for the subsequence (scattered subword)
relation is decidable, with non-multiply-recursive complexity, and the problem is tractable for every rational relation when $R$ is
recognizable.

More generally the problem is undecidable for every relation $S = R_0 \cdot \mathrm{Graph}(f) \cdot R_1$ with $R_0$ recognizable
with second projection $\Sigma^*$ and $f$ a non-constant strictly alphabetic morphism.

## Depends on

- [Regular relations](regular-relations.md)

## Proof depends on

- [Emptiness of a linear bounded automaton on computable input slices is undecidable](../../../../undecidable-problems/emptiness-problem-for-linear-bounded-automata/exists-is-lba-not-computable-pred-forall.md)

## Expansion

The proof reduces emptiness of linear bounded automata. A configuration with tape $a_0 \cdots a_n$ (end markers included),
state $q$ and head on $a_i$ is encoded as $w_C = \# a_0 \cdots a_{i-1} q a_i \cdots a_n \#$; all configurations of a run have
encodings of the same length. Because of this, the relation of pairs
$(w_{C_0} w_{C_1} \cdots w_{C_m},\ w_{C'_1} \cdots w_{C'_m})$ in which each $C'_{i+1}$ is a successor of $C_i$, $C_0$ is initial and
$C_m$ is final, is regular: the two components stay a constant delay apart. A pair of this relation with its first component a
suffix of the second forces $C'_i = C_i$ for every $i$, so the intersection with $\preceq_{\mathrm{suff}}$ is nonempty exactly
when the automaton has an accepting computation. Inserting blocks of $\#$ symbols makes the subword relation behave like the
suffix relation, and a uniform binary coding of the letters gives the result over a two-letter alphabet.

## Sources

- P. Barceló, D. Figueira and L. Libkin, "Graph logics with rational relations", *Logical Methods in Computer Science* 9(3), paper 1, 2013, doi:10.2168/LMCS-9(3:1)2013; Section 5 of the version arXiv:1304.4150v2: Theorem 5.1 (the first theorem of the section), the corollary after it, Proposition 5.3 and their common proof, and the summary table of Section 7 (the subsequence relation).
