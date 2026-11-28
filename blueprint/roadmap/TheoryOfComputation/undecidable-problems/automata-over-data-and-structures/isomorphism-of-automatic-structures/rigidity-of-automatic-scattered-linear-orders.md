# Rigidity of automatic scattered linear orders is Π⁰₁-hard

Whether an automatic linear order has no nontrivial automorphism is $\Pi^0_1$-hard, even for scattered linear orders, while for regular languages ordered lexicographically it is decidable.

**Theorem.** A linear order is *scattered* if the rational line $(\mathbb Q; \le)$ does not embed into it, and *rigid* if the identity is its only automorphism; an [automatic](automatic-structure.md) linear order is *automatically rigid* if it has no nontrivial automorphism that is FA recognizable. Then:

1. the set of word automatic presentations of rigid linear orders, and the set of word automatic presentations of rigid scattered linear orders, are $\Pi^0_1$-hard;
2. the set of word automatic presentations of automatically rigid linear orders, and the set of word automatic presentations of automatically rigid scattered linear orders, are $\Pi^0_1$-complete.

Both hardness results hold already when the order is fixed: for the order $\le^2_{\mathrm{lex}}$ on convolutions $\{0,1\}^+ \otimes \{0,1\}^+$, the set of regular languages $L$ with $(L; \le^2_{\mathrm{lex}})$ rigid (rigid and scattered, automatically rigid, automatically rigid and scattered) is $\Pi^0_1$-hard (Theorem 2 of the source). For a regular language $L$ under the lexicographic order $\le_{\mathrm{lex}}$, rigidity of $(L; \le_{\mathrm{lex}})$ is decidable (Theorem 1), but for context-free languages $L \subseteq \{0,1\}^+$ it is $\Pi^0_1$-hard (Theorem 3). For tree automatic presentations, rigidity is $\Pi^0_2$-hard, and there is a scattered linear order whose set of tree automatic presentations is $\Pi^0_1$-hard (Theorem 6 and Corollary 2).

## Depends on

- [Automatic structure](automatic-structure.md)
- [Arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces the $\Pi^0_1$-complete set of pairs of polynomials $p, q \in \mathbb N[x_1, \dots, x_k]$ with $p(\bar y) \neq q(\bar y)$ for all $\bar y \in \mathbb N^k$. From $p$ and $q$ one builds the scattered linear order $L_{p,q}$, the $(\mathbb N^k; \le_{\mathrm{lex}})$-indexed sum of the blocks $B(m, n) = (m + \delta) \cdot \omega^* + (n + \delta) \cdot \omega$ with $m = p(\bar x)$ and $n = q(\bar x)$, where $\delta$ is a fixed scattered linear order. Every automorphism maps each block onto itself, and $B(m, n)$ is rigid iff $m \neq n$, so $L_{p,q}$ is rigid iff $p(\bar x) \neq q(\bar x)$ for all $\bar x$. A regular language $L$ with $(L; \le^2_{\mathrm{lex}}) \cong L_{p,q}$ is computable from $p$ and $q$, and for it rigidity and automatic rigidity coincide (Lemma 2). The upper bound in part 2 holds because whether a given FA-recognizable relation is a nontrivial automorphism is decidable, so the existence of one is $\Sigma^0_1$.

## Sources

- D. Kuske, "Isomorphisms of scattered automatic linear orders", *Theoretical Computer Science* 533:46–63, 2014, doi:[10.1016/j.tcs.2014.03.022](https://doi.org/10.1016/j.tcs.2014.03.022); read as arXiv:1204.5653v1, whose numbering is used here: Section 2 (scattered, rigid and automatically rigid linear orders), Theorem 1, Lemmas 1 and 2, Theorem 2 and Corollary 1 with their proofs, Theorem 3, Corollary 2 and Theorem 6.
