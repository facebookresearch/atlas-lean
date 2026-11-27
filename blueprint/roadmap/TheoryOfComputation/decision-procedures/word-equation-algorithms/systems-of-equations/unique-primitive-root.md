# Unique primitive root of a word


Every nonempty word is a power of a unique primitive word, its primitive root.

Let $\Sigma$ be an alphabet.

1. Every nonempty word $W \in \Sigma^+$ is $R^k$ for some primitive word $R$ and some $k \ge 1$.
2. If $R^i = S^j$ with $R, S$ primitive and $i, j \ge 1$, then $R = S$ and $i = j$. So the primitive word $R$ in item 1 is unique; it is the primitive root of $W$.


## Depends on

- [Primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md)

## Proof depends on

None.

## Expansion

Item 1: take a shortest word $R$ with $W \in R^+$; if $R = T^j$ with $j \ge 2$, then $T$ is shorter and $W \in T^+$, so $R$ is primitive.

This page becomes ready once item 2 has a proof prerequisite of its own. One route is the periodicity lemma of Fine and Wilf: if $i = 1$ or $j = 1$, primitivity gives the claim directly; otherwise the word $R^i = S^j$ has periods $|R|$ and $|S|$ and length at least $|R| + |S|$, so it has period $d = \gcd(|R|, |S|)$, and primitivity of $R$ and $S$ forces $d = |R| = |S|$ and $R = S$. Saarela's polynomial proof (European Journal of Combinatorics 47 (2015), Theorem 2.3, with Lemma 2.2) is the other cited route.

A consequence used for constant-free equations: if $W_1, \dots, W_m \in \Sigma^*$ commute pairwise and some $W_s$ is nonempty, then all lie in $R^*$ for the primitive root $R$ of $W_s$. Indeed each nonempty $W_t$ commutes with $W_s$, so both are [powers of a common word](../../word-equations-with-length/commuting-words-are-powers-of-a-common-word.md) $w$, which is nonempty; writing $w = T^l$ with $T$ primitive gives $W_s = T^{lq}$ for some $q \ge 1$, hence $T = R$ by item 2 and $W_t \in R^*$.

## Sources

- Aleksi Saarela, "Systems of word equations, polynomials and linear algebra: A new approach", European Journal of Combinatorics 47 (2015), 1–14, https://doi.org/10.1016/j.ejc.2015.01.005; read as arXiv:1401.7498v1, https://arxiv.org/abs/1401.7498v1, Theorem 2.3 (unique primitive root) with Lemma 2.2 (Section 2, "Basic Theorems")
- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Theorem 1, item 2 (Section 2)
