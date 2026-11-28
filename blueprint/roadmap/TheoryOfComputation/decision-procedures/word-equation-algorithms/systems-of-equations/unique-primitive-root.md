# Unique primitive root of a word

Every nonempty word is a power of a unique primitive word, its primitive root.

Let $\Sigma$ be an alphabet.

1. Every nonempty word $W \in \Sigma^+$ is $R^k$ for some primitive word $R$ and some $k \ge 1$.
2. If $R^i = S^j$ with $R, S$ primitive and $i, j \ge 1$, then $R = S$ and $i = j$. So the primitive word $R$ in item 1 is unique; it is the primitive root of $W$.

## Depends on

- [Primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md)

## Proof depends on

- [Periodicity lemma of Fine and Wilf](fine-and-wilf-periodicity-lemma.md)

## Expansion

Item 1: take a shortest word $R$ with $W \in R^+$; if $R = T^j$ with $j \ge 2$, then $T$ is shorter and $W \in T^+$, so $R$ is primitive.

Item 2: the words $R$ and $S$ are nonempty, since primitive words are. If $j = 1$, then $S = R^i$, and primitivity of $S$ forces $i = 1$ and $R = S$; the case $i = 1$ is symmetric. Otherwise $i, j \ge 2$. The word $w = R^i = S^j$ has period $|R|$, because $w$ is a prefix of $R w = R^{i+1}$, and likewise period $|S|$; its length satisfies $|w| = i|R| \ge 2|R|$ and $|w| = j|S| \ge 2|S|$, hence $|w| \ge |R| + |S| \ge |R| + |S| - \gcd(|R|, |S|)$. By the periodicity lemma of Fine and Wilf, $w$ has period $d = \gcd(|R|, |S|) \ge 1$, so $w_k = w_{k \bmod d}$ for every index $k$. Let $t$ be the prefix of $w$ of length $d$. As $d$ divides $|R|$ and $R$ is the prefix of $w$ of length $|R|$, this gives $R = t^{|R|/d}$, and primitivity of $R$ forces $|R| = d$; likewise $|S| = d$. Then $R$ and $S$ are both the prefix of $w$ of length $d$, so $R = S$, and $i|R| = j|S|$ gives $i = j$. Saarela proves the same theorem by a polynomial argument (European Journal of Combinatorics 47 (2015), Theorem 2.3, with Lemma 2.2).

A consequence used for constant-free equations: if $W_1, \dots, W_m \in \Sigma^*$ commute pairwise and some $W_s$ is nonempty, then all lie in $R^*$ for the primitive root $R$ of $W_s$. Indeed each nonempty $W_t$ commutes with $W_s$, so both are [powers of a common word](../../word-equations-with-length/commuting-words-are-powers-of-a-common-word.md) $w$, which is nonempty; writing $w = T^l$ with $T$ primitive gives $W_s = T^{lq}$ for some $q \ge 1$, hence $T = R$ by item 2 and $W_t \in R^*$.

## Sources

- Aleksi Saarela, "Systems of word equations, polynomials and linear algebra: A new approach", European Journal of Combinatorics 47 (2015), 1–14, https://doi.org/10.1016/j.ejc.2015.01.005; read as arXiv:1401.7498v1, https://arxiv.org/abs/1401.7498v1, Theorem 2.3 (unique primitive root) with Lemma 2.2 (Section 2, "Basic Theorems")
- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Theorem 1, item 2 (Section 2)
- N. J. Fine and H. S. Wilf, "Uniqueness theorems for periodic functions", Proceedings of the American Mathematical Society 16 (1965), 109–114, https://doi.org/10.1090/S0002-9939-1965-0174934-9, for the periodicity lemma used in the proof of item 2
