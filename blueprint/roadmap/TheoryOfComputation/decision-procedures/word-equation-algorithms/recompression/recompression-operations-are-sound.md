# Recompression operations are sound

Wrapping a variable in words, replacing every occurrence of a word whose occurrences do not overlap by a fresh letter, replacing a variable by a word, and the pair and block compressions built from them never make an unsatisfiable word equation satisfiable.

Let $U = V$ be a word equation over letters $\Gamma$ and variables $\mathcal{X}$, with solutions taking values in $\Gamma^*$. Each of the following operations transforms $U = V$ into an equation $U' = V'$, over letters $\Gamma'$, such that, if $U' = V'$ has a solution with values in $\Gamma'^*$, then $U = V$ has a solution with values in $\Gamma^*$:

1. replacing every occurrence of a variable $X$ by $wXv$, for words $w, v \in \Gamma^*$ (here $\Gamma' = \Gamma$);
2. for a word $w \in \Gamma^+$ whose occurrences in $U$ and $V$ are pairwise disjoint, for instance $w = ab$ with letters $a \neq b$, and a letter $c \notin \Gamma$, replacing all occurrences of $w$ in $U$ and $V$ by $c$ (here $\Gamma' = \Gamma \cup \{c\}$);
3. replacing every occurrence of a variable $X$ by a word $w \in \Gamma^*$ (here $\Gamma' = \Gamma$);
4. block compression of a letter $a \in \Gamma$: for each length $\ell$ of a maximal block of explicit letters $a$ in $U$ or $V$, replacing every such maximal block $a^\ell$ by a letter $a_\ell \notin \Gamma$, distinct letters for distinct $\ell$ (here $\Gamma'$ is $\Gamma$ together with these letters).

Pair compression of letters $a \neq b$, replacing every explicit occurrence of $ab$ by a fresh letter, is the case $w = ab$ of item 2. Consequently every nondeterministic procedure composed of these operations is sound: whatever its guesses, it never turns an unsatisfiable equation into a satisfiable one.


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

In the first case, from a solution $\sigma'$ of $U' = V'$ define $\sigma(X) = w\, \sigma'(X)\, v$ and $\sigma(Y) = \sigma'(Y)$ for $Y \neq X$. In the second, let $h$ be the morphism that maps $c$ to $w$ and fixes every other letter and variable; then $h(U') = U$ and $h(V') = V$, and $\sigma(Y) = h(\sigma'(Y))$ takes values in $\Gamma^*$ with $\sigma(U) = h(\sigma'(U')) = h(\sigma'(V')) = \sigma(V)$. In the third, set $\sigma(X) = w$ and keep the other values. In the fourth, the morphism $h$ that maps each $a_\ell$ to $a^\ell$ and fixes everything else again satisfies $h(U') = U$ and $h(V') = V$, and the same argument applies. Jeż states the soundness of block compression in his Lemma 4 and obtains it from Lemma 3; the argument here spells out that step.

The second operation is the source's "replacing all occurrences of a word"; the disjointness assumption makes "all occurrences" well defined, as it fails for $w = aa$ in $aaa$. The argument above uses only that substituting $w$ for $c$ gives back $U$ and $V$. So, as an elementary consequence not stated in the source, replacing an arbitrary chosen set of pairwise disjoint occurrences of $w$ by $c$ is sound as well; for $w = ab$ in $abab$, choosing only the first occurrence gives $cab$, while item 2 gives $cc$. In the [recompression algorithm](recompression.md), popping and cutting prefixes and suffixes are instances of the first operation, removing a variable with empty value of the third, and compressing explicit pairs and blocks of the second and fourth.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Lemma 3 and its proof (Section 2, "Soundness and completeness"), and the soundness part of Lemma 4 for the procedures PairCompNCr and BlockCompNCr (Algorithm 2)
