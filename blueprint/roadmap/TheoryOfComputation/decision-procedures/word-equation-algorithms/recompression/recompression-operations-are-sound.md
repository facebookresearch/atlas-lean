# Recompression operations are sound


Three kinds of rewriting of a word equation never make an unsatisfiable equation satisfiable: wrapping a variable in words, replacing chosen occurrences of a word by a fresh letter, and replacing a variable by a word.

Let $U = V$ be a word equation over letters $\Gamma$ and variables $\mathcal{X}$, with solutions taking values in $\Gamma^*$. Each of the following operations transforms $U = V$ into an equation $U' = V'$, over letters $\Gamma'$, such that, if $U' = V'$ has a solution with values in $\Gamma'^*$, then $U = V$ has a solution with values in $\Gamma^*$:

1. replacing every occurrence of a variable $X$ by $wXv$, for words $w, v \in \Gamma^*$ (here $\Gamma' = \Gamma$);
2. for a word $w \in \Gamma^+$ and a letter $c \notin \Gamma$, replacing a chosen set of pairwise disjoint occurrences of $w$ in $U$ and $V$ by $c$ (here $\Gamma' = \Gamma \cup \{c\}$), so that substituting $w$ for $c$ gives back $U$ and $V$;
3. replacing every occurrence of a variable $X$ by a word $w \in \Gamma^*$ (here $\Gamma' = \Gamma$).

Consequently every nondeterministic procedure composed of these operations is sound: whatever its guesses, it never turns an unsatisfiable equation into a satisfiable one.


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

In the first case, from a solution $\sigma'$ of $U' = V'$ define $\sigma(X) = w\, \sigma'(X)\, v$ and $\sigma(Y) = \sigma'(Y)$ for $Y \neq X$. In the second, let $h$ be the morphism that maps $c$ to $w$ and fixes every other letter and variable; then $h(U') = U$ and $h(V') = V$, and $\sigma(Y) = h(\sigma'(Y))$ takes values in $\Gamma^*$ with $\sigma(U) = h(\sigma'(U')) = h(\sigma'(V')) = \sigma(V)$. In the third, set $\sigma(X) = w$ and keep the other values. The overlap condition matters: for $w = aa$ in $aaa$, only one of the two occurrences can be replaced. In the [recompression algorithm](recompression.md), popping, removing a variable with empty value, cutting prefixes and suffixes, and compressing explicit pairs and blocks are instances of these operations.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Lemma 3 and its proof (Section 2, "Soundness and completeness")
