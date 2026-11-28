# Density of lexicographic orders of context-free languages is undecidable

No algorithm decides whether the language of a context-free grammar over $\{0,1\}$ is a dense linear order under the lexicographic order, or whether two such languages have the same order type, even when one of them is regular.

**Lexicographic orders.** Order $\{0,1\}$ by $0 < 1$ and $\{0,1\}^*$ lexicographically: $u <_\ell v$ if $u$ is a proper prefix of $v$, or $u = x0y$ and $v = x1z$ for some words $x, y, z$. Every language $L \subseteq \{0,1\}^*$ is then a linear order $(L, <_\ell)$. A linear order is *dense* if it has at least two elements and between any two elements there is a third; $\eta$ denotes the order type of the rationals, the countable [dense linear order without endpoints](../../../Order/ordered-sets/is-dense-linear-order-without-endpoints.md); density in this sense allows a least or a greatest element. A [context-free grammar](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md) is a *prefix grammar* if the language generated from each of its nonterminals is prefix-free.

**Theorem (Ésik).** There is no algorithm that decides, for a context-free grammar $G$ over $\{0,1\}$, whether $(L(G), <_\ell)$ is dense, and none that decides whether its order type is $\eta$ (Theorem 3.3 of the source). Undecidability holds already on the prefix grammars the reduction builds, so also for the promise problem restricted to prefix grammars; whether a context-free grammar is a prefix grammar is itself undecidable (Remark 2.1 of the source, credited to Boasson).

The source derives that there is no algorithm that decides, for a context-free grammar $G$ and a right-linear grammar $G'$ over $\{0,1\}$, whether $(L(G), <_\ell)$ and $(L(G'), <_\ell)$ are isomorphic (Theorem 3.4), again already for prefix grammars. In particular it is undecidable whether the lexicographic orders of the languages of two context-free grammars have the same order type. For lexicographic orders of regular languages, isomorphism is decidable, a result of Thomas that the source recalls.

## Depends on

- [Context-free languages](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [Dense linear order without endpoints](../../../Order/ordered-sets/is-dense-linear-order-without-endpoints.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

From an instance $(\alpha, \beta)$ of the Post correspondence problem the proof builds a context-free prefix grammar $G_{\alpha,\beta}$ over $\{0,1\}$ whose language, under the lexicographic order, is dense if and only if $(\alpha, \beta)$ has no solution (Proposition 3.1 of the source); it is then a dense order of type $\eta$. Comparing with a right-linear prefix grammar for a regular language of order type $\eta$ gives Theorem 3.4.

## Sources

- Z. Ésik, "An undecidable property of context-free linear orders", *Information Processing Letters* 111(3), 2011, pp. 107–109, doi:10.1016/j.ipl.2010.10.018; read as arXiv:1004.1736v1 ("An undecidable property of context-free languages"), <https://arxiv.org/abs/1004.1736v1>: Theorems 3.3 and 3.4, Proposition 3.1 and Remark 3.2, and the definitions of Section 2, in the numbering of that version.
