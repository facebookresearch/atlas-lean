# Piecewise testability of context-free languages is undecidable

No algorithm decides whether the language of a given context-free grammar is piecewise testable.

Precisely: given a [context-free](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
grammar $G$ over an alphabet $A$, it is undecidable whether $L(G) \subseteq A^*$ is a
[piecewise testable language](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md),
that is, a finite Boolean combination of the languages $A^* a_1 A^* a_2 \cdots a_k A^*$.

The source proves more generally, following a remark of Thomas Place, that piecewise testability is undecidable for every
full trio that contains $\{a^n b^n : n \ge 0\}$, among them the languages of labeled Petri nets. For the classes that the
source treats in its section on decidable classes, separability by piecewise testable languages (given $K$ and $L$, is there a piecewise testable language
containing $K$ and disjoint from $L$?) is decidable.

## Depends on

- [Context-free languages](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [Piecewise testable languages](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Write $L_{ab} = \{a^n b^n : n \ge 0\}$ and $\mathcal{T}(L_{ab})$ for the full trio it generates, which is contained in the
context-free languages. First, universality is undecidable for $\mathcal{T}(L_{ab})$: from an instance
$\alpha, \beta : A^* \to \{0, 1\}^*$ of the Post correspondence problem one builds rational transductions $R_\alpha, R_\beta$
with $R_\gamma L_{ab} = \{u v : u \in A^+,\ v \in \{0,1\}^*,\ v \ne \gamma(u)\}$, using the input $a^n b^n$ to compare
position $n$ of $v$ with position $n$ of $\gamma(u)$; then $R_\alpha L_{ab} \cup R_\beta L_{ab} \cup (B^* \setminus A^+\{0,1\}^*)$
is universal exactly when the instance has no solution. Second, fix $K \in \mathcal{T}(L_{ab})$ that is not piecewise testable
and a new letter $\#$; for $L \subseteq A^*$ in the trio, $K \# A^* \cup A^* \# L$ is piecewise testable if and only if $L$ is
universal, because piecewise testable languages are closed under residuals and a word $w \notin L$ would give
$K = (K \# A^* \cup A^* \# L)(\# w)^{-1}$.

## Sources

- W. Czerwiński, W. Martens, L. van Rooijen, M. Zeitoun and G. Zetzsche, "A characterization for decidable separability by piecewise testable languages", *Discrete Mathematics and Theoretical Computer Science* 19(4), FCT '15 special issue, article 1, 2017, doi:10.23638/DMTCS-19-4-1; Corollary 6.3 of the version arXiv:1410.1042v4, with Lemma 6.1 and Proposition 6.2 and their proofs.
